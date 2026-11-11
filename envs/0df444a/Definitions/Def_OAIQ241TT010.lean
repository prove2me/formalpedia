-- Prove2me | Definitions.Def_OAIQ241TT010
-- name    : OAIQ241TT010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:01:32.069789+00:00
-- url     : https://prove2.me/theorems/234c98d9-9e53-4ae1-9f53-4f627ac917d2
-- title:
--   Definitions bundle OAIQ241TT010 of the split of OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 259 declarations of OpenAI's Lean: 165 definitions and 94 theorems. The definitions and types are `OAI.AlgorithmicThinTrees.GraphStack.incidence`, `OAI.AlgorithmicThinTrees.GraphStack.incidenceRows`, `OAI.AlgorithmicThinTrees.GraphStack.laplacian`, `OAI.AlgorithmicThinTrees.GraphStack.projection`, `OAI.AlgorithmicThinTrees.GraphStack.response`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.affinePoint`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.beA`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.beB`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.beR`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.beV`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.bsR`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.bsV`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.budgetEdge`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.budgetIncoming`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.buildPencil`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.clockProgram`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.differenceVector`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.edgeMatrix`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.edgeTotal`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.esActive`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.esCapacity`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.esCapacityRate`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.esE`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.esEdge`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.esP`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.esU`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.esX`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.esY`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.esZ`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.fsP`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.fsRE`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.gainProgram`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.graphBaseline`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.graphBound`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.graphError`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.graphRadius`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.graphSizeProgram`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.graphStep`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.initializeLoop`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.initializeSearch` and 125 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `MatrixSigning_Arithmetic_ArithmeticEncodingSize`, `MatrixSigning_Arithmetic_BinaryAddressLookup`, `MatrixSigning_Arithmetic_ComplexScalarNodes`, `MatrixSigning_Arithmetic_DivisionInput`, `MatrixSigning_Arithmetic_EncodedDivision`, `MatrixSigning_Arithmetic_FloorRationalMachine`, `MatrixSigning_Arithmetic_NegativeDivision`, `MatrixSigning_Arithmetic_RationalDivisionMachine`, `MatrixSigning_Arithmetic_RationalDivisionStages`, `MatrixSigning_Arithmetic_RationalMultiplicationMachine`, `MatrixSigning_Arithmetic_RationalMultiplyNormalize`, `MatrixSigning_Arithmetic_RationalReciprocalCore`, `MatrixSigning_Arithmetic_RationalReciprocalMachine`, `MatrixSigning_Arithmetic_RationalReciprocalSerialize`, `MatrixSigning_Arithmetic_RationalSignClassifier`, `MatrixSigning_Arithmetic_SparseScalarNodes`, `MatrixSigning_Arithmetic_ZeroPaddedRow`, `MatrixSigning_Complexity_ComplexScalarCosts`, `MatrixSigning_Complexity_SparseScalarCost`, `MatrixSigning_Complexity_TerminalWitnessCost`, `MatrixSigning_Encoding_FramedArrayReplacement`, `MatrixSigning_Encoding_InverseEncodingSize`, `MatrixSigning_Encoding_SumEncodingSize`, `MatrixSigning_Machines_ControllerReachable`, `MatrixSigning_Machines_ControllerReplayBound`, `MatrixSigning_Machines_ControllerTerminalBound`, `MatrixSigning_Machines_ExpressionPrimitives`, `MatrixSigning_Machines_FixedDotBody`, `MatrixSigning_Machines_FixedDotBounds`, `MatrixSigning_Machines_FixedDotMachine`, `MatrixSigning_Machines_FixedDotPrimitives`, `MatrixSigning_Machines_SignedFloorMachine`, `MatrixSigning_Machines_SparseCoefficientStage`, `MatrixSigning_Machines_TerminalInputBounds`, `MatrixSigning_Matrices_DenseMatrixSerialization`, `MatrixSigning_Matrices_MatrixReadProgram`, `MatrixSigning_Matrices_PivotControllerLoop`, `MatrixSigning_Matrices_RowDotBody`, `MatrixSigning_Matrices_RowDotBounds`, `MatrixSigning_Matrices_RowDotControl`, `MatrixSigning_Matrices_RowDotMachine`, `MatrixSigning_Matrices_RowDotPrimitives`, `MatrixSigning_Optimization_SchurWitnessHead`, `MatrixSigning_Optimization_SignedFloorInterface`, `MatrixSigning_Optimization_StoredWitnessLift`, `MatrixSigning_Optimization_TerminalWitnessMachine`, `MatrixSigning_Realization_ArithmeticRoutine`, `MatrixSigning_Realization_ArrayRealization`, `MatrixSigning_Realization_CoordinateRealization`, `MatrixSigning_Realization_FaceChoiceRealization`, `MatrixSigning_Realization_FloorCleanRoutine`, `MatrixSigning_Realization_MatrixStructureRealization`, `MatrixSigning_Realization_PencilArrayRealization`, `MatrixSigning_Realization_PencilCompileRealization`, `MatrixSigning_Realization_RatFieldsRealization`, `MatrixSigning_Realization_RoundedStepRealization`, `MatrixSigning_Realization_ScalarRealization`, `MatrixSigning_Realization_ScheduleRealization`, `MatrixSigning_Realization_ValueDataRealization`, `MatrixSigning_Realization_VectorRealization`, `ThinTrees_Arithmetic_ArraySums`, `ThinTrees_Arithmetic_UnaryArithmetic`, `ThinTrees_Arithmetic_UnaryRoot`, `ThinTrees_Continuation_Realization`, `ThinTrees_Encoding_GraphRealization`, `ThinTrees_Normalization_Realization`, `ThinTrees_Pencil_BlockAssembly`, `ThinTrees_Pencil_FiniteFamilies`, `ThinTrees_Pencil_MatrixConstraintRealization`, `ThinTrees_Pencil_Parameters`, `ThinTrees_Pencil_PointPrograms`, `ThinTrees_Pencil_Realization`, `ThinTrees_Pencil_ScalarConstraintRealization`, `ThinTrees_Pencil_SearchRealization`.
--
--   **Imports.** It imports the published bundle `Def_AlgorithmicThinTrees`; the bundles `OAIQ241TT007`, `OAIQ241TT008` and `OAIQ241TT009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ241TT012` and `OAIQ241TT013`.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT007
import Definitions.Def_OAIQ241TT008
import Definitions.Def_OAIQ241TT009

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_ArithmeticEncodingSize
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W01

theorem ratLength_mul_le (q r : ℚ) :
    ratLength (q * r) ≤ 4 * (ratLength q + ratLength r) + 7 := by
  obtain ⟨hqnum, hqden⟩ := rational_parts_le_two_pow_length q
  obtain ⟨hrnum, hrden⟩ := rational_parts_le_two_pow_length r
  obtain ⟨hn, hd⟩ := KS.W30.mul_parts_le_two_pow q r (ratLength q) (ratLength r)
    hqnum hqden hrnum hrden
  have h := ratLength_le_of_parts (q * r) _ _ hn hd
  omega

theorem mul_parts_size_le (q r : ℚ) :
    Nat.size (q * r).num.natAbs ≤ ratLength q + ratLength r + 1 ∧
      Nat.size (q * r).den ≤ ratLength q + ratLength r + 1 := by
  obtain ⟨hqnum, hqden⟩ := rational_parts_le_two_pow_length q
  obtain ⟨hrnum, hrden⟩ := rational_parts_le_two_pow_length r
  obtain ⟨hn, hd⟩ := KS.W30.mul_parts_le_two_pow q r (ratLength q) (ratLength r)
    hqnum hqden hrnum hrden
  constructor
  · simpa only [Nat.size_pow] using Nat.size_le_size hn
  · simpa only [Nat.size_pow] using Nat.size_le_size hd

end KS.W01

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_DenseMatrixSerialization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.sumBudget_cons _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W08.AccessCounted.readMatrix_ops _root_.OAI.KS.W08.AccessCounted.readMatrix_value _root_.OAI.KS.W08.AccessCounted.readMatrix_work _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W17.FixedPSD.withSaved_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W08

open KS.W07
open scoped BigOperators

theorem denseMatrixTape_length_le {n : ℕ} (M : DenseRatMatrix n) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2 ^ b) :
    (denseMatrixTape M).length ≤ n * n * (8 * b + 15) := by
  rw [denseMatrixTape_length]
  calc
    _ ≤ ∑ _k : Fin (n * n), (8 * b + 15) := by
      apply Finset.sum_le_sum
      intro k _
      have h := KS.W01.ratLength_le_of_parts
        (DenseRatMatrix.decode M (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
        b b (hnum _ _) (hden _ _)
      unfold KS.W01.ratLength at h
      omega
    _ = _ := by simp [Nat.mul_comm]

end KS.W08

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_BinaryAddressLookup
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W08

open KS.W01.FixedStack KS.W29.FixedSequential
open KS.W04.ReusableArrayLookup

theorem run_binaryMatrix_lookup {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ)
    (hnum : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).den ≤ 2 ^ b)
    (i j : Fin n) (bits : List Bool)
    (hlen : n * n * (40 * b + 84) + 6 ≤ bits.length) :
    binaryMatrixLookupProgram.toMachine.run
      ⟨some binaryMatrixLookupProgram.initial,
        arrayStacks (denseMatrixTape M) (denseMatrixBinaryCursor i j) [] [] []⟩ bits =
      ⟨none, arrayStacks (denseMatrixTape M) []
        (KS.W01.encodeRat (AccessCounted.readMatrix M i j).value) [] []⟩ := by
  apply run_compose_bounded matrixCursorProgram KS.W04.ReusableArrayLookup.program
    (arrayStacks (denseMatrixTape M) (denseMatrixBinaryCursor i j) [] [] [])
    (arrayStacks (denseMatrixTape M) [] [] [] (denseMatrixCursor i j))
    (arrayStacks (denseMatrixTape M) []
      (KS.W01.encodeRat (AccessCounted.readMatrix M i j).value) [] [])
    (8 * n * n + 2) (n * n * (40 * b + 76) + 4)
  · exact run_matrixCursorProgram M i j
  · intro coins hc
    have ht := denseMatrixTape_length_le M b hnum hden
    have hi := (matrixEntryIndex_lt i j).le
    have hb : 5 * (denseMatrixTape M ++ []).length + i.val * n + j.val + 4 ≤
        coins.length := by
      rw [List.append_nil]
      have he : 5 * (n * n * (8 * b + 15)) + n * n + 4 =
          n * n * (40 * b + 76) + 4 := by ring
      nlinarith
    simpa only [List.append_nil] using run_preservedMatrix_lookup M i j [] coins hb
  · have he : (8 * n * n + 2) + (n * n * (40 * b + 76) + 4) =
        n * n * (40 * b + 84) + 6 := by ring
    simpa only [he] using hlen

end KS.W08

end

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

theorem canonicalNormalizeTicks_le (q r : ℚ) :
    canonicalNormalizeTicks q r ≤
      1024 * ((KS.W01.encodeRat q ++ KS.W01.encodeRat r).length + 1) ^ 3 := by
  simpa only [canonicalNormalizeTicks, KS.W06.RationalCompare.pairBits_encodeRat] using
    normalizeTicks_le (negativeBit q.num) (constructorBits q.num) (Computability.encodeNat q.den)
      (negativeBit r.num) (constructorBits r.num) (Computability.encodeNat r.den)

end KS.W15.RationalMultiply

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalMultiplicationMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.sumBudget_cons _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W15.RationalMultiply
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem totalTicks_le_polynomial (q r : ℚ) :
    totalTicks q r ≤ KS.W29.polynomialFuel 2048 3 (inputBits q r).length := by
  have hn := canonicalNormalizeTicks_le q r
  obtain ⟨hp, hd⟩ := KS.W01.mul_parts_size_le q r
  have hl : KS.W01.ratLength q + KS.W01.ratLength r = (inputBits q r).length := by
    simp [inputBits, KS.W01.ratLength]
  rw [hl] at hp hd
  let N := (inputBits q r).length + 1
  have hN : 0 < N := by dsimp [N]; omega
  have hpow : N ≤ N ^ 3 := by
    calc
      N = N ^ 1 := by simp
      _ ≤ N ^ 3 := Nat.pow_le_pow_right hN (by decide)
  change canonicalNormalizeTicks q r +
      16 * ((Computability.encodeNat (q * r).num.natAbs).length +
        (Computability.encodeNat (q * r).den).length + 1) ≤ 2048 * N ^ 3
  simp only [KS.W19.encodeNat_length_eq_size]
  change canonicalNormalizeTicks q r ≤ 1024 * N ^ 3 at hn
  change Nat.size (q * r).num.natAbs ≤ N at hp
  change Nat.size (q * r).den ≤ N at hd
  omega

end KS.W15.RationalMultiply

end

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

def mulNodeTicks (q r : ℚ) : Nat :=
  pairTicks (KS.W01.encodeRat q) (KS.W01.encodeRat r) + RationalMultiply.totalTicks q r +
    (2 * (KS.W01.encodeRat (q * r)).length + 2)
def addNodeTicks (q r : ℚ) : Nat :=
  pairTicks (KS.W01.encodeRat q) (KS.W01.encodeRat r) + KS.W13.RationalAdd.totalTicks q r +
    (2 * (KS.W01.encodeRat (q + r)).length + 2)

end KS.W15.ComplexMachine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_DivisionInput
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.DivisionInput
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun

def program : Program 10 := compose parseFirst secondStage
def machine : Machine := program.toMachine

theorem first_run (xs d coins : List Bool) (hc : coins.length = 3 * xs.length + 2) :
    parseFirst.toMachine.run (parseFirst.toMachine.init (KS.W01.frame xs ++ KS.W01.frame d)) coins =
      ⟨none, «stacks» (KS.W01.frame d) xs [] []⟩ := by
  erw [first_init]
  refine (KS.W19.MachineTransport.run_ofMachine (lift3 KS.W29.FrameDecoder.machine firstPorts) _ coins).trans ?_
  refine (run_pack KS.W29.FrameDecoder.machine firstPorts _ _ coins).trans ?_
  refine (congrArg (fun c => pack firstPorts c (fun _ => []))
    (KS.W29.FrameDecoder.run_frame xs (KS.W01.frame d) coins hc)).trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem first_halts (xs d coins : List Bool) (hc : coins.length = 3 * xs.length + 2) :
    HaltsAfter parseFirst (parseFirst.toMachine.init (KS.W01.frame xs ++ KS.W01.frame d)) coins := by
  erw [first_init]
  apply (haltsAfter_lift3_iff _ firstPorts _ coins).2
  erw [project_pack]
  exact FrameActivity.haltsAfter_frame xs (KS.W01.frame d) coins hc

theorem second_run (xs d coins : List Bool) (hc : coins.length = 3 * d.length + 2) :
    parseSecond.toMachine.run ⟨some parseSecond.initial, «stacks» (KS.W01.frame d) xs [] []⟩ coins =
      ⟨none, «stacks» [] xs d []⟩ := by
  erw [second_start]
  refine (KS.W19.MachineTransport.run_ofMachine (lift3 KS.W29.FrameDecoder.machine secondPorts) _ coins).trans ?_
  refine (run_pack KS.W29.FrameDecoder.machine secondPorts _ _ coins).trans ?_
  refine (congrArg (fun c => pack secondPorts c («stacks» [] xs [] []))
    (KS.W29.FrameDecoder.run_frame d [] coins hc)).trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem second_halts (xs d coins : List Bool) (hc : coins.length = 3 * d.length + 2) :
    HaltsAfter parseSecond ⟨some parseSecond.initial, «stacks» (KS.W01.frame d) xs [] []⟩ coins := by
  erw [second_start]
  apply (haltsAfter_lift3_iff _ secondPorts _ coins).2
  erw [project_pack]
  exact FrameActivity.haltsAfter_frame d [] coins hc

theorem run_input (xs d first second rev work : List Bool)
    (hf : first.length = 3 * xs.length + 2) (hs : second.length = 3 * d.length + 2)
    (hr : rev.length = xs.length + 1)
    (hw : xs.length * (8 * (xs.length + 2 * d.length + 2) + 1) + 1 ≤ work.length) :
    machine.run (machine.init (KS.W01.frame xs ++ KS.W01.frame d))
      (first ++ (second ++ (rev ++ work))) =
      ⟨none, DivisionMachine.«stacks» d [] (DivisionLoop.process d xs.reverse [] []).1
        (DivisionLoop.process d xs.reverse [] []).2 [] [] [] []⟩ := by
  have hi : machine.init (KS.W01.frame xs ++ KS.W01.frame d) =
      liftLeft parseFirst secondStage (parseFirst.toMachine.init (KS.W01.frame xs ++ KS.W01.frame d)) := by
    apply config_ext
    · rfl
    · intro j
      rfl
  erw [hi]
  change (compose parseFirst secondStage).toMachine.run _ _ = _
  erw [run_compose parseFirst secondStage _ first _ (first_halts xs d first hf), first_run xs d first hf]
  change liftRight parseFirst secondStage ((compose parseSecond loopStage).toMachine.run
    (liftLeft parseSecond loopStage ⟨some parseSecond.initial, _⟩) _) = _
  erw [run_compose parseSecond loopStage _ second _ (second_halts xs d second hs), second_run xs d second hs]
  change liftRight parseFirst secondStage (liftRight parseSecond loopStage
    ((compose reverseInput DivisionMachine.loop).toMachine.run
      (liftLeft reverseInput DivisionMachine.loop ⟨some reverseInput.initial, _⟩) _)) = _
  erw [run_compose reverseInput DivisionMachine.loop _ rev _ (reverse_halts xs d rev hr),
    reverse_run xs d rev hr, DivisionMachine.loop_payload d xs work hw]
  rfl

theorem run_input_tape (xs d bits : List Bool) (hb : bits.length = inputFuel xs d) :
    machine.run (machine.init (KS.W01.frame xs ++ KS.W01.frame d)) bits =
      ⟨none, DivisionMachine.«stacks» d [] (DivisionLoop.process d xs.reverse [] []).1
        (DivisionLoop.process d xs.reverse [] []).2 [] [] [] []⟩ := by
  unfold inputFuel at hb
  obtain ⟨first, rest, rfl, hf, ht⟩ := DivisionMachine.split_exact bits (3 * xs.length + 2) _ hb
  obtain ⟨second, rest, rfl, hs, ht⟩ := DivisionMachine.split_exact rest (3 * d.length + 2) _ ht
  obtain ⟨rev, work, rfl, hr, hw⟩ := DivisionMachine.split_exact rest (xs.length + 1) _ ht
  exact run_input xs d first second rev work hf hs hr hw.ge

end KS.W19.DivisionInput

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_EncodedDivision
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.EncodedDivision
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem input_spec (xs d : List Bool) :
    RunSpec DivisionInput.program
      (DivisionInput.machine.init (KS.W01.frame xs ++ KS.W01.frame d)).«stacks»
      (DivisionMachine.«stacks» d [] (resultPair xs d).1 (resultPair xs d).2 [] [] [] [])
      (DivisionInput.inputFuel xs d) := by
  intro bits hb
  exact DivisionInput.run_input_tape xs d bits hb

end KS.W19.EncodedDivision

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SignedFloorMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.SignedFloorMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def divide : Program 11 := KS.W29.FixedSequential.liftPorts DivisionInput.program naturalPorts
def tailProgram : Program 11 := compose divide finish
def program : Program 11 := compose strip tailProgram

theorem divide_spec (sign : Bool) (xs d : List Bool) :
    RunSpec divide («stacks» (KS.W01.frame xs ++ KS.W01.frame d) [] [] [] [sign])
      («stacks» [] d (EncodedDivision.resultPair xs d).1 (EncodedDivision.resultPair xs d).2 [sign])
      (DivisionInput.inputFuel xs d) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec DivisionInput.program naturalPorts _ _ _ _ _
    (EncodedDivision.input_spec xs d)
  · intro i
    fin_cases i <;> rfl
  · intro i
    fin_cases i <;> rfl
  · intro j hj
    have hge : 10 ≤ j.val := by
      by_contra hn
      have hlt : j.val < 10 := by omega
      exact hj ⟨j.val, hlt⟩ (Fin.ext rfl)
    have he : j = 10 := Fin.ext (by have hh := j.isLt; omega)
    subst j
    rfl

theorem program_spec (sign : Bool) (xs d : List Bool) :
    RunSpec program («stacks» (sign :: (KS.W01.frame xs ++ KS.W01.frame d)) [] [] [] [])
      («stacks» [] d (sign :: KS.W01.encodeNat (bitsValue (EncodedDivision.resultPair xs d).1))
        (EncodedDivision.resultPair xs d).2 [])
      (1 + (DivisionInput.inputFuel xs d + (6 * (EncodedDivision.resultPair xs d).1.length + 6))) :=
  (strip_spec sign (KS.W01.frame xs ++ KS.W01.frame d)).compose
    ((divide_spec sign xs d).compose
      (finish_spec sign d (EncodedDivision.resultPair xs d).1 (EncodedDivision.resultPair xs d).2))

end KS.W19.SignedFloorMachine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_SignedFloorInterface
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.SignedFloorMachine
open KS.W03.MachineCombinators

theorem rational_runSpec (q : Rat) :
    RunSpec program («stacks» (KS.W01.encodeRat q) [] [] [] [])
      («stacks» [] (Computability.encodeNat q.den) (KS.W01.encodeInt ⌊q⌋)
        (rationalRemainder q) [])
      (KS.W29.polynomialFuel 32 2 (KS.W01.encodeRat q).length) := by
  have h := (program_spec (negativeOfInt q.num)
    (Computability.encodeNat (KS.W01.intPayload q.num))
    (Computability.encodeNat q.den)).mono
      (fuel_quadratic (negativeOfInt q.num)
        (Computability.encodeNat (KS.W01.intPayload q.num))
        (Computability.encodeNat q.den))
  have hin : negativeOfInt q.num ::
      (KS.W01.frame (Computability.encodeNat (KS.W01.intPayload q.num)) ++
        KS.W01.frame (Computability.encodeNat q.den)) = KS.W01.encodeRat q :=
    (SignedFloor.encodeRat_constructor q).symm
  have hout : negativeOfInt q.num :: KS.W01.encodeNat
      (bitsValue (EncodedDivision.resultPair
        (Computability.encodeNat (KS.W01.intPayload q.num))
        (Computability.encodeNat q.den)).1) = KS.W01.encodeInt ⌊q⌋ :=
    SignedFloor.floor_wire q
  rw [hin, hout] at h
  exact h

end KS.W19.SignedFloorMachine

end

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

def program : Program 11 := compose SignedFloorMachine.program (compose clearScratch appendDenominator)

theorem full_spec (q : ℚ) :
    RunSpec program (state (KS.W01.encodeRat q) []) (state [] (KS.W01.encodeRat (⌊q⌋ : ℚ)))
      (ticks q) := by
  have h := (SignedFloorMachine.rational_runSpec q).compose
    ((clearScratch_spec (Computability.encodeNat q.den) (KS.W01.encodeInt ⌊q⌋)
      (SignedFloorMachine.rationalRemainder q)).compose
      (appendDenominator_spec (KS.W01.encodeInt ⌊q⌋)))
  simp only [encodeRat_intCast] at h ⊢
  exact h

theorem polynomial_spec (q : ℚ) :
    RunSpec program (state (KS.W01.encodeRat q) []) (state [] (KS.W01.encodeRat (⌊q⌋ : ℚ)))
      (KS.W29.polynomialFuel 64 2 (KS.W01.encodeRat q).length) :=
  (full_spec q).mono (ticks_le_polynomial q)

end KS.W20.FloorRationalMachine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalReciprocalCore
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.RationalReciprocal
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19
open KS.W03.MachineCombinators KS.W30.BinaryRational

theorem core_spec (q : ℚ) :
    RunSpec core (canonicalState q) (canonicalState q⁻¹)
      (310 * (KS.W01.ratLength q + 1) ^ 3) := by
  let x := encodeMagnitude q
  let y : RatBits := ⟨x.negative, x.denominator, x.numerator⟩
  have hsize := KS.W01.rational_parts_size_le_length q
  have hn : x.numerator.length ≤ KS.W01.ratLength q := by
    simpa only [x, encodeMagnitude, encodeNat_length_eq_size] using hsize.1
  have hd : x.denominator.length ≤ KS.W01.ratLength q := by
    simpa only [x, encodeMagnitude, encodeNat_length_eq_size] using hsize.2
  have hyc : CanonicalBits y.numerator := canonicalBits_encodeNat _
  have hyd : CanonicalBits y.denominator := canonicalBits_encodeNat _
  have hs := swap_spec x.numerator x.denominator x.negative
  have hnrm := RationalMagnitudeMachine.normalizes_ratBits y (KS.W01.ratLength q) hyc hyd hd hn
  have hout : normalize y = encodeMagnitude q⁻¹ := inverseRat_canonical q
  rw [hout] at hnrm
  have h := hs.compose hnrm
  have hlin := Nat.le_self_pow (by decide : 3 ≠ 0) (KS.W01.ratLength q + 1)
  have ht : (4 * x.numerator.length + 2 * x.denominator.length + 6) +
      300 * (KS.W01.ratLength q + 1) ^ 3 ≤ 310 * (KS.W01.ratLength q + 1) ^ 3 := by omega
  exact h.mono ht

end KS.W30.RationalReciprocal

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_InverseEncodingSize
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.sumBudget_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W01

theorem inverse_parts_le_two_pow_length (q : ℚ) :
    (q⁻¹).num.natAbs ≤ 2 ^ ratLength q ∧ (q⁻¹).den ≤ 2 ^ ratLength q := by
  obtain ⟨hnum, hden⟩ := rational_parts_le_two_pow_length q
  constructor
  · apply le_trans (b := q.den) _ hden
    rw [Rat.num_inv, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_sign]
    split_ifs <;> simp
  · rw [Rat.den_inv]
    split_ifs
    · exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
    · exact hnum

theorem ratLength_inv_le (q : ℚ) : ratLength (q⁻¹) ≤ 4 * ratLength q + 7 := by
  obtain ⟨hn, hd⟩ := inverse_parts_le_two_pow_length q
  have h := ratLength_le_of_parts (q⁻¹) _ _ hn hd
  omega

theorem ratLength_div_le (q r : ℚ) :
    ratLength (q / r) ≤ 4 * (ratLength q + ratLength r) + 7 := by
  obtain ⟨hqn, hqd⟩ := rational_parts_le_two_pow_length q
  obtain ⟨hrn, hrd⟩ := inverse_parts_le_two_pow_length r
  obtain ⟨hn, hd⟩ := KS.W30.mul_parts_le_two_pow q (r⁻¹)
    (ratLength q) (ratLength r) hqn hqd hrn hrd
  rw [div_eq_mul_inv]
  have h := ratLength_le_of_parts (q * r⁻¹) _ _ hn hd
  omega

end KS.W01

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalReciprocalSerialize
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.RationalReciprocal
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19
open KS.W03.MachineCombinators

theorem serializeCore_spec (q : ℚ) :
    RunSpec serializeCore (canonicalState q)
      (KS.W01.SignedRationalSerializer.outputState (KS.W01.encodeRat q⁻¹))
      (600 * (KS.W01.ratLength q + 1) ^ 3) := by
  have hs := KS.W01.SignedRationalSerializer.serializes_rational q⁻¹
  have h := (core_spec q).compose hs
  have hp := KS.W01.rational_parts_size_le_length q⁻¹
  have hi := KS.W01.ratLength_inv_le q
  have hnum : (Computability.encodeNat (q⁻¹).num.natAbs).length ≤ 4 * KS.W01.ratLength q + 7 := by
    rw [encodeNat_length_eq_size]
    exact hp.1.trans hi
  have hden : (Computability.encodeNat (q⁻¹).den).length ≤ 4 * KS.W01.ratLength q + 7 := by
    rw [encodeNat_length_eq_size]
    exact hp.2.trans hi
  have hserial : 16 * ((Computability.encodeNat (q⁻¹).num.natAbs).length +
      (Computability.encodeNat (q⁻¹).den).length + 1) ≤ 240 * (KS.W01.ratLength q + 1) := by omega
  have hlin := Nat.le_self_pow (by decide : 3 ≠ 0) (KS.W01.ratLength q + 1)
  have ht : 310 * (KS.W01.ratLength q + 1) ^ 3 +
      16 * ((Computability.encodeNat (q⁻¹).num.natAbs).length +
        (Computability.encodeNat (q⁻¹).den).length + 1) ≤
      600 * (KS.W01.ratLength q + 1) ^ 3 := by omega
  exact h.mono ht

end KS.W30.RationalReciprocal

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalReciprocalMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W30.RationalReciprocal
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem program_spec (q : ℚ) :
    RunSpec program (inputState (KS.W01.encodeRat q))
      (outputState (KS.W01.encodeRat q⁻¹))
      (1000 * (KS.W01.ratLength q + 1) ^ 3) := by
  have hp : RunSpec KS.W06.SingleRationalParser.program
      (inputState (KS.W01.encodeRat q)) (canonicalState q)
      (8 * (KS.W01.ratLength q + 1)) := by
    have h := KS.W06.SingleRationalParser.canonical_spec q []
    simp only [List.append_nil] at h
    exact h
  have h := hp.compose (serializeCore_spec q)
  have hlin := Nat.le_self_pow (by decide : 3 ≠ 0) (KS.W01.ratLength q + 1)
  exact h.mono (by omega)

end KS.W30.RationalReciprocal

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalDivisionStages
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W30.RationalDivision
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem parseNumerator_spec (q r : ℚ) :
    RunSpec parseNumerator (inputState (inputBits q r))
      («stacks» (KS.W06.SingleRationalParser.canonicalState q (KS.W01.encodeRat r)) [] [])
      (8 * (KS.W01.ratLength q + 1)) :=
  liftCore_spec _ _ _ [] [] _ (KS.W06.SingleRationalParser.canonical_spec q (KS.W01.encodeRat r))

theorem reciprocal_spec (q r : ℚ) :
    RunSpec reciprocal
      («stacks» (RationalReciprocal.inputState (KS.W01.encodeRat r)) [] (KS.W01.encodeRat q))
      («stacks» (RationalReciprocal.outputState (KS.W01.encodeRat r⁻¹)) [] (KS.W01.encodeRat q))
      (1000 * (KS.W01.ratLength r + 1) ^ 3) :=
  liftCore_spec _ _ _ [] _ _ (RationalReciprocal.program_spec r)

theorem multiply_spec (q r : ℚ) :
    RunSpec multiply (inputState (inputBits q r⁻¹))
      (outputState (KS.W01.encodeRat (q / r))) (KS.W15.RationalMultiply.totalTicks q r⁻¹) := by
  simp only [div_eq_mul_inv]
  exact liftCore_spec _ _ _ [] [] _ (KS.W15.RationalMultiply.full_spec q r⁻¹)

end KS.W30.RationalDivision

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalDivisionMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.sumBudget_cons _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.RationalDivision
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def totalTicks (q r : ℚ) : ℕ :=
  8 * (KS.W01.ratLength q + 1) + ((2 * KS.W01.ratLength r + 2) +
    (serializerTicks q + ((2 * KS.W01.ratLength q + 2) + ((2 * KS.W01.ratLength r + 2) +
      (1000 * (KS.W01.ratLength r + 1) ^ 3 + ((2 * KS.W01.ratLength r⁻¹ + 2) +
        ((2 * KS.W01.ratLength q + 2) + KS.W15.RationalMultiply.totalTicks q r⁻¹)))))))

theorem full_spec (q r : ℚ) :
    RunSpec program (inputState (inputBits q r))
      (outputState (KS.W01.encodeRat (q / r))) (totalTicks q r) :=
  (parseNumerator_spec q r).compose ((storeDenominator_spec q r).compose
    ((serializeNumerator_spec q r).compose ((storeNumerator_spec q r).compose
      ((restoreDenominator_spec q r).compose ((reciprocal_spec q r).compose
        ((prepareInverse_spec q r).compose ((prependNumerator_spec q r).compose (multiply_spec q r))))))))

theorem totalTicks_le_polynomial (q r : ℚ) :
    totalTicks q r ≤ KS.W29.polynomialFuel 1100000 3 (inputBits q r).length := by
  let N := KS.W01.ratLength q + KS.W01.ratLength r + 1
  have hN : 0 < N := by dsimp [N]; omega
  have hlin := Nat.le_self_pow (by decide : 3 ≠ 0) N
  have hinv := KS.W01.ratLength_inv_le r
  have hparts := KS.W01.rational_parts_size_le_length q
  have hserial : serializerTicks q ≤ 48 * (KS.W01.ratLength q + 1) := by
    simp only [serializerTicks, KS.W19.encodeNat_length_eq_size]
    omega
  have hsmall : KS.W01.ratLength r + 1 ≤ N := by dsimp [N]; omega
  have hrecip : 1000 * (KS.W01.ratLength r + 1) ^ 3 ≤ 1000 * N ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsmall _)
  have hpair : (KS.W15.RationalMultiply.inputBits q r⁻¹).length + 1 ≤ 8 * N := by
    simp only [KS.W15.RationalMultiply.inputBits, List.length_append]
    change KS.W01.ratLength q + KS.W01.ratLength r⁻¹ + 1 ≤ 8 * N
    dsimp [N]
    omega
  have hmul : KS.W15.RationalMultiply.totalTicks q r⁻¹ ≤ 1048576 * N ^ 3 := by
    calc
      _ ≤ 2048 * ((KS.W15.RationalMultiply.inputBits q r⁻¹).length + 1) ^ 3 :=
        KS.W15.RationalMultiply.totalTicks_le_polynomial q r⁻¹
      _ ≤ 2048 * (8 * N) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpair _)
      _ = 1048576 * N ^ 3 := by ring
  have hother : 8 * (KS.W01.ratLength q + 1) + (2 * KS.W01.ratLength r + 2) +
      serializerTicks q + (2 * KS.W01.ratLength q + 2) + (2 * KS.W01.ratLength r + 2) +
      (2 * KS.W01.ratLength r⁻¹ + 2) + (2 * KS.W01.ratLength q + 2) ≤ 100 * N := by
    dsimp [N]
    omega
  change totalTicks q r ≤ 1100000 * ((inputBits q r).length + 1) ^ 3
  have hlen : (inputBits q r).length + 1 = N := by
    simp only [inputBits, List.length_append, N, KS.W01.ratLength]
  rw [hlen]
  unfold totalTicks
  omega

theorem program_spec (q r : ℚ) :
    RunSpec program (inputState (inputBits q r))
      (outputState (KS.W01.encodeRat (q / r)))
      (KS.W29.polynomialFuel 1100000 3 (inputBits q r).length) :=
  (full_spec q r).mono (totalTicks_le_polynomial q r)

end KS.W30.RationalDivision

end

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

theorem sum_parts_le_two_pow (xs : List ℚ) :
    xs.sum.num.natAbs ≤ 2 ^ sumBudget xs ∧ xs.sum.den ≤ 2 ^ sumBudget xs := by
  induction xs with
  | nil => simp [sumBudget]
  | cons q xs ih =>
    obtain ⟨hqn, hqd⟩ := rational_parts_le_two_pow_length q
    obtain ⟨hn, hd⟩ := KS.W30.add_parts_le_two_pow q xs.sum
      (ratLength q) (sumBudget xs) hqn hqd ih.1 ih.2
    constructor
    · simpa only [List.sum_cons, sumBudget_cons] using hn
    · simp only [List.sum_cons, sumBudget_cons]
      exact hd.trans (Nat.pow_le_pow_right (by decide) (by omega))

theorem ratLength_sum_le (xs : List ℚ) :
    ratLength xs.sum ≤ 4 * ((xs.map ratLength).sum + xs.length) + 7 := by
  obtain ⟨hn, hd⟩ := sum_parts_le_two_pow xs
  have h := ratLength_le_of_parts xs.sum (sumBudget xs) (sumBudget xs) hn hd
  unfold sumBudget at h
  omega

end KS.W01

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedDotPrimitives
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W03.MultiplicationMachine.input_port _root_.OAI.KS.W03.MultiplicationMachine.output_port _root_.OAI.KS.W03.MultiplicationMachine.stack_count _root_.OAI.KS.W03.MultiplicationMachine.state_count _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W12.FixedDot

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem multiplication_spec (rem acc : List Bool) (p : ℚ × ℚ) :
    RunSpec multiplyProgram (registers rem (pairPayload p) [] acc [])
      (registers rem [] (KS.W01.encodeRat (p.1 * p.2)) acc [])
      (KS.W15.RationalMultiply.totalTicks p.1 p.2) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ _ _ _ _ _ _ (KS.W15.RationalMultiply.full_spec p.1 p.2)
  · intro i
    fin_cases i <;> rfl
  · intro i
    fin_cases i <;> rfl
  · intro j hj
    have h0 : j ≠ 0 := hj 0
    have h10 : j ≠ 10 := hj 10
    simp [registers, h0, h10]

theorem decode_spec (payload rem acc : List Bool) :
    RunSpec decodeProgram (registers (KS.W01.frame payload ++ rem) [] [] acc [])
      (registers rem payload [] acc []) (3 * payload.length + 2) := by
  intro bits hbits
  refine (KS.W19.MachineTransport.run_ofMachine
    (lift3 KS.W29.FrameDecoder.machine framePorts)
    (⟨some (0 : Fin 3), registers (KS.W01.frame payload ++ rem) [] [] acc []⟩ : Config 19 3)
    bits).trans ?_
  apply lift3_run_eq
  · have hp : project framePorts
        (⟨some 0, registers (KS.W01.frame payload ++ rem) [] [] acc []⟩ : Config 19 3) =
        KS.W29.FrameDecoder.machine.init (KS.W01.frame payload ++ rem) := by
      change KS.W29.Config.mk (some (0 : Fin 3)) _ =
        KS.W29.Config.mk (some (0 : Fin 3)) _
      congr 1
      funext i
      fin_cases i <;> rfl
    refine (congrArg (fun c : KS.W29.Config 3 => KS.W29.FrameDecoder.machine.run c bits)
      hp).trans ((KS.W29.FrameDecoder.run_frame_of_length_ge payload rem bits hbits.ge).trans ?_)
    change KS.W29.Config.mk none _ = KS.W29.Config.mk none _
    congr 1
    funext i
    fin_cases i <;> rfl
  · intro j hj
    have h16 : j ≠ 16 := hj 0
    have h0 : j ≠ 0 := hj 1
    have h18 : j ≠ 18 := hj 2
    simp [registers, h16, h0, h18]

end KS.W12.FixedDot

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedDotBody
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalSignClassifier.program_output _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.FixedDot

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem addition_spec (rem : List Bool) (a b : ℚ) :
    RunSpec additionProgram (registers rem (KS.W01.encodeRat a ++ KS.W01.encodeRat b) [] [] [])
      (registers rem [] (KS.W01.encodeRat (a + b)) [] [])
      (KS.W13.RationalAdd.totalTicks a b) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ _ _ _ _ _ _ (KS.W13.RationalAdd.full_spec a b)
  · intro i
    fin_cases i <;> rfl
  · intro i
    fin_cases i <;> rfl
  · intro j hj
    have h0 : j ≠ 0 := hj 0
    have h10 : j ≠ 10 := hj 10
    simp [registers, h0, h10]

theorem transfer_product_spec (rem product acc : List Bool) :
    RunSpec (transferProgram 10 0) (registers rem [] product acc [])
      (registers rem product [] acc []) (2 * product.length + 2) := by
  have h := transfer_spec 10 0 (by decide) (by decide) (by decide)
    (registers rem [] product acc []) rfl
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  funext j
  fin_cases j <;> simp [transferAfter, registers]

theorem transfer_accumulator_spec (rem product acc : List Bool) :
    RunSpec (transferProgram 17 0) (registers rem product [] acc [])
      (registers rem (acc ++ product) [] [] []) (2 * acc.length + 2) := by
  have h := transfer_spec 17 0 (by decide) (by decide) (by decide)
    (registers rem product [] acc []) rfl
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  funext j
  fin_cases j <;> simp [transferAfter, registers]

theorem store_accumulator_spec (rem value : List Bool) :
    RunSpec (transferProgram 10 17) (registers rem [] value [] [])
      (registers rem [] [] value []) (2 * value.length + 2) := by
  have h := transfer_spec 10 17 (by decide) (by decide) (by decide)
    (registers rem [] value [] []) rfl
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  funext j
  fin_cases j <;> simp [transferAfter, registers]

def bodyTicks (p : ℚ × ℚ) (a : ℚ) : ℕ :=
  (((((3 * (pairPayload p).length + 2) + KS.W15.RationalMultiply.totalTicks p.1 p.2) +
    (2 * (KS.W01.encodeRat (p.1 * p.2)).length + 2)) +
    (2 * (KS.W01.encodeRat a).length + 2)) +
    KS.W13.RationalAdd.totalTicks a (p.1 * p.2)) +
    (2 * (KS.W01.encodeRat (a + p.1 * p.2)).length + 2)

theorem body_spec (p : ℚ × ℚ) (ps : List (ℚ × ℚ)) (a : ℚ) :
    RunSpec body (boundary (inputWire (p :: ps)) a)
      (boundary (inputWire ps) (a + p.1 * p.2)) (bodyTicks p a) := by
  exact (((((decode_spec (pairPayload p) (inputWire ps) (KS.W01.encodeRat a)).compose
    (multiplication_spec (inputWire ps) (KS.W01.encodeRat a) p)).compose
    (transfer_product_spec (inputWire ps) (KS.W01.encodeRat (p.1 * p.2)) (KS.W01.encodeRat a))).compose
    (transfer_accumulator_spec (inputWire ps) (KS.W01.encodeRat (p.1 * p.2)) (KS.W01.encodeRat a))).compose
    (addition_spec (inputWire ps) a (p.1 * p.2))).compose
    (store_accumulator_spec (inputWire ps) (KS.W01.encodeRat (a + p.1 * p.2)))

theorem run_dot_loop (ps : List (ℚ × ℚ)) (a : ℚ) (bits : List Bool)
    (hlen : loopTicks bodyTicks ps a ≤ bits.length) :
    (loopProgram body).toMachine.run (loopConfig body (inputWire ps) a) bits =
      ⟨none, boundary [] (a + dotValue ps)⟩ :=
  run_loop_of_body_spec body bodyTicks body_spec ps a bits hlen

theorem dot_loop_spec (ps : List (ℚ × ℚ)) (a : ℚ) :
    RunSpec (loopProgram body) (boundary (inputWire ps) a)
      (boundary [] (a + dotValue ps)) (loopTicks bodyTicks ps a) := by
  intro bits hbits
  exact run_dot_loop ps a bits hbits.ge

end KS.W12.FixedDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedDotMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationMachine.input_port _root_.OAI.KS.W03.MultiplicationMachine.output_port _root_.OAI.KS.W03.MultiplicationMachine.stack_count _root_.OAI.KS.W03.MultiplicationMachine.state_count _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalSignClassifier.program_output _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.FixedDot
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem push_spec (b : Bool) (before : Fin 19 → List Bool) :
    RunSpec (pushProgram b) before (pushAfter b before) 1 := by
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons coin rest =>
      have hr : rest = [] := by simpa using hbits
      subst rest
      refine (KS.W19.MachineTransport.run_ofMachine
        (compile (0 : Fin 1) (16 : Fin 19) 17 (pushDispatch b))
        (⟨some (0 : Fin 1), before⟩ : Config 19 1) [coin]).trans ?_
      simp only [Machine.run]
      refine (step_compile (0 : Fin 1) (16 : Fin 19) 17 (pushDispatch b)
        (0 : Fin 1) before coin).trans ?_
      change (Config.mk (none : Option (Fin 1)) _ : Config 19 1) = Config.mk none _
      apply congrArg (fun work : Fin 19 → List Bool =>
        (Config.mk (none : Option (Fin 1)) work : Config 19 1))
      funext j
      by_cases hj : j = 17
      · subst j
        simp [pushDispatch, pushAfter, Instruction.action, KS.W29.StackAction.apply]
      · simp [pushDispatch, pushAfter, Instruction.action, KS.W29.StackAction.apply, hj]

theorem initialize_spec (source : List Bool) :
    RunSpec «initialize_» (initialStacks source) (boundary source 0) 5 := by
  let s0 := initialStacks source
  let s1 := pushAfter true s0
  let s2 := pushAfter true s1
  let s3 := pushAfter false s2
  let s4 := pushAfter true s3
  have h := ((((push_spec true s0).compose (push_spec true s1)).compose
    (push_spec false s2)).compose (push_spec true s3)).compose (push_spec false s4)
  have hz : KS.W01.encodeRat 0 = [false, true, false, true, true] := by decide
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  funext j
  fin_cases j <;> simp [s0, s1, s2, s3, s4, pushAfter, initialStacks, boundary, registers, hz]

def machine : Machine := program.toMachine

def totalTicks (ps : List (ℚ × ℚ)) : ℕ := 5 + loopTicks bodyTicks ps 0

theorem full_spec (ps : List (ℚ × ℚ)) :
    RunSpec program (initialStacks (inputWire ps)) (boundary [] (dotValue ps)) (totalTicks ps) := by
  have h := (initialize_spec (inputWire ps)).compose (dot_loop_spec ps 0)
  simp only [zero_add] at h
  exact h

@[simp] theorem machine_stackCount : machine.stackCount = 19 := rfl
@[simp] theorem machine_inputStack : machine.inputStack = (16 : Fin 19) := rfl
@[simp] theorem machine_outputStack : machine.outputStack = (17 : Fin 19) := rfl

end KS.W12.FixedDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedDotBounds
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.FixedDot
open KS.W01 KS.W01.FixedStack KS.W29.FixedSequential

theorem product_sumBudget_le_wire (ps : List (ℚ × ℚ)) :
    ((ps.map (fun p => p.1 * p.2)).map ratLength).sum + ps.length ≤
      8 * (inputWire ps).length := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      have hm := ratLength_mul_le p.1 p.2
      have hp : ratLength p.1 + ratLength p.2 = (pairPayload p).length := by
        simp [ratLength, pairPayload]
      rw [hp] at hm
      simp only [List.map_cons, List.sum_cons, List.length_cons, inputWire_cons,
        List.length_append, pairWire_length]
      omega

theorem dotValue_length_le_wire (ps : List (ℚ × ℚ)) :
    ratLength (dotValue ps) ≤ 32 * (inputWire ps).length + 7 := by
  have hs := ratLength_sum_le (ps.map (fun p => p.1 * p.2))
  have hb := product_sumBudget_le_wire ps
  simp only [List.length_map] at hs
  exact hs.trans (by omega)

theorem bodyTicks_le_uniform (p : ℚ × ℚ) (a : ℚ) (L : ℕ)
    (hp : (pairPayload p).length ≤ L) (ha : ratLength a ≤ 32 * L + 7) :
    bodyTicks p a ≤ 100000000 * (L + 1) ^ 3 := by
  have hprod := ratLength_mul_le p.1 p.2
  have hpl : ratLength p.1 + ratLength p.2 = (pairPayload p).length := by
    simp [ratLength, pairPayload]
  rw [hpl] at hprod
  have hprod' : ratLength (p.1 * p.2) ≤ 4 * L + 7 := by omega
  have hsum := ratLength_add_le a (p.1 * p.2)
  have hsum' : ratLength (a + p.1 * p.2) ≤ 144 * L + 65 := by omega
  have hmul : KS.W15.RationalMultiply.totalTicks p.1 p.2 ≤ 2048 * (L + 1) ^ 3 := by
    apply (KS.W15.RationalMultiply.totalTicks_le_polynomial p.1 p.2).trans
    apply Nat.mul_le_mul_left 2048
    apply Nat.pow_le_pow_left
    simpa [KS.W15.RationalMultiply.inputBits, pairPayload] using Nat.add_le_add_right hp 1
  have hinput : (encodeRat a ++ encodeRat (p.1 * p.2)).length + 1 ≤ 36 * (L + 1) := by
    simp only [List.length_append]
    change ratLength a + ratLength (p.1 * p.2) + 1 ≤ 36 * (L + 1)
    omega
  have hadd0 := (KS.W13.RationalAdd.totalTicks_le_polynomial a (p.1 * p.2)).trans
    (Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left hinput 3))
  have hadd : KS.W13.RationalAdd.totalTicks a (p.1 * p.2) ≤ 46656000 * (L + 1) ^ 3 := by
    convert hadd0 using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hcube : L + 1 ≤ (L + 1) ^ 3 := by
    calc
      L + 1 = (L + 1) ^ 1 := by simp
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  simp only [ratLength] at ha hprod' hsum'
  unfold bodyTicks
  omega

theorem loopTicks_le_prefix_budget (all : List (ℚ × ℚ)) (C : ℕ)
    (hbody : ∀ pre p post, pre ++ p :: post = all → bodyTicks p (dotValue pre) ≤ C)
    (pre rest : List (ℚ × ℚ)) (hsplit : pre ++ rest = all) :
    loopTicks bodyTicks rest (dotValue pre) ≤ rest.length * (C + 1) + 1 := by
  induction rest generalizing pre with
  | nil => simp [loopTicks]
  | cons p rest ih =>
      have hb := hbody pre p rest hsplit
      have hs : (pre ++ [p]) ++ rest = all := by simpa only [List.append_assoc, List.singleton_append] using hsplit
      have ht := ih (pre ++ [p]) hs
      have hv : dotValue (pre ++ [p]) = dotValue pre + p.1 * p.2 := by
        simp [dotValue_append]
      rw [hv] at ht
      simp only [loopTicks, List.length_cons]
      nlinarith

theorem totalTicks_le_polynomial (ps : List (ℚ × ℚ)) :
    totalTicks ps ≤ KS.W29.polynomialFuel 200000000 4 (inputWire ps).length := by
  let L := (inputWire ps).length
  let C := 100000000 * (L + 1) ^ 3
  have hb : ∀ pre p post, pre ++ p :: post = ps → bodyTicks p (dotValue pre) ≤ C := by
    intro pre p post hsplit
    apply bodyTicks_le_uniform p (dotValue pre) L
    · apply pairPayload_le_wire p ps
      rw [← hsplit]
      simp
    · have hpre : (inputWire pre).length ≤ L := by
        dsimp [L]
        rw [← hsplit, inputWire_append, List.length_append]
        omega
      exact (dotValue_length_le_wire pre).trans (by omega)
  have hl := loopTicks_le_prefix_budget ps C hb [] ps rfl
  have hn : ps.length ≤ L := count_le_wire ps
  simp only [dotValue_nil] at hl
  have ht : totalTicks ps ≤ L * (C + 1) + 6 := by
    have hm := Nat.mul_le_mul_right (C + 1) hn
    unfold totalTicks
    omega
  have hN : 1 ≤ L + 1 := by omega
  have hp : 1 ≤ (L + 1) ^ 4 := by
    simpa only [one_pow] using Nat.pow_le_pow_left hN 4
  have hL : L ≤ (L + 1) ^ 4 := by
    calc
      L ≤ L + 1 := by omega
      _ = (L + 1) ^ 1 := by simp
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  have hc : L * C ≤ 100000000 * (L + 1) ^ 4 := by
    have hm := Nat.mul_le_mul_right ((L + 1) ^ 3) (show L ≤ L + 1 by omega)
    calc
      L * C = 100000000 * (L * (L + 1) ^ 3) := by dsimp [C] <;> ring
      _ ≤ 100000000 * ((L + 1) * (L + 1) ^ 3) := Nat.mul_le_mul_left _ hm
      _ = 100000000 * (L + 1) ^ 4 := by ring
  change totalTicks ps ≤ 200000000 * (L + 1) ^ 4
  simp only [Nat.mul_add, Nat.mul_one] at ht
  omega

end KS.W12.FixedDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_MatrixReadProgram
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationMachine.input_port _root_.OAI.KS.W03.MultiplicationMachine.output_port _root_.OAI.KS.W03.MultiplicationMachine.stack_count _root_.OAI.KS.W03.MultiplicationMachine.state_count _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W06.RationalSignClassifier.program_output _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W12.FixedDot.machine_inputStack _root_.OAI.KS.W12.FixedDot.machine_outputStack _root_.OAI.KS.W12.FixedDot.machine_stackCount _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W15.RationalMultiply.machine_inputStack _root_.OAI.KS.W15.RationalMultiply.machine_outputStack _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W17.FixedPSD.withSaved_initial _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W08.MatrixRead

open KS.W01.FixedStack KS.W29.FixedSequential
open KS.W03.MultiplicationBody KS.W03.MachineCombinators

theorem run_access {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ)
    (hnum : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).den ≤ 2 ^ b)
    (i j : Fin n) (bits : List Bool)
    (hlen : n * n * (40 * b + 84) + 6 ≤ bits.length) :
    accessProgram.toMachine.run
      ⟨some accessProgram.initial, workspace (denseMatrixTape M) [] [] [] (denseMatrixBinaryCursor i j)⟩ bits =
      ⟨none, workspace (denseMatrixTape M)
        (KS.W01.encodeRat (KS.W07.DenseRatMatrix.decode M i j)) [] [] []⟩ := by
  have hs : RunSpec binaryMatrixLookupProgram
      (KS.W04.ReusableArrayLookup.arrayStacks (denseMatrixTape M) (denseMatrixBinaryCursor i j) [] [] [])
      (KS.W04.ReusableArrayLookup.arrayStacks (denseMatrixTape M) []
        (KS.W01.encodeRat (KS.W07.DenseRatMatrix.decode M i j)) [] [])
      (n*n*(40*b+84)+6) := by
    intro coins hcoins
    simpa only [AccessCounted.readMatrix_value] using
      run_binaryMatrix_lookup M b hnum hden i j coins hcoins.ge
  have hl : RunSpec accessProgram
      (workspace (denseMatrixTape M) [] [] [] (denseMatrixBinaryCursor i j))
      (workspace (denseMatrixTape M) (KS.W01.encodeRat (KS.W07.DenseRatMatrix.decode M i j)) [] [] [])
      (n*n*(40*b+84)+6) := by
    apply KS.W01.FixedPortRunSpec.lift_runSpec _ accessPorts _ _ _ _ _ hs
    · intro r; fin_cases r <;> rfl
    · intro r; fin_cases r <;> rfl
    · intro r hr
      have h0 : r≠0 := hr (2 : Fin 5)
      have h3 : r≠3 := hr (1 : Fin 5)
      fin_cases r <;> simp_all [workspace]
  exact hl.run_of_le bits hlen

theorem run_matrix_read {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ)
    (hnum : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).den ≤ 2 ^ b)
    (i j : Fin n) (bits : List Bool)
    (hlen : 1024 * (n + 1) ^ 2 * (b + 1) ≤ bits.length) :
    program.toMachine.run
      ⟨some program.initial, workspace (denseMatrixTape M) (Computability.encodeNat j.val)
        (Computability.encodeNat i.val) (Computability.encodeNat n) []⟩ bits =
      ⟨none, workspace (denseMatrixTape M)
        (KS.W01.encodeRat (KS.W07.DenseRatMatrix.decode M i j)) [] [] []⟩ := by
  apply KS.W04.ReusableArrayLookup.run_compose_bounded addressProgram accessProgram
    (workspace (denseMatrixTape M) (Computability.encodeNat j.val)
      (Computability.encodeNat i.val) (Computability.encodeNat n) [])
    (workspace (denseMatrixTape M) [] [] [] (denseMatrixBinaryCursor i j))
    (workspace (denseMatrixTape M) (KS.W01.encodeRat (KS.W07.DenseRatMatrix.decode M i j)) [] [] [])
    (512 * (n + 1) ^ 2) (n * n * (40 * b + 84) + 6)
  · exact run_address (denseMatrixTape M) i j
  · exact run_access M b hnum hden i j
  · have hb : 512 * (n + 1) ^ 2 + (n * n * (40 * b + 84) + 6) ≤
        1024 * (n + 1) ^ 2 * (b + 1) := by ring_nf; omega
    exact hb.trans hlen

end KS.W08.MatrixRead

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RowDotPrimitives
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W17.FixedPSD.withSaved_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.RowDot
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem read_spec {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ)
    (hnum : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).den ≤ 2 ^ b)
    (i j : Fin n) (s : Fin 29 → List Bool)
    (hsource : s 19 = KS.W08.denseMatrixTape M)
    (hclear : ∀ r : Fin 7, s ⟨r.val, by omega⟩ = []) :
    RunSpec readProgram
      (readBefore s (Computability.encodeNat j.val) (Computability.encodeNat i.val)
        (Computability.encodeNat n))
      (put s 0 (KS.W01.encodeRat (KS.W07.DenseRatMatrix.decode M i j)))
      (1024 * (n + 1) ^ 2 * (b + 1)) := by
  have hsmall : RunSpec KS.W08.MatrixRead.program
      (KS.W08.MatrixRead.workspace (KS.W08.denseMatrixTape M)
        (Computability.encodeNat j.val) (Computability.encodeNat i.val)
        (Computability.encodeNat n) [])
      (KS.W08.MatrixRead.workspace (KS.W08.denseMatrixTape M)
        (KS.W01.encodeRat (KS.W07.DenseRatMatrix.decode M i j)) [] [] [])
      (1024 * (n + 1) ^ 2 * (b + 1)) := by
    intro bits hbits
    exact KS.W08.MatrixRead.run_matrix_read M b hnum hden i j bits hbits.ge
  have hclearPhysical : ∀ r : Fin 29, r.val < 7 → s r = [] := by
    intro r hr
    exact hclear ⟨r.val, hr⟩
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ _ _ _ _ _ _ hsmall
  · intro r
    fin_cases r <;>
      simp [readBefore, put, readPorts, KS.W08.MatrixRead.workspace, hsource]
    all_goals exact hclearPhysical _ (by decide)
  · intro r
    fin_cases r <;> simp [put, readPorts, KS.W08.MatrixRead.workspace, hsource]
    all_goals exact hclearPhysical _ (by decide)
  · intro r hr
    have h0 : r ≠ 0 := hr 0
    have h1 : r ≠ 1 := hr 1
    have h2 : r ≠ 2 := hr 2
    simp [put, readBefore, h0, h1, h2]

end KS.W12.RowDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RowDotBody
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W06.RationalSignClassifier.program_output _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W17.FixedPSD.withSaved_initial _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.RowDot
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem collect_spec {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ)
    (hnum : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).den ≤ 2 ^ b)
    (x : Fin n → ℚ) (i : Fin n) (p : Fin n × ℚ) (xs : List (Fin n × ℚ)) (out : List Bool) :
    RunSpec collectProgram (boundary M x i (p :: xs) p.1.val out)
      (put (put (boundary M x i xs p.1.val out) 27 (KS.W01.encodeRat p.2))
        0 (KS.W01.encodeRat (KS.W07.DenseRatMatrix.decode M i p.1)))
      (collectTicks n b p.1.val i.val p.2) := by
  let s0 := boundary M x i (p :: xs) p.1.val out
  let s1 := put (boundary M x i xs p.1.val out) 27 (KS.W01.encodeRat p.2)
  let s2 := put s1 0 (Computability.encodeNat p.1.val)
  let s3 := put s2 1 (Computability.encodeNat i.val)
  let s4 := put s3 2 (Computability.encodeNat n)
  have h1 : RunSpec decodeProgram s0 s1 (3 * (KS.W01.encodeRat p.2).length + 2) := by
    convert decode_spec s0 (KS.W01.encodeRat p.2) (tailTape xs) rfl rfl rfl using 1
    all_goals try with_reducible_and_instances rfl
    funext j
    fin_cases j <;> simp [s0, s1, boundary, state, put]
  have h2 : RunSpec copyColumn s1 s2 (2 * (Computability.encodeNat p.1.val).length + 2) :=
    copy_spec 24 0 (by decide) (by decide) (by decide) s1 rfl rfl
  have h3 : RunSpec copyRow s2 s3 (2 * (Computability.encodeNat i.val).length + 2) :=
    copy_spec 21 1 (by decide) (by decide) (by decide) s2 rfl rfl
  have h4 : RunSpec copyDimension s3 s4 (2 * (Computability.encodeNat n).length + 2) :=
    copy_spec 22 2 (by decide) (by decide) (by decide) s3 rfl rfl
  have h5 : RunSpec readProgram s4
      (put s1 0 (KS.W01.encodeRat (KS.W07.DenseRatMatrix.decode M i p.1)))
      (1024 * (n + 1) ^ 2 * (b + 1)) := by
    exact read_spec M b hnum hden i p.1 s1 rfl (by intro r; fin_cases r <;> rfl)
  exact (((h1.compose h2).compose h3).compose h4).compose h5

theorem body_spec {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ)
    (hnum : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).den ≤ 2 ^ b)
    (x : Fin n → ℚ) (i : Fin n) (p : Fin n × ℚ) (xs : List (Fin n × ℚ)) (out : List Bool) :
    RunSpec body (boundary M x i (p :: xs) p.1.val out)
      (boundary M x i xs (p.1.val + 1)
        ((FixedDot.pairWire (KS.W07.DenseRatMatrix.decode M i p.1, p.2)).reverse ++ out))
      (bodyTicks M b i p) := by
  let s := put (put (boundary M x i xs p.1.val out) 27 (KS.W01.encodeRat p.2))
    0 (KS.W01.encodeRat (KS.W07.DenseRatMatrix.decode M i p.1))
  let t := put (put (put s 0 []) 27 []) 25
    ((FixedDot.pairWire (KS.W07.DenseRatMatrix.decode M i p.1, p.2)).reverse ++ s 25)
  have h1 := collect_spec M b hnum hden x i p xs out
  have h2 := pair_spec s (KS.W07.DenseRatMatrix.decode M i p.1) p.2 rfl rfl rfl rfl rfl
  have h3 := increment_spec t p.1.val rfl rfl rfl
  have h := (h1.compose h2).compose h3
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  funext j
  fin_cases j <;> simp [t, s, put, boundary, state]

end KS.W12.RowDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RowDotControl
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationMachine.input_port _root_.OAI.KS.W03.MultiplicationMachine.output_port _root_.OAI.KS.W03.MultiplicationMachine.stack_count _root_.OAI.KS.W03.MultiplicationMachine.state_count _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W06.RationalSignClassifier.program_output _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W12.FixedDot.inputWire_append _root_.OAI.KS.W12.FixedDot.machine_inputStack _root_.OAI.KS.W12.FixedDot.machine_outputStack _root_.OAI.KS.W12.FixedDot.machine_stackCount _root_.OAI.KS.W15.RationalMultiply.machine_inputStack _root_.OAI.KS.W15.RationalMultiply.machine_outputStack _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W17.FixedPSD.withSaved_initial _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W12.RowDot
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem run_loop {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ)
    (hnum : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).den ≤ 2 ^ b)
    (x : Fin n → ℚ) (i : Fin n) (xs : List (Fin n × ℚ)) (k : ℕ)
    (hc : Consecutive k xs) (out bits : List Bool) (hlen : loopTicks M b i xs ≤ bits.length) :
    loopProgram.toMachine.run ⟨some loopProgram.initial, boundary M x i xs k out⟩ bits =
      ⟨none, boundary M x i [] (k + xs.length)
        ((FixedDot.inputWire (rowPairs M i xs)).reverse ++ out)⟩ := by
  induction xs generalizing k out bits with
  | nil =>
      cases bits with
      | nil => simp [loopTicks] at hlen
      | cons coin rest =>
          rw [Machine.run, step_empty, Machine.run_halted _ _ rfl]
          simp
  | cons p xs ih =>
      obtain ⟨hk, htail⟩ := (consecutive_cons k p xs).mp hc
      subst k
      cases bits with
      | nil => simp [loopTicks] at hlen
      | cons coin rest =>
          have ht : bodyTicks M b i p + loopTicks M b i xs ≤ rest.length := by
            simp only [loopTicks, List.length_cons] at hlen
            omega
          obtain ⟨remaining, hremaining, hreturn⟩ :=
            (body_spec M b hnum hden x i p xs out).loop_body_then guard rest (by omega)
          rw [Machine.run, step_cons]
          change loopProgram.toMachine.run
              (KS.W29.FixedLoop.liftBody body
                ⟨some body.initial, boundary M x i (p :: xs) p.1.val out⟩) rest =
            loopProgram.toMachine.run
              ⟨some loopProgram.initial, boundary M x i xs (p.1.val + 1)
                ((FixedDot.pairWire (KS.W07.DenseRatMatrix.decode M i p.1, p.2)).reverse ++ out)⟩
              remaining at hreturn
          rw [hreturn]
          have hn : loopTicks M b i xs ≤ remaining.length := by omega
          simpa [loopProgram, KS.W29.FixedLoop.loop_initial, FixedDot.inputWire_cons,
            List.reverse_append, List.append_assoc, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using
            ih (p.1.val + 1) htail
              ((FixedDot.pairWire (KS.W07.DenseRatMatrix.decode M i p.1, p.2)).reverse ++ out)
              remaining hn

theorem loop_spec {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ)
    (hnum : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).den ≤ 2 ^ b)
    (x : Fin n → ℚ) (i : Fin n) :
    RunSpec loopProgram (boundary M x i (indexedVector x) 0 [])
      (boundary M x i [] n ((FixedDot.inputWire (rowPairs M i (indexedVector x))).reverse))
      (loopTicks M b i (indexedVector x)) := by
  intro bits hbits
  simpa [indexedVector] using run_loop M b hnum hden x i (indexedVector x) 0
    (consecutive_indexedVector x) [] bits hbits.ge

end KS.W12.RowDot

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RowDotMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W06.RationalSignClassifier.program_output _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W12.FixedDot.dotValue_append _root_.OAI.KS.W12.FixedDot.inputWire_append _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W17.FixedPSD.withSaved_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.RowDot
open Matrix
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem prepare_spec {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ)
    (hnum : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).den ≤ 2 ^ b)
    (x : Fin n → ℚ) (i : Fin n) :
    RunSpec prepareProgram (initialStacks M x i)
      (boundary M x i [] n ((FixedDot.inputWire (rowPairs M i (indexedVector x))).reverse))
      (prepareTicks M b x i) := by
  have hc : RunSpec copyVector (initialStacks M x i)
      (boundary M x i (indexedVector x) 0 []) (2 * (vectorTape x).length + 2) := by
    convert copy_spec (20 : Fin 29) 23 (by decide) (by decide) (by decide)
      (initialStacks M x i) rfl rfl using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
    funext j
    fin_cases j <;> simp [initialStacks, boundary, state, put, Computability.encodeNat]
    rfl
  exact hc.compose (loop_spec M b hnum hden x i)

def finishTicks (n : ℕ) (ps : List (ℚ × ℚ)) : ℕ :=
  ((Computability.encodeNat n).length + 1) + ((FixedDot.inputWire ps).length + 1) + FixedDot.totalTicks ps

theorem finish_spec {n : ℕ} (M : KS.W07.DenseRatMatrix n) (x : Fin n → ℚ) (i : Fin n)
    (ps : List (ℚ × ℚ)) :
    RunSpec finishProgram (boundary M x i [] n (FixedDot.inputWire ps).reverse)
      (put (initialStacks M x i) 17 (KS.W01.encodeRat (FixedDot.dotValue ps)))
      (finishTicks n ps) := by
  let s0 := boundary M x i [] n (FixedDot.inputWire ps).reverse
  let s1 := KS.W15.RationalMultiply.clearAfter 24 s0
  let s2 := KS.W15.RationalMultiply.moveAfter 25 16 s1
  have h1 := KS.W15.RationalMultiply.clear_spec (24 : Fin 29) s0
  have h2 := KS.W15.RationalMultiply.move_spec (25 : Fin 29) 16 (by decide) s1
  have h3 : RunSpec dotProgram s2
      (put (initialStacks M x i) 17 (KS.W01.encodeRat (FixedDot.dotValue ps)))
      (FixedDot.totalTicks ps) := by
    apply KS.W01.FixedPortRunSpec.lift_runSpec _ _ _ _ _ _ _ (FixedDot.full_spec ps)
    · intro j
      fin_cases j <;> simp [s0, s1, s2, boundary, state, dotPorts,
        FixedDot.initialStacks, FixedDot.registers, KS.W15.RationalMultiply.clearAfter,
        KS.W15.RationalMultiply.moveAfter]
    · intro j
      fin_cases j <;> simp [put, initialStacks, state, dotPorts, FixedDot.boundary, FixedDot.registers]
    · intro j hj
      have h16 : j ≠ 16 := hj 16
      have h17 : j ≠ 17 := hj 17
      fin_cases j <;> simp_all [s0, s1, s2, put, initialStacks, boundary, state,
        KS.W15.RationalMultiply.clearAfter, KS.W15.RationalMultiply.moveAfter]
  have h := (h1.compose h2).compose h3
  simp [finishProgram, finishTicks, s0, s1, boundary, state,
    KS.W15.RationalMultiply.clearAfter] at h ⊢
  exact h

def totalTicks {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ) (x : Fin n → ℚ) (i : Fin n) : ℕ :=
  prepareTicks M b x i + finishTicks n (rowPairs M i (indexedVector x))

theorem full_spec {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ)
    (hnum : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).den ≤ 2 ^ b)
    (x : Fin n → ℚ) (i : Fin n) :
    RunSpec program (initialStacks M x i)
      (put (initialStacks M x i) 17 (KS.W01.encodeRat ((KS.W07.DenseRatMatrix.decode M *ᵥ x) i)))
      (totalTicks M b x i) := by
  have h := (prepare_spec M b hnum hden x i).compose
    (finish_spec M x i (rowPairs M i (indexedVector x)))
  simp only [rowPairs_dotValue] at h
  exact h

end KS.W12.RowDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RowDotBounds
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W17.FixedPSD.withSaved_initial
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

theorem matrix_parts_stored {n : ℕ} (M : DenseRatMatrix n) (x : Fin n → ℚ) (i : Fin n) :
    (∀ j k, (DenseRatMatrix.decode M j k).num.natAbs ≤ 2 ^ storedLength M x i) ∧
    (∀ j k, (DenseRatMatrix.decode M j k).den ≤ 2 ^ storedLength M x i) := by
  have hlen : ∀ j k, ratLength (DenseRatMatrix.decode M j k) ≤ storedLength M x i := by
    intro j k
    have h := matrix_entry_length M j k
    unfold storedLength
    omega
  constructor <;> intro j k
  · exact (rational_parts_le_two_pow_length _).1.trans (Nat.pow_le_pow_right (by decide) (hlen j k))
  · exact (rational_parts_le_two_pow_length _).2.trans (Nat.pow_le_pow_right (by decide) (hlen j k))

theorem totalTicks_stored {n : ℕ} (M : DenseRatMatrix n) (x : Fin n → ℚ) (i : Fin n) :
    totalTicks M (storedLength M x i) x i ≤
      KS.W29.polynomialFuel 1000000000000 8 (storedLength M x i) := by
  let L := storedLength M x i
  let ps := rowPairs M i (indexedVector x)
  have hloop := loopTicks_stored M x i
  have hwire := pair_stream_length M x i
  have hdot := FixedDot.totalTicks_le_polynomial ps
  have hv : (vectorTape x).length ≤ L := by dsimp [L, storedLength]; omega
  have hn : (Computability.encodeNat n).length ≤ L := by dsimp [L, storedLength]; omega
  have hw1 : (FixedDot.inputWire ps).length + 1 ≤ 6 * (L + 1) ^ 2 := by
    dsimp [ps, L] at *
    nlinarith
  have hp : ((FixedDot.inputWire ps).length + 1) ^ 4 ≤ (6 * (L + 1) ^ 2) ^ 4 := by gcongr
  have hdot' : FixedDot.totalTicks ps ≤ 259200000000 * (L + 1) ^ 8 := by
    calc
      _ ≤ 200000000 * ((FixedDot.inputWire ps).length + 1) ^ 4 := hdot
      _ ≤ 200000000 * (6 * (L + 1) ^ 2) ^ 4 := Nat.mul_le_mul_left _ hp
      _ = _ := by ring
  have hgrow : (L + 1) ^ 4 ≤ (L + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  have hgrow2 : (L + 1) ^ 2 ≤ (L + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  have hgrow1 : L + 1 ≤ (L + 1) ^ 8 := by
    simpa only [pow_one] using (Nat.pow_le_pow_right (n := L + 1) (by omega) (show 1 ≤ 8 by decide))
  unfold totalTicks prepareTicks finishTicks KS.W29.polynomialFuel
  change _ ≤ 1000000000000 * (L + 1) ^ 8
  dsimp only [L, ps] at *
  omega

end KS.W12.RowDot

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_ZeroPaddedRow
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationMachine.input_port _root_.OAI.KS.W03.MultiplicationMachine.output_port _root_.OAI.KS.W03.MultiplicationMachine.stack_count _root_.OAI.KS.W03.MultiplicationMachine.state_count _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W06.RationalSignClassifier.program_output
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.RowDot
open Matrix
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07
open scoped BigOperators

theorem literalPush_spec {k : ℕ} (port : Fin k) (b : Bool) (s : Fin k → List Bool) :
    RunSpec (literalPush port b) s (Function.update s port (b :: s port)) 1 := by
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons coin rest =>
      have hr : rest = [] := by simpa using hbits
      subst rest
      refine (KS.W19.MachineTransport.run_ofMachine
        (compile (0 : Fin 1) port port (literalDispatch port b))
        (⟨some (0 : Fin 1), s⟩ : Config k 1) [coin]).trans ?_
      simp only [Machine.run]
      refine (step_compile (0 : Fin 1) port port (literalDispatch port b)
        (0 : Fin 1) s coin).trans ?_
      change (Config.mk (none : Option (Fin 1)) _ : Config k 1) = Config.mk none _
      apply congrArg (fun ws : Fin k → List Bool =>
        (Config.mk (none : Option (Fin 1)) ws : Config k 1))
      funext j
      by_cases hj : j = port
      · subst j
        simp [literalDispatch, Instruction.action, KS.W29.StackAction.apply]
      · simp [literalDispatch, Instruction.action, KS.W29.StackAction.apply, hj]

end KS.W12.RowDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_NegativeDivision
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W06.RationalSignClassifier.program_output _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.RowDot
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem division_spec (saved : Fin 29 → List Bool) (q r : ℚ) :
    RunSpec divisionProgram (arithmeticState saved (KS.W01.encodeRat q ++ KS.W01.encodeRat r) [])
      (arithmeticState saved [] (KS.W01.encodeRat (q / r))) (KS.W30.RationalDivision.totalTicks q r) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ _ _ _ _ _ _ (KS.W30.RationalDivision.full_spec q r)
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro j hj
    have h0 : j ≠ 0 := hj 0
    have h10 : j ≠ 10 := hj 10
    simp [arithmeticState, h0, h10]

theorem minusOne_spec (s : Fin 29 → List Bool) :
    RunSpec minusOneProgram s (put s 0 (KS.W01.encodeRat (-1) ++ s 0)) 5 := by
  let s1 := put s 0 (true :: s 0)
  let s2 := put s1 0 (true :: s1 0)
  let s3 := put s2 0 (false :: s2 0)
  let s4 := put s3 0 (true :: s3 0)
  have h := ((((literalPush_spec (0 : Fin 29) true s).compose
    (literalPush_spec 0 true s1)).compose (literalPush_spec 0 false s2)).compose
    (literalPush_spec 0 true s3)).compose (literalPush_spec 0 true s4)
  have he : KS.W01.encodeRat (-1) = [true, true, false, true, true] := by decide
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  funext j
  by_cases hj : j = 0 <;> simp [s1, s2, s3, s4, put, hj, he]

theorem product_spec (saved : Fin 29 → List Bool) (q r : ℚ) :
    RunSpec productProgram (arithmeticState saved (KS.W01.encodeRat q ++ KS.W01.encodeRat r) [])
      (arithmeticState saved [] (KS.W01.encodeRat (q * r))) (KS.W15.RationalMultiply.totalTicks q r) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ _ _ _ _ _ _ (KS.W15.RationalMultiply.full_spec q r)
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro j hj
    have h0 : j ≠ 0 := hj 0
    have h10 : j ≠ 10 := hj 10
    simp [arithmeticState, h0, h10]

def negativeDivisionTicks (q r : ℚ) : ℕ := KS.W30.RationalDivision.totalTicks q r + 5 +
  (2 * (KS.W01.encodeRat (q / r)).length + 2) + KS.W15.RationalMultiply.totalTicks (q / r) (-1)

theorem negativeDivision_spec (saved : Fin 29 → List Bool) (q r : ℚ) (hs : saved 26 = []) :
    RunSpec negativeDivisionProgram
      (arithmeticState saved (KS.W01.encodeRat q ++ KS.W01.encodeRat r) [])
      (arithmeticState saved [] (KS.W01.encodeRat (-(q / r)))) (negativeDivisionTicks q r) := by
  let s := arithmeticState saved [] (KS.W01.encodeRat (q / r))
  let t := put s 0 (KS.W01.encodeRat (-1))
  have h1 := division_spec saved q r
  have h2 : RunSpec minusOneProgram s t 5 := by simpa [s, t, arithmeticState] using minusOne_spec s
  have h3 : RunSpec (StackTransfer.program 10 0 26) t
      (arithmeticState saved (KS.W01.encodeRat (q / r) ++ KS.W01.encodeRat (-1)) [])
      (2 * (KS.W01.encodeRat (q / r)).length + 2) := by
    convert StackTransfer.spec (10 : Fin 29) 0 26 (by decide) (by decide) (by decide) t
      (by simp [t, s, put, arithmeticState, hs]) using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
    funext j
    fin_cases j <;> simp [StackTransfer.after, t, s, put, arithmeticState]
  have h4 := product_spec saved (q / r) (-1)
  have h := ((h1.compose h2).compose h3).compose h4
  simpa [negativeDivisionProgram, negativeDivisionTicks] using h

theorem negativeDivisionTicks_le (q r : ℚ) :
    negativeDivisionTicks q r ≤ KS.W29.polynomialFuel 100000000 3
      (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length := by
  let N := KS.W01.ratLength q + KS.W01.ratLength r + 1
  have hN : 0 < N := by dsimp [N]; omega
  have hd := KS.W30.RationalDivision.totalTicks_le_polynomial q r
  have hq := KS.W01.ratLength_div_le q r
  have hm := KS.W15.RationalMultiply.totalTicks_le_polynomial (q / r) (-1)
  have hminus : KS.W01.ratLength (-1) = 5 := by decide
  have hpair : (KS.W15.RationalMultiply.inputBits (q / r) (-1)).length + 1 ≤ 13 * N := by
    simp only [KS.W15.RationalMultiply.inputBits, List.length_append]
    change KS.W01.ratLength (q / r) + KS.W01.ratLength (-1) + 1 ≤ 13 * N
    rw [hminus]
    dsimp [N]
    omega
  have hm' : KS.W15.RationalMultiply.totalTicks (q / r) (-1) ≤ 4499456 * N ^ 3 := by
    calc
      _ ≤ 2048 * ((KS.W15.RationalMultiply.inputBits (q / r) (-1)).length + 1) ^ 3 := hm
      _ ≤ 2048 * (13 * N) ^ 3 := by gcongr
      _ = _ := by ring
  have hl : N ≤ N ^ 3 := Nat.le_self_pow (by decide) N
  change negativeDivisionTicks q r ≤ 100000000 * ((KS.W01.encodeRat q ++ KS.W01.encodeRat r).length + 1) ^ 3
  simp only [List.length_append]
  change negativeDivisionTicks q r ≤ 100000000 * N ^ 3
  unfold negativeDivisionTicks
  change KS.W30.RationalDivision.totalTicks q r + 5 + (2 * KS.W01.ratLength (q / r) + 2) +
    KS.W15.RationalMultiply.totalTicks (q / r) (-1) ≤ _
  simp only [KS.W29.polynomialFuel, KS.W30.RationalDivision.inputBits,
    List.length_append] at hd
  change KS.W30.RationalDivision.totalTicks q r ≤ 1100000 * N ^ 3 at hd
  dsimp [N] at *
  omega

end KS.W12.RowDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalSignClassifier
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
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

theorem read_spec (q : ℚ) :
    RunSpec readProgram (SingleRationalParser.inputState (KS.W01.encodeRat q))
      (classifiedCanonical q) (readTicks q) := by
  have hp := SingleRationalParser.canonical_spec q []
  simp only [List.append_nil] at hp
  exact hp.compose (classify_spec (parsedState q) _ _ rfl rfl rfl)

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

def negNodeTicks (q : ℚ) : Nat :=
  (2 * ratLength q + 2 + 6) + RationalMultiply.totalTicks (-1) q + (2 * ratLength (-q) + 2)

theorem mulNodeTicks_le (q r : ℚ) :
    mulNodeTicks q r ≤ 4096 * (ratLength q + ratLength r + 1) ^ 3 := by
  have ht := RationalMultiply.totalTicks_le_polynomial q r
  have hs := ratLength_mul_le q r
  have hp : ratLength q + ratLength r + 1 ≤ (ratLength q + ratLength r + 1)^3 :=
    Nat.le_self_pow (by decide) _
  simp only [RationalMultiply.inputBits,List.length_append] at ht
  change RationalMultiply.totalTicks q r ≤ 2048 * (ratLength q + ratLength r + 1)^3 at ht
  change 4 * ratLength q + 2 * ratLength r + 6 + RationalMultiply.totalTicks q r +
    (2 * ratLength (q*r) + 2) ≤ _
  omega

theorem addNodeTicks_le (q r : ℚ) :
    addNodeTicks q r ≤ 4096 * (ratLength q + ratLength r + 1) ^ 3 := by
  have ht := KS.W13.RationalAdd.totalTicks_le_polynomial q r
  have hs := ratLength_add_le q r
  have hp : ratLength q + ratLength r + 1 ≤ (ratLength q + ratLength r + 1)^3 :=
    Nat.le_self_pow (by decide) _
  simp only [List.length_append] at ht
  change KS.W13.RationalAdd.totalTicks q r ≤ 1000 * (ratLength q + ratLength r + 1)^3 at ht
  change 4 * ratLength q + 2 * ratLength r + 6 + KS.W13.RationalAdd.totalTicks q r +
    (2 * ratLength (q+r) + 2) ≤ _
  omega

theorem negNodeTicks_le (q : ℚ) : negNodeTicks q ≤ 1048576 * (ratLength q + 1)^3 := by
  have ht := RationalMultiply.totalTicks_le_polynomial (-1) q
  simp only [RationalMultiply.inputBits,List.length_append] at ht
  have hlen : ratLength (-1) = 5 := by decide
  have hs := ratLength_neg_le q
  have hp : ratLength q + 1 ≤ (ratLength q + 1)^3 := Nat.le_self_pow (by decide) _
  have hbase : ratLength (-1) + ratLength q + 1 ≤ 6 * (ratLength q + 1) := by omega
  have hpower := Nat.mul_le_mul_left 2048 (Nat.pow_le_pow_left hbase 3)
  have ht' : RationalMultiply.totalTicks (-1) q ≤ 442368 * (ratLength q + 1)^3 := by
    change RationalMultiply.totalTicks (-1) q ≤ 2048 * (ratLength (-1) + ratLength q + 1)^3 at ht
    exact ht.trans (by nlinarith [hpower])
  unfold negNodeTicks
  omega

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

def ticks (a b : ℚ) : ℕ := (KS.W01.encodeRat 1).length+1 +
  ((KS.W01.encodeRat 2).length+1 + (addNodeTicks a 1 +
    (mulNodeTicks 2 b + (negNodeTicks (a+1) + divNodeTicks (-(a+1)) (2*b)))))

end KS.W19.SparseScalarNodes

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_SparseScalarCost
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.sumBudget_cons _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.SparseScalarNodes
open KS.W01 KS.W15.ComplexMachine

theorem ratLength_div_le (q r : ℚ) : ratLength (q/r) ≤ 4*(ratLength q+ratLength r)+7 := by
  obtain ⟨hn,hd⟩ := rational_parts_le_two_pow_length q
  obtain ⟨rn,rd⟩ := rational_parts_le_two_pow_length r
  obtain ⟨outn,outd⟩ := KS.W30.div_parts_le_two_pow q r (ratLength q) (ratLength r) hn hd rn rd
  have h := ratLength_le_of_parts (q/r) _ _ outn outd
  omega

theorem divNodeTicks_le (q r : ℚ) :
    divNodeTicks q r ≤ 1200000*(ratLength q+ratLength r+1)^3 := by
  have hs := ratLength_div_le q r
  have hp : ratLength q+ratLength r+1 ≤ (ratLength q+ratLength r+1)^3 :=
    Nat.le_self_pow (by decide) _
  simp only [divNodeTicks,divTicks,pairTicks,KS.W30.RationalDivision.inputBits,
    KS.W29.polynomialFuel,List.length_append]
  change 4*ratLength q+2*ratLength r+6 +
    1100000*(ratLength q+ratLength r+1)^3 + (2*ratLength (q/r)+2) ≤ _
  omega

theorem ticks_polynomial (a b : ℚ) :
    ticks a b ≤ 3000000*(200*(ratLength a+ratLength b+1))^3 := by
  have l1 : ratLength (1 : ℚ) = 7 := by decide
  have l2 : ratLength (2 : ℚ) = 9 := by decide
  have la := ratLength_add_le a 1
  have lb := ratLength_mul_le 2 b
  have ln := ratLength_neg_le (a+1)
  rw [l1] at la
  rw [l2] at lb
  let H := 200*(ratLength a+ratLength b+1)
  have h1 : ratLength a+ratLength (1 : ℚ)+1 ≤ H := by rw [l1]; dsimp [H]; omega
  have h2 : ratLength (2 : ℚ)+ratLength b+1 ≤ H := by rw [l2]; dsimp [H]; omega
  have h3 : ratLength (a+1)+1 ≤ H := by dsimp [H]; omega
  have h4 : ratLength (-(a+1))+ratLength (2*b)+1 ≤ H := by dsimp [H]; omega
  have t1 := (addNodeTicks_le a 1).trans (Nat.mul_le_mul_left 4096 (Nat.pow_le_pow_left h1 3))
  have t2 := (mulNodeTicks_le 2 b).trans (Nat.mul_le_mul_left 4096 (Nat.pow_le_pow_left h2 3))
  have t3 := (negNodeTicks_le (a+1)).trans (Nat.mul_le_mul_left 1048576 (Nat.pow_le_pow_left h3 3))
  have t4 := (divNodeTicks_le (-(a+1)) (2*b)).trans (Nat.mul_le_mul_left 1200000 (Nat.pow_le_pow_left h4 3))
  have hp : H ≤ H^3 := Nat.le_self_pow (by decide) _
  have hH : 200 ≤ H := by dsimp [H]; omega
  change (encodeRat 1).length+1+((encodeRat 2).length+1+
    (addNodeTicks a 1+(mulNodeTicks 2 b+(negNodeTicks (a+1)+divNodeTicks (-(a+1)) (2*b))))) ≤ 3000000*H^3
  change ratLength (1 : ℚ)+1+(ratLength (2 : ℚ)+1+_) ≤ _
  rw [l1,l2]
  omega

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

def ticks (s : Fin 35 → List Bool) (a b : ℚ) : ℕ := SparseScalarNodes.ticks a b +
  KS.W04.CleanRationalCompare.clearListTicks cleanupPorts (after s a b)

end KS.W19.SparseCoefficientStage

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
open KS.W04.ReusableArrayLookup (run_halted_of_length_ge run_compose_bounded)

theorem replaceFuel_linear («prefix» : List (List Bool)) (old new tail : List Bool) :
    replaceFuel «prefix» old new ≤
      2 * («prefix».flatMap KS.W01.frame ++ KS.W01.frame old ++ tail).length +
        2 * (KS.W01.frame new).length + «prefix».length + 3 := by
  simp only [replaceFuel, KS.W11.FramedArray.scanFuel, List.length_append,
    KS.W01.length_frame]
  omega

end KS.W11.FramedArrayRewrite

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

def scalarTicks {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (j : Fin (n+1)) : ℕ :=
  SparseCoefficientStage.ticks (collected saved M j)
    (DenseRatMatrix.decode M j j) (DenseRatMatrix.decode M 0 j)

def ticks {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (B : ℕ) (j : Fin (n+1)) : ℕ :=
  collectTicks saved M B j + (scalarTicks saved M j + TerminalSparseAssembly.ticks (n+1) j.val (coefficient M j))

end KS.W19.TerminalWitnessMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_TerminalWitnessCost
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.TerminalWitnessMachine
open KS.W01 KS.W07

theorem cleanupTicks_linear {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (j : Fin (n+1)) :
    KS.W04.CleanRationalCompare.clearListTicks SparseCoefficientStage.cleanupPorts
      (SparseCoefficientStage.after (collected saved M j)
        (DenseRatMatrix.decode M j j) (DenseRatMatrix.decode M 0 j)) ≤
      300*(ratLength (DenseRatMatrix.decode M j j)+ratLength (DenseRatMatrix.decode M 0 j)+j.val+1) := by
  let a := DenseRatMatrix.decode M j j
  let b := DenseRatMatrix.decode M 0 j
  have h1 := ratLength_add_le a 1
  have h2 := ratLength_mul_le 2 b
  have h3 := ratLength_neg_le (a+1)
  have hj := raw_length_le j.val
  have l1 : ratLength (1 : ℚ) = 7 := by decide
  have l2 : ratLength (2 : ℚ) = 9 := by decide
  rw [l1] at h1
  rw [l2] at h2
  change (ratLength a+1) + ((ratLength b+1) + ((ratLength (a+1)+1) +
    ((ratLength (2*b)+1) + ((ratLength (1 : ℚ)+1) + ((ratLength (2 : ℚ)+1) +
    ((ratLength (-(a+1))+1) + ((Computability.encodeNat j.val).length+1+1))))))) ≤
      300*(ratLength a+ratLength b+j.val+1)
  omega

end KS.W19.TerminalWitnessMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_SchurWitnessHead
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W06.RationalSignClassifier.program_output _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W17.FixedPSD.withSaved_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.RowDot
open Matrix
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07
open scoped BigOperators

def schurHeadTicks {n : ℕ} (M : DenseRatMatrix (n + 1)) (b : ℕ) (y : Fin n → ℚ) : ℕ :=
  totalTicks M b (zeroPadded y) 0 +
  ((2 * (Computability.encodeNat (n + 1)).length + 2) + 1024 * (n + 2) ^ 2 * (b + 1)) +
  (2 * (KS.W01.encodeRat ((DenseRatMatrix.decode M *ᵥ zeroPadded y) 0)).length + 2) +
  negativeDivisionTicks ((DenseRatMatrix.decode M *ᵥ zeroPadded y) 0) (DenseRatMatrix.decode M 0 0)

theorem schurHead_spec {n : ℕ} (M : DenseRatMatrix (n + 1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2 ^ b) (y : Fin n → ℚ) :
    RunSpec schurHeadProgram (initialStacks M (zeroPadded y) 0)
      (put (initialStacks M (zeroPadded y) 0) 10 (KS.W01.encodeRat (schurHead M y)))
      (schurHeadTicks M b y) := by
  let z := (DenseRatMatrix.decode M *ᵥ zeroPadded y) 0
  let pivot := DenseRatMatrix.decode M 0 0
  let saved := initialStacks M (zeroPadded y) 0
  let s := put saved 17 (KS.W01.encodeRat z)
  let t := put s 2 (Computability.encodeNat (n + 1))
  let u := put s 0 (KS.W01.encodeRat pivot)
  have h1 := full_spec M b hnum hden (zeroPadded y) 0
  have h2 : RunSpec copyDimension s t (2 * (Computability.encodeNat (n + 1)).length + 2) :=
    copy_spec 22 2 (by decide) (by decide) (by decide) s rfl rfl
  have h3 : RunSpec readProgram t u (1024 * (n + 2) ^ 2 * (b + 1)) := by
    convert read_spec M b hnum hden 0 0 s rfl (by intro j; fin_cases j <;> rfl) using 1
    all_goals try with_reducible_and_instances rfl
    funext j
    fin_cases j <;>
      simp [t, s, readBefore, put, saved, initialStacks, state, Computability.encodeNat] <;> rfl
  have h4 : RunSpec (StackTransfer.program 17 0 26) u
      (arithmeticState saved (KS.W01.encodeRat z ++ KS.W01.encodeRat pivot) [])
      (2 * (KS.W01.encodeRat z).length + 2) := by
    convert StackTransfer.spec (17 : Fin 29) 0 26 (by decide) (by decide) (by decide) u rfl using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
    funext j
    fin_cases j <;> simp [u, s, saved, initialStacks, state, arithmeticState, StackTransfer.after, put]
  have h5 := negativeDivision_spec saved z pivot (by rfl)
  have h := ((h1.compose (h2.compose h3)).compose h4).compose h5
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  funext j
  fin_cases j <;> simp [schurHead, z, pivot, saved, put, arithmeticState, initialStacks, state,
    zeroPadded_row_dot]

theorem schurHeadTicks_stored {n : ℕ} (M : DenseRatMatrix (n + 1)) (y : Fin n → ℚ) :
    schurHeadTicks M (storedLength M (zeroPadded y) 0) y ≤
      KS.W29.polynomialFuel 10000000000000000 8 (storedLength M (zeroPadded y) 0) := by
  let L := storedLength M (zeroPadded y) 0
  let z := (DenseRatMatrix.decode M *ᵥ zeroPadded y) 0
  let p := DenseRatMatrix.decode M 0 0
  have hbase := totalTicks_stored M (zeroPadded y) 0
  have hw := pair_stream_length M (zeroPadded y) 0
  have hz := FixedDot.dotValue_length_le_wire (rowPairs M 0 (indexedVector (zeroPadded y)))
  rw [rowPairs_dotValue] at hz
  have hp := matrix_entry_length M 0 0
  have hp' : KS.W01.ratLength p ≤ L := by dsimp [p, L, storedLength]; omega
  have hn : n + 1 ≤ L := by
    have h := dimension_le_vector (zeroPadded y)
    dsimp [L, storedLength]; omega
  have hnwire : (Computability.encodeNat (n + 1)).length ≤ L := by
    dsimp [L, storedLength]; omega
  have hz' : KS.W01.ratLength z ≤ 167 * (L + 1) ^ 2 := by
    dsimp [z, L] at *
    nlinarith
  have hpw : (KS.W01.encodeRat z ++ KS.W01.encodeRat p).length + 1 ≤ 168 * (L + 1) ^ 2 := by
    simp only [List.length_append]
    change KS.W01.ratLength z + KS.W01.ratLength p + 1 ≤ _
    nlinarith
  have hneg : negativeDivisionTicks z p ≤ 474163200000000 * (L + 1) ^ 6 := by
    calc
      _ ≤ 100000000 * ((KS.W01.encodeRat z ++ KS.W01.encodeRat p).length + 1) ^ 3 :=
        negativeDivisionTicks_le z p
      _ ≤ 100000000 * (168 * (L + 1) ^ 2) ^ 3 := by gcongr
      _ = _ := by ring
  have hr : 1024 * (n + 2) ^ 2 * (L + 1) ≤ 1024 * (L + 1) ^ 3 := by
    calc
      _ ≤ 1024 * (L + 1) ^ 2 * (L + 1) :=
        Nat.mul_le_mul_right (L + 1) (Nat.mul_le_mul_left 1024
          (Nat.pow_le_pow_left (show n + 2 ≤ L + 1 by omega) 2))
      _ = _ := by ring
  have h6 : (L + 1) ^ 6 ≤ (L + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  have h3 : (L + 1) ^ 3 ≤ (L + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  have h2 : (L + 1) ^ 2 ≤ (L + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  have h1 : L + 1 ≤ (L + 1) ^ 8 := by
    simpa only [pow_one] using (Nat.pow_le_pow_right (n := L + 1) (by omega) (show 1 ≤ 8 by decide))
  unfold schurHeadTicks KS.W29.polynomialFuel
  change _ ≤ 10000000000000000 * (L + 1) ^ 8
  change totalTicks M L (zeroPadded y) 0 ≤ 1000000000000 * (L + 1) ^ 8 at hbase
  dsimp only [z, p, L] at *
  unfold KS.W01.ratLength at hz'
  omega

theorem schurHead_polynomial_spec {n : ℕ} (M : DenseRatMatrix (n + 1)) (y : Fin n → ℚ) :
    RunSpec schurHeadProgram (initialStacks M (zeroPadded y) 0)
      (put (initialStacks M (zeroPadded y) 0) 10 (KS.W01.encodeRat (schurHead M y)))
      (KS.W29.polynomialFuel 10000000000000000 8 (storedLength M (zeroPadded y) 0)) := by
  obtain ⟨hn, hd⟩ := matrix_parts_stored M (zeroPadded y) 0
  exact (schurHead_spec M _ hn hd y).mono (schurHeadTicks_stored M y)

end KS.W12.RowDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_StoredWitnessLift
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationMachine.input_port _root_.OAI.KS.W03.MultiplicationMachine.output_port _root_.OAI.KS.W03.MultiplicationMachine.stack_count _root_.OAI.KS.W03.MultiplicationMachine.state_count _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W06.RationalSignClassifier.program_output
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.StoredWitnessLift
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07
open KS.W12.RowDot

theorem runSpec_stack_length_le {k : ℕ} (P : Program k)
    (before after : Fin k → List Bool) (budget : ℕ)
    (hP : RunSpec P before after budget) (j : Fin k) :
    (after j).length ≤ (before j).length + budget := by
  let bs := List.replicate budget false
  have hexec := hP bs (by simp [bs])
  have h := P.toMachine.run_stack_length_le
    (⟨some P.initial, before⟩ : Config k P.states) bs j
  have hout := congrArg (fun c : Config k P.states => (c.«stacks» j).length) hexec
  have hfinal := hout.symm.trans_le h
  simpa only [bs, List.length_replicate] using hfinal

theorem head_length_le_budget {n : ℕ} (M : DenseRatMatrix (n + 1)) (y : Fin n → ℚ) :
    (KS.W01.encodeRat (schurHead M y)).length ≤ headBudget M y := by
  have h := runSpec_stack_length_le schurHeadProgram
    (initialStacks M (zeroPadded y) 0)
    (put (initialStacks M (zeroPadded y) 0) 10 (KS.W01.encodeRat (schurHead M y)))
    (headBudget M y) (schurHead_polynomial_spec M y) (10 : Fin 29)
  change (KS.W01.encodeRat (schurHead M y)).length ≤ ([] : List Bool).length + headBudget M y at h
  simpa only [List.length_nil, Nat.zero_add] using h

theorem ticks_polynomial {n : ℕ} (M : DenseRatMatrix (n + 1)) (y : Fin n → ℚ) :
    ticks M y ≤ KS.W29.polynomialFuel 10000000000000000000000000000 8 (inputLength M y) := by
  have hh := head_length_le_budget M y
  have hb := headBudget_le M y
  have ht : (vectorTape y).length ≤ inputLength M y := by unfold inputLength; omega
  have hzero : (KS.W01.frame (KS.W01.encodeRat 0)).length = 11 := by decide
  have hp : (vectorTape (zeroPadded y)).length = 11 + (vectorTape y).length := by
    simp only [zeroPadded, vectorTape_cons, List.length_append, hzero]
  have hgrow : inputLength M y + 1 ≤ (inputLength M y + 1) ^ 8 := by
    simpa only [pow_one] using (Nat.pow_le_pow_right (n := inputLength M y + 1) (by omega)
      (show 1 ≤ 8 by decide))
  unfold ticks KS.W29.polynomialFuel
  rw [hp, KS.W01.length_frame]
  omega

end KS.W12.StoredWitnessLift

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_ControllerReachable
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W17.FixedPSD.withSaved_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W07

theorem ControllerReachable.matrix_tape_length {N n : ℕ} {A : DenseRatMatrix N} {M : DenseRatMatrix n}
    {h : PivotHistory n N} (hr : ControllerReachable A M h) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode A i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode A i j).den ≤ 2^b) :
    (KS.W08.denseMatrixTape M).length ≤ N*N*(8*KS.W30.inverseBitBound N b+15) := by
  have hp := fun i j => hr.call.entry_parts_size_le b hnum hden i j
  have ht := KS.W08.denseMatrixTape_length_le M (KS.W30.inverseBitBound N b)
    (fun i j => (Nat.size_le.mp (hp i j).1).le)
    (fun i j => (Nat.size_le.mp (hp i j).2).le)
  exact ht.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul hr.call.dimension_le hr.call.dimension_le))

theorem commonHeight_vector_tape_length {n E : ℕ} {q : Fin n → ℚ} (h : CommonHeight q E) :
    (KS.W12.RowDot.vectorTape q).length ≤ n*(8*E+15) := by
  have hl (i : Fin n) : KS.W01.ratLength (q i) ≤ 4*E+7 := by
    have hp := h.parts_bound i
    have hh := KS.W01.ratLength_le_of_parts (q i) E E hp.1 hp.2
    omega
  have he : (KS.W12.RowDot.vectorTape q).length =
      ∑ i : Fin n, (2*KS.W01.ratLength (q i)+1) := by
    simp [KS.W12.RowDot.vectorTape,List.length_flatMap,List.sum_ofFn,KS.W01.length_frame,KS.W01.ratLength]
  rw [he]
  calc
    _ ≤ ∑ _i : Fin n, (8*E+15) := Finset.sum_le_sum (fun i _ => by have := hl i; omega)
    _ = _ := by simp

theorem ControllerReachable.witness_tape_length {N n : ℕ} {A : DenseRatMatrix N} {M : DenseRatMatrix n}
    {h : PivotHistory n N} (hr : ControllerReachable A M h) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode A i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode A i j).den ≤ 2^b)
    (q : Fin n → ℚ) (hq : uniformNegativeWitness n (DenseRatMatrix.decode M) = some q) :
    (KS.W12.RowDot.vectorTape q).length ≤ N*(8*witnessHeightBudget N b N+15) := by
  have hc := uniform_witness_height hr.call b hnum hden q hq
  have he : witnessHeightBudget N b n ≤ witnessHeightBudget N b N := by
    unfold witnessHeightBudget
    exact Nat.mul_le_mul_right _ (Nat.add_le_add_right hr.call.dimension_le 1)
  exact (commonHeight_vector_tape_length (hc.mono he)).trans (Nat.mul_le_mul_right _ hr.call.dimension_le)

theorem ControllerReachable.history_tape_length {N n : ℕ} {A : DenseRatMatrix N} {M : DenseRatMatrix n}
    {h : PivotHistory n N} (hr : ControllerReachable A M h) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode A i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode A i j).den ≤ 2^b) :
    (historyTape h).length ≤ h.depth * originalFrameBound N b := by
  induction hr with
  | initial => simp [historyTape,PivotHistory.depth]
  | @descend n M h previous ht ih =>
    have hm := previous.matrix_tape_length b hnum hden
    have hd := previous.call.dimension_le
    have hraw := KS.W19.TerminalWitnessMachine.raw_length_le (n+1)
    have hframe : (savedFrame (Computability.encodeNat (n+1)) (KS.W08.denseMatrixTape M)).length ≤
        originalFrameBound N b := by
      simp only [savedFrame,KS.W01.length_frame,KS.W08.SavedPivotPacket.payload,List.length_append]
      unfold originalFrameBound originalMatrixTapeBound
      omega
    simp only [historyTape,DenseRatMatrix.ofMatrix_decode,List.length_append,PivotHistory.depth]
    nlinarith

end KS.W17.FixedPSD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_ControllerReplayBound
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W17.FixedPSD.withSaved_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W07

theorem ControllerReachable.restore_ticks_le {N n : ℕ} {A : DenseRatMatrix N} {M : DenseRatMatrix n}
    {h : PivotHistory n N} (hr : ControllerReachable A M h) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode A i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode A i j).den ≤ 2^b)
    (q : Fin n → ℚ) (hq : uniformNegativeWitness n (DenseRatMatrix.decode M) = some q) :
    restoreTicks h q ≤ (h.depth+1)*originalReplayStepBound N b := by
  induction hr with
  | initial =>
    simp only [restoreTicks,PivotHistory.depth,zero_add,one_mul]
    unfold originalReplayStepBound
    omega
  | @descend n M h previous ht ih =>
    have hchild : uniformNegativeWitness n (schurTail (DenseRatMatrix.decode M)) = some q := by
      simpa [child] using hq
    have hparent : uniformNegativeWitness (n+1) (DenseRatMatrix.decode M) =
        some (schurWitnessLift (DenseRatMatrix.decode M) q) := by
      simp [uniformNegativeWitness,ht,hchild]
    have htail := (ControllerReachable.descend previous ht).witness_tape_length b hnum hden q hq
    have hhead := previous.witness_tape_length b hnum hden
      (schurWitnessLift (DenseRatMatrix.decode M) q) hparent
    have hmatrix := previous.matrix_tape_length b hnum hden
    have hdim := previous.call.dimension_le
    have hraw := KS.W19.TerminalWitnessMachine.raw_length_le (n+1)
    have hin : KS.W12.StoredWitnessLift.inputLength M q ≤ originalReplayInputBound N b := by
      unfold KS.W12.StoredWitnessLift.inputLength originalReplayInputBound
        originalMatrixTapeBound originalWitnessTapeBound
      omega
    have hwork : KS.W12.StoredWitnessLift.ticks M q ≤
        10000000000000000000000000000*(originalReplayInputBound N b+1)^8 := by
      have hh := KS.W12.StoredWitnessLift.ticks_polynomial M q
      unfold KS.W29.polynomialFuel at hh
      exact hh.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 8))
    have hlift : (liftedTape M q).length ≤ originalWitnessTapeBound N b := hhead
    have hstep : 1+(9*(Computability.encodeNat (n+1)).length+3*(KS.W08.denseMatrixTape M).length+7+
        replayTicks M q) ≤ originalReplayStepBound N b := by
      unfold replayTicks originalReplayStepBound originalReplayInputBound
        originalMatrixTapeBound originalWitnessTapeBound at *
      omega
    have hi := ih (schurWitnessLift (DenseRatMatrix.decode M) q) hparent
    simp only [restoreTicks,DenseRatMatrix.ofMatrix_decode,PivotHistory.depth]
    nlinarith

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

def controllerTicks : {n N : ℕ} → PivotHistory n N → DenseRatMatrix n → ℕ
  | 0, _, h, _ => (historyTape h).length+1
  | n+1, _, h, M =>
    let b := localBits M
    if DenseRatMatrix.decode M 0 0 < 0 then
      1 + (PivotDecision.ticks M b+(((2+unitTicks n)+1+finishTicks h M (Pi.single 0 1))+1)) + 1
    else if DenseRatMatrix.decode M 0 0 = 0 then
      match firstNonzeroOffDiagonal (DenseRatMatrix.decode M) with
      | some j =>
        1 + (PivotDecision.ticks M b+
          (((2+KS.W19.TerminalWitnessMachine.ticks (historyTape h) M b j.succ)+1+
            finishTicks h M (zeroPivotWitness (DenseRatMatrix.decode M) 0 j.succ))+1)) + 1
      | none =>
        1+(PivotDecision.ticks M b+(descentTicks M b+1))+
          controllerTicks (.push (DenseRatMatrix.decode M) h) (child M)
    else
      1+(PivotDecision.ticks M b+(descentTicks M b+1))+
        controllerTicks (.push (DenseRatMatrix.decode M) h) (child M)

end KS.W17.FixedPSD

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_TerminalInputBounds
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.TerminalWitnessMachine
open KS.W07 KS.W01

theorem entry_parts_le_payload {n : ℕ} (M : DenseRatMatrix n) (i j : Fin n) :
    (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^(KS.W08.denseMatrixTape M).length ∧
      (DenseRatMatrix.decode M i j).den ≤ 2^(KS.W08.denseMatrixTape M).length := by
  obtain ⟨hn,hd⟩ := rational_parts_le_two_pow_length (DenseRatMatrix.decode M i j)
  have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (entry_length_le_payload M i j)
  exact ⟨hn.trans hp,hd.trans hp⟩

end KS.W19.TerminalWitnessMachine

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

theorem ControllerReachable.finish_ticks_le {N n : ℕ} {A : DenseRatMatrix N} {M : DenseRatMatrix n}
    {h : PivotHistory n N} (hr : ControllerReachable A M h) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode A i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode A i j).den ≤ 2^b)
    (q : Fin n → ℚ) (hq : uniformNegativeWitness n (DenseRatMatrix.decode M) = some q) :
    finishTicks h M q ≤ originalMatrixTapeBound N b+N+3+(N+1)*originalReplayStepBound N b := by
  have hm := hr.matrix_tape_length b hnum hden
  have hd := hr.call.dimension_le
  have hraw := KS.W19.TerminalWitnessMachine.raw_length_le n
  have hdepth := h.dimension_depth
  have hrestore := hr.restore_ticks_le b hnum hden q hq
  have hmono := Nat.mul_le_mul_right (originalReplayStepBound N b) (show h.depth+1≤N+1 by omega)
  unfold finishTicks originalMatrixTapeBound
  omega

end KS.W17.FixedPSD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_ExpressionPrimitives
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.sumBudget_cons _root_.OAI.KS.W12.RowDot.tailTape_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W13.ExpressionMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem binaryArithmetic_spec (op : BinaryOp) (q r : ℚ) (source : List Bool) (s : List ℚ) :
    RunSpec (binaryArithmetic op) (registers source (encodeStack s) (KS.W01.encodeRat q++KS.W01.encodeRat r) [] [] [])
      (registers source (encodeStack s) [] (KS.W01.encodeRat (op.eval q r)) [] []) (binaryBudget q r) := by
  cases op
  · have hsmall := KS.W13.RationalAdd.polynomial_spec q r
    have hlarge : RunSpec (binaryArithmetic .add)
        (registers source (encodeStack s) (KS.W01.encodeRat q++KS.W01.encodeRat r) [] [] [])
        (registers source (encodeStack s) [] (KS.W01.encodeRat (BinaryOp.add.eval q r)) [] [])
        (KS.W29.polynomialFuel 1000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length) := by
      apply KS.W01.FixedPortRunSpec.lift_runSpec KS.W13.RationalAdd.program (firstPorts 16 (by decide)) _ _ _ _ _ hsmall
      · intro i; fin_cases i <;> rfl
      · intro i; fin_cases i <;> rfl
      · intro j hj
        have h0 : j ≠ 0 := hj 0
        have h10 : j ≠ 10 := hj 10
        simp [registers,h0,h10]
    apply hlarge.mono
    simp only [KS.W29.polynomialFuel,List.length_append]
    change _ * (KS.W01.ratLength q+KS.W01.ratLength r+1)^3 ≤ binaryBudget q r
    exact Nat.mul_le_mul_right _ (by decide)
  · have hsmall := KS.W13.RationalSubtract.polynomial_spec q r
    have hlarge : RunSpec (binaryArithmetic .sub)
        (registers source (encodeStack s) (KS.W01.encodeRat q++KS.W01.encodeRat r) [] [] [])
        (registers source (encodeStack s) [] (KS.W01.encodeRat (BinaryOp.sub.eval q r)) [] [])
        (KS.W29.polynomialFuel 600000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length) := by
      apply KS.W01.FixedPortRunSpec.lift_runSpec KS.W13.RationalSubtract.program (firstPorts 19 (by decide)) _ _ _ _ _ hsmall
      · intro i; fin_cases i <;> rfl
      · intro i; fin_cases i <;> rfl
      · intro j hj
        have h0 : j ≠ 0 := hj 0
        have h10 : j ≠ 10 := hj 10
        simp [registers,h0,h10]
    apply hlarge.mono
    simp only [KS.W29.polynomialFuel,List.length_append]
    change _ * (KS.W01.ratLength q+KS.W01.ratLength r+1)^3 ≤ binaryBudget q r
    exact Nat.mul_le_mul_right _ (by decide)
  · have hsmall := (KS.W15.RationalMultiply.full_spec q r).mono (KS.W15.RationalMultiply.totalTicks_le_polynomial q r)
    have hlarge : RunSpec (binaryArithmetic .mul)
        (registers source (encodeStack s) (KS.W01.encodeRat q++KS.W01.encodeRat r) [] [] [])
        (registers source (encodeStack s) [] (KS.W01.encodeRat (BinaryOp.mul.eval q r)) [] [])
        (KS.W29.polynomialFuel 2048 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length) := by
      apply KS.W01.FixedPortRunSpec.lift_runSpec KS.W15.RationalMultiply.program (firstPorts 13 (by decide)) _ _ _ _ _ hsmall
      · intro i; fin_cases i <;> rfl
      · intro i; fin_cases i <;> rfl
      · intro j hj
        have h0 : j ≠ 0 := hj 0
        have h10 : j ≠ 10 := hj 10
        simp [registers,h0,h10]
    apply hlarge.mono
    simp only [KS.W29.polynomialFuel,List.length_append]
    change _ * (KS.W01.ratLength q+KS.W01.ratLength r+1)^3 ≤ binaryBudget q r
    exact Nat.mul_le_mul_right _ (by decide)
  · have hsmall := KS.W30.RationalDivision.program_spec q r
    have hlarge : RunSpec (binaryArithmetic .div)
        (registers source (encodeStack s) (KS.W01.encodeRat q++KS.W01.encodeRat r) [] [] [])
        (registers source (encodeStack s) [] (KS.W01.encodeRat (BinaryOp.div.eval q r)) [] [])
        (KS.W29.polynomialFuel 1100000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length) := by
      apply KS.W01.FixedPortRunSpec.lift_runSpec KS.W30.RationalDivision.program (firstPorts 15 (by decide)) _ _ _ _ _ hsmall
      · intro i; fin_cases i <;> rfl
      · intro i; fin_cases i <;> rfl
      · intro j hj
        have h0 : j ≠ 0 := hj 0
        have h10 : j ≠ 10 := hj 10
        simp [registers,h0,h10]
    apply hlarge.mono
    simp only [KS.W29.polynomialFuel,List.length_append]
    change _ * (KS.W01.ratLength q+KS.W01.ratLength r+1)^3 ≤ binaryBudget q r
    exact Nat.mul_le_mul_right _ (by decide)

end KS.W13.ExpressionMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ArithmeticRoutine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.ArithmeticRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open CleanRoutine PairRoutine
open KS.W13.ExpressionMachine

lemma program_spec (op : BinaryOp) (q r : ℚ) :
    RunSpec (program op) (io (pair (encode q) (encode r)))
      (io (encode (op.eval q r))) (ticks op q r) := by
  have h := (decode_spec q r).compose ((prepend_spec q r).compose
    ((binaryArithmetic_spec op q r [] []).compose (extract_spec (op.eval q r))))
  simp only [ticks,Nat.add_assoc] at h ⊢
  exact h

def routine (op : BinaryOp) :
    Routine (fun p : ℚ×ℚ => pair (encode p.1) (encode p.2))
      (fun p => encode (op.eval p.1 p.2)) (fun p => ticks op p.1 p.2) where
  scratch := 23
  program := program op
  spec p := program_spec op p.1 p.2

end CurrentKS.ArithmeticRoutine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_FloorCleanRoutine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_wordLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.FloorCleanRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open CleanRoutine KS.W20.FloorRationalMachine

def cleanProgram : Program 11 := compose program extract

def routine : Routine encode (fun q => encode (⌊q⌋ : ℚ)) ticks where
  scratch := 10
  program := cleanProgram
  spec q := by
    have h := (polynomial_spec q).compose (extract_spec (⌊q⌋ : ℚ))
    have hi : state (encode q) []=(@io 10 (encode q)) := by
      funext j;fin_cases j <;> rfl
    simp only [hi] at h
    exact h

end CurrentKS.FloorCleanRoutine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ScalarRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
attribute [-simp] _root_.OAI.CurrentKS.Realization.listCode_cons _root_.OAI.CurrentKS.Realization.listCode_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine

def ratOp (op : KS.W13.ExpressionMachine.BinaryOp) :
    Realizes (prodCode ratCode ratCode) ratCode (fun p => op.eval p.1 p.2) where
  cost := fun p => ArithmeticRoutine.ticks op p.1 p.2
  routine := ArithmeticRoutine.routine op

def ratFloor : Realizes ratCode ratCode (fun q => (⌊q⌋ : ℚ)) where
  cost := FloorCleanRoutine.ticks
  routine := FloorCleanRoutine.routine

variable {α β : Type*} {encA : α → Word} {encB : β → Word}

def Realizes.add {f g : α → ℚ} (r : Realizes encA ratCode f) (s : Realizes encA ratCode g) :
    Realizes encA ratCode (fun x => f x+g x) := (r.both s).then (ratOp .add)
def Realizes.sub {f g : α → ℚ} (r : Realizes encA ratCode f) (s : Realizes encA ratCode g) :
    Realizes encA ratCode (fun x => f x-g x) := (r.both s).then (ratOp .sub)
def Realizes.mul {f g : α → ℚ} (r : Realizes encA ratCode f) (s : Realizes encA ratCode g) :
    Realizes encA ratCode (fun x => f x*g x) := (r.both s).then (ratOp .mul)

def Realizes.pow {function : α → ℚ} (realization : Realizes encA ratCode function) :
    (exponent : ℕ) → Realizes encA ratCode (fun input => function input ^ exponent)
  | 0 => (constant encA ratCode 1).congr (fun _ => (pow_zero _).symm)
  | exponent + 1 => ((realization.pow exponent).mul realization).congr
      (fun input => (pow_succ (function input) exponent).symm)

def Realizes.div {f g : α → ℚ} (r : Realizes encA ratCode f) (s : Realizes encA ratCode g) :
    Realizes encA ratCode (fun x => f x/g x) := (r.both s).then (ratOp .div)

def Realizes.neg {f : α → ℚ} (r : Realizes encA ratCode f) :
    Realizes encA ratCode (fun x => -f x) :=
  ((constant encA ratCode 0).sub r).congr (fun x => zero_sub (f x))

def Realizes.abs {f : α → ℚ} (r : Realizes encA ratCode f) :
    Realizes encA ratCode (fun x => |f x|) :=
  ((r.le (constant encA ratCode 0)).ite r.neg r).congr (by
    intro x
    by_cases h : f x≤0
    · simp [h,abs_of_nonpos h]
    · simp [h,abs_of_pos (lt_of_not_ge h)])

def roundScalar : Realizes (prodCode ratCode ratCode) ratCode
    (fun p => p.1*(⌊p.2/p.1⌋ : ℚ)) :=
  let rho := first ratCode ratCode
  let x := second ratCode ratCode
  rho.mul ((x.div rho).then ratFloor)

def sumRationals : Realizes (listCode ratCode) ratCode List.sum :=
  (((constant (listCode ratCode) ratCode 0).both (identity (listCode ratCode))).then
    (ratOp .add).fold).congr fold_add_zero

def l1Rationals : Realizes (listCode ratCode) ratCode (fun xs => (xs.map abs).sum) :=
  (identity ratCode).abs.map.then sumRationals

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ArrayRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α γ : Type*}

def natToRat : Realizes natCode ratCode (fun n => (n : ℚ)) :=
  let step := (identity ratCode).add (constant ratCode ratCode 1)
  (((identity natCode).both (constant natCode ratCode 0)).then step.iterate).congr (by
    intro n
    simp only [iterate_ratSucc,zero_add,id_eq])

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_VectorRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine Matrix

variable {α β γ : Type*}

def vectorAdd := (ratOp .add).zipWith 0 0

def vectorScaleBody : Realizes (prodCode ratCode ratCode) ratCode (fun p => p.1*p.2) :=
  ratOp .mul

def vectorScale := vectorScaleBody.mapCtx

def matrixAdd := vectorAdd.zipWith [] []

def matrixScale := vectorScale.mapCtx

def dot : Realizes (prodCode vectorCode vectorCode) ratCode dotValue :=
  ((ratOp .mul).zipWith 0 0).then sumRationals

def matVec : Realizes (prodCode matrixCode vectorCode) vectorCode matVecValue :=
  let swap := (second matrixCode vectorCode).both (first matrixCode vectorCode)
  let rowDot := ((second vectorCode vectorCode).both (first vectorCode vectorCode)).then dot
  swap.then rowDot.mapCtx

def quadratic : Realizes (prodCode vectorCode matrixCode) ratCode quadraticValue :=
  let v := first vectorCode matrixCode
  let m := second vectorCode matrixCode
  (v.both ((m.both v).then matVec)).then dot

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_MatrixStructureRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

def natLE : Realizes (prodCode natCode natCode) boolCode (fun p => decide (p.1≤p.2)) :=
  (((first natCode natCode).then natToRat).le ((second natCode natCode).then natToRat)).congr
    (by intro p;simp)

def natEq : Realizes (prodCode natCode natCode) boolCode (fun p => decide (p.1=p.2)) :=
  let rev := (second natCode natCode).both (first natCode natCode)
  (natLE.ite (rev.then natLE) (constant (prodCode natCode natCode) boolCode false)).congr
    (by intro p;by_cases h : p.1≤p.2 <;> by_cases k : p.2≤p.1 <;> by_cases e : p.1=p.2 <;> simp_all; omega)

variable {α : Type*}

def identityEntry : Realizes (prodCode natCode natCode) ratCode
    (fun p => if p.1=p.2 then 1 else 0) :=
  (natEq.ite (constant _ ratCode 1) (constant _ ratCode 0)).congr (by intro p;simp)

def identityMatrix : Realizes natCode matrixCode
    (fun n => (List.range n).map (fun i => (List.range n).map (fun j => if i=j then 1 else 0))) :=
  let ctx := prodCode natCode natCode
  let i := (first ctx natCode).then (second natCode natCode)
  let j := second ctx natCode
  let entry := (i.both j).then identityEntry
  (((identity natCode).both (identity natCode)).both (identity natCode)).then entry.matrixTabulate

def matrixMul : Realizes (prodCode matrixCode matrixCode) matrixCode matrixMulData :=
  let A := first matrixCode matrixCode
  let Bt := (second matrixCode matrixCode).then transposeMatrix
  let cols := first matrixCode vectorCode
  let row := second matrixCode vectorCode
  let rowResult := (row.both cols).then dot.mapCtx
  (Bt.both A).then rowResult.mapCtx

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_CoordinateRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

def natLT : Realizes (prodCode natCode natCode) boolCode (fun p => decide (p.1 < p.2)) :=
  ((((first natCode natCode).then natSucc).both (second natCode natCode)).then natLE).congr
    (by intro p;simp)

def Realizes.scaleMatrix {α : Type*} {ea : α → Word} {f : α → ℚ} {g : α → MatrixData}
    (r : Realizes ea ratCode f) (s : Realizes ea matrixCode g) :
    Realizes ea matrixCode (fun a => (g a).map (fun row => row.map (fun x => f a*x))) :=
  (r.both s).then matrixScale

def negateMatrix : Realizes matrixCode matrixCode
    (fun M => M.map (fun row => row.map (fun x => -x))) :=
  ((constant matrixCode ratCode (-1)).scaleMatrix (identity matrixCode)).congr (by intro M;simp)

def zeroMatrix : Realizes natCode matrixCode (fun n => matrixData (0 : Matrix (Fin n) (Fin n) ℚ)) :=
  ((constant natCode ratCode 0).scaleMatrix identityMatrix).congr (by
    intro n
    rw [identityMatrix_data,matrixScale_data,zero_smul])

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_RatFieldsRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.CurrentKS.Realization.poly_matrixView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine
open KS.W29.FixedSequential KS.W03.MachineCombinators

def ratDenBinary : Realizes ratCode binaryNatCode (fun q => q.den) :=
  (ratFields.then (second binaryNatCode KS.W01.encodeNat)).then unframeNat

def ratDenSize : Realizes ratCode natCode (fun q : ℚ => q.den.size) := ratDenBinary.then binarySize

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_PencilArrayRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

def accumMatrixRealizes : Realizes (prodCode matrixCode (prodCode ratCode matrixCode)) matrixCode accumMatrix :=
  let acc := first matrixCode (prodCode ratCode matrixCode)
  let new := (second matrixCode (prodCode ratCode matrixCode)).then matrixScale
  (acc.both new).then matrixAdd

def evalPencil : Realizes (prodCode pencilCode vectorCode) matrixCode evalPencilData :=
  let pencil := first pencilCode vectorCode
  let c := pencil.then (first matrixCode (listCode matrixCode))
  let bs := pencil.then (second matrixCode (listCode matrixCode))
  let y := second pencilCode vectorCode
  let pairs := (y.both bs).then ((identity (prodCode ratCode matrixCode)).zipWith 0 [])
  (c.both pairs).then accumMatrixRealizes.fold

def normalPencil : Realizes (prodCode pencilCode vectorCode) vectorCode normalData :=
  let c := (first pencilCode vectorCode).then (second matrixCode (listCode matrixCode))
  let v := second pencilCode vectorCode
  (v.both c).then quadratic.neg.mapCtx

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_RoundedStepRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine Matrix

def roundedUpdate : Realizes updateCode vectorCode roundedUpdateValue :=
  let pars := first stepParametersCode (prodCode vectorCode vectorCode)
  let step := pars.then (first ratCode ratCode)
  let mesh := pars.then (second ratCode ratCode)
  let vectors := second stepParametersCode (prodCode vectorCode vectorCode)
  let y := vectors.then (first vectorCode vectorCode)
  let a := vectors.then (second vectorCode vectorCode)
  let norm := a.then l1Rationals
  let scale := ((step.div norm).both a).then vectorScale
  let moved := (y.both scale).then ((ratOp .sub).zipWith 0 0)
  (mesh.both moved).then roundScalar.mapCtx

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_PencilCompileRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

def matrixSub : Realizes (prodCode matrixCode matrixCode) matrixCode matrixSubData :=
  ((first matrixCode matrixCode).both ((second matrixCode matrixCode).then negateMatrix)).then matrixAdd
def basisVector : Realizes (prodCode natCode natCode) vectorCode basisData :=
  ((second natCode natCode).both (first natCode natCode)).then identityEntry.tabulate

variable {α : Type*}

def Realizes.pencilFromEval {ea : α → Word} {f : α×List ℚ → MatrixData}
    (r : Realizes (prodCode ea vectorCode) matrixCode f) :
    Realizes (prodCode ea natCode) pencilCode (pencilFromEvalData f) :=
  let pc := prodCode ea natCode
  let a := first ea natCode
  let n := second ea natCode
  let zeros := ((constant pc ratCode 0).both n).then (replicateList ratCode)
  let c := (a.both zeros).then r
  let p := first pc natCode
  let idx := second pc natCode
  let ni := (p.then n).both idx
  let atBasis := ((p.then a).both (ni.then basisVector)).then r
  let one := (atBasis.both (p.then c)).then matrixSub
  c.both (((identity pc).both n).then one.tabulate)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ValueDataRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

def weightedSum : Realizes (prodCode natCode (prodCode vectorCode (listCode matrixCode))) matrixCode weightedSumData :=
  let n := first natCode (prodCode vectorCode (listCode matrixCode))
  let values := Realization.second natCode (prodCode vectorCode (listCode matrixCode))
  let pairs := values.then ((identity (prodCode ratCode matrixCode)).zipWith 0 [])
  ((n.then zeroMatrix).both pairs).then accumMatrixRealizes.fold

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ScheduleRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α : Type*} {ea : α → Word} {f g : α → ℚ}

def saEpsilon := saNu.div (saD.then natToRat)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_FaceChoiceRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

def vectorSub := (ratOp .sub).zipWith 0 0

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Normalization_Realization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
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

def outer : Realizes vectorCode matrixCode
    (fun xs : List ℚ => xs.map (fun q => xs.map (fun r => q*r))) :=
  let one := ((second vectorCode ratCode).both (first vectorCode ratCode)).then vectorScale
  ((identity vectorCode).both (identity vectorCode)).then one.mapCtx

end AlgorithmicThinTrees.Normalization.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_ArraySums
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Array sums. -/

section

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

def matrixSum : Realizes (prodCode natCode (listCode matrixCode)) matrixCode matrixSumData :=
  let n := first natCode (listCode matrixCode)
  let xs := second natCode (listCode matrixCode)
  let ones := ((constant _ ratCode 1).both (xs.then (lengthList matrixCode))).then (replicateList ratCode)
  (n.both (ones.both xs)).then weightedSum

variable {α β : Type*} {ea : α → Word} {eb : β → Word}

def Realizes.sumFin {n : α → ℕ} {f : (a : α) → Fin (n a) → ℚ}
    (r : Realizes (finFamilyCode ea n) ratCode (fun a => f a.1 a.2))
    (rn : Realizes ea natCode n) : Realizes ea ratCode (fun a => ∑i,f a i) :=
  ((r.tabulateFin rn).then sumRationals).congr (fun _ => List.sum_ofFn)
end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_UnaryArithmetic
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unary arithmetic. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

def natDivBinary : Realizes (prodCode natCode natCode) binaryNatCode (fun p => p.1/p.2) :=
  (((((first natCode natCode).then natToRat).div
    ((second natCode natCode).then natToRat)).then ratFloor).then ratNumBinary).congr
      (fun p => by
        simp only [Rat.num_intCast,Int.floor_div_natCast,Int.floor_natCast,
          ←Int.natCast_ediv,intPayload_natCast])

def natDiv : Realizes (prodCode natCode natCode) natCode (fun p => p.1/p.2) :=
  natDivBinary.then binaryToNat

def natMod : Realizes (prodCode natCode natCode) natCode (fun p => p.1%p.2) :=
  ((first natCode natCode).both
    (((second natCode natCode).both natDiv).then natMul)).then natSub |>.congr
      (fun p => by
        dsimp only
        have h := Nat.mod_add_div p.1 p.2
        omega)

variable {α : Type*} {ea : α → Word} {f g : α → ℕ}
def Realizes.ndiv (r : Realizes ea natCode f) (s : Realizes ea natCode g) :=
  (r.both s).then natDiv
def Realizes.nmod (r : Realizes ea natCode f) (s : Realizes ea natCode g) :=
  (r.both s).then natMod
def Realizes.neq (r : Realizes ea natCode f) (s : Realizes ea natCode g) :=
  (r.both s).then natEq
def Realizes.nlt (r : Realizes ea natCode f) (s : Realizes ea natCode g) :=
  (r.both s).then natLT

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_UnaryRoot
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unary root. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

def unaryRootStepProgram (d : ℕ) : Realizes rootCode rootCode (unaryRootStep d) :=
  let r := first natCode natCode
  let b := second natCode natCode
  let next := b.then natSucc
  (r.both (((next.then (AlgorithmicThinTrees.Normalization.Stack.unaryPow d)).both r).then natLE |>.ite next b)).congr (by
    intro a; simp [unaryRootStep])

def unaryRoot (d : ℕ) (hd : d≠0) : Realizes natCode natCode (Nat.nthRoot d) :=
  (((identity natCode).both ((identity natCode).both (constant natCode natCode 0))).then
    (unaryRootStepProgram d).iterate |>.then (second natCode natCode)).congr (by
      intro r
      change ((unaryRootStep d)^[r] (r,0)).2 = Nat.nthRoot d r
      rw [unaryRootStep_iterate_zero d hd r r,min_eq_right (unaryRoot_le d r hd)])
end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_GraphRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Graph realization. -/

section

namespace AlgorithmicThinTrees.GraphStack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.MetricTests.RationalStep
open scoped BigOperators

def incidence : Realizes edgeCode vectorCode
    (fun a => List.ofFn (qdiff (a.1.G.left a.2) (a.1.G.right a.2))) :=
  let n := edgeGraph.then numVertices
  ((((n.both edgeLeft).then basisVector).both ((n.both edgeRight).then basisVector)).then
    vectorSub).congr (by
      intro a
      change zipDefault (fun p : ℚ×ℚ => p.1-p.2) 0 0
        (basisData (a.1.n,(a.1.G.left a.2).val),
          basisData (a.1.n,(a.1.G.right a.2).val)) = _
      simp only [basis_data]
      rw [vectorSub_data]
      rfl)

def incidenceRows : Realizes graphCode matrixCode
    (fun a => matrixData (fun e => qdiff (a.G.left e) (a.G.right e))) :=
  incidence.tabulateFin numEdges

def laplacian : Realizes graphCode matrixCode (fun a => matrixData (qlap a.G)) :=
  let ones := ((constant graphCode ratCode 1).both numEdges).then (replicateList ratCode)
  let atoms := incidenceRows.then Normalization.Stack.outer.map
  (numVertices.both (ones.both atoms)).then weightedSum |>.congr (by
    intro a
    change weightedSumData (a.n,(List.replicate a.m (1:ℚ),
      (List.ofFn (fun e => List.ofFn (qdiff (a.G.left e) (a.G.right e)))).map _))=_
    rw [← List.ofFn_const (n:=a.m) (1:ℚ)]
    simp only [List.map_ofFn,Function.comp_def]
    change weightedSumData (a.n,(List.ofFn (fun _ : Fin a.m => (1:ℚ)),
      List.ofFn (fun e => matrixData (vecMulVec (qdiff (a.G.left e) (a.G.right e))
        (qdiff (a.G.left e) (a.G.right e))))))=_
    rw [weightedSum_data]
    simp only [one_smul,qlap])

def projection : Realizes natCode matrixCode (fun n => matrixData (qproject n)) :=
  let inv := (constant natCode ratCode 1).div natToRat
  ((identityMatrix.both (((identity natCode).both inv).then constantMatrix)).then
    matrixSub).congr (by
      intro n
      rw [identityMatrix_data,matrixSub_data]
      simp only [one_div]
      rfl)

def response : Realizes matrixObjectCode matrixCode (fun a => matrixData (qresponse a.2)) :=
  let P := matrixDim.then projection
  let A := matrixEntries
  let symm := (constant matrixObjectCode ratCode (1/2)).scaleMatrix
    ((A.both (A.then transposeMatrix)).then matrixAdd)
  ((P.both symm).then matrixMul).both P |>.then matrixMul |>.congr (by
    intro a
    rw [transpose_data]
    change matrixMulData (matrixMulData (matrixData (qproject a.1),
      matrixScaleData (1/2,matrixAddData (matrixData a.2,matrixData a.2.transpose))),
      matrixData (qproject a.1))=_
    unfold matrixAddData matrixScaleData
    rw [matrixAdd_data,matrixScale_data,matrixMul_data,matrixMul_data]
    rfl)

end AlgorithmicThinTrees.GraphStack

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_FiniteFamilies
attribute [-instance] _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite families. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {α β : Type*} {ea : α → Word} {eb : β → Word}
variable {I J : α → Type*} {n m : α → ℕ}

def indexedSumTest (e : (a : α) → I a ≃ Fin (n a)) (e' : (a : α) → J a ≃ Fin (m a))
    (rn : Realizes ea natCode n) :
    Realizes (indexedCode ea (sumEquiv e e')) boolCode
      (fun p => decide (p.2.isLeft=true)) :=
  ((indexedIndex (sumEquiv e e')).nlt ((indexedFirst (sumEquiv e e')).then rn)).congr (by
    rintro ⟨a,i|j⟩
    · change decide ((e a i).val<n a)=decide (true=true)
      simp [(e a i).isLt]
    · change decide (n a+(e' a j).val<n a)=decide (false=true)
      simp)

def Realizes.sumCases {e : (a : α) → I a ≃ Fin (n a)}
    {e' : (a : α) → J a ≃ Fin (m a)} {f : (Σ a,I a) → β} {g : (Σ a,J a) → β}
    (r : Realizes (indexedCode ea e) eb f) (s : Realizes (indexedCode ea e') eb g)
    (rn : Realizes ea natCode n) :
    Realizes (indexedCode ea (sumEquiv e e')) eb
      (fun p => p.2.elim (fun i => f ⟨p.1,i⟩) (fun j => g ⟨p.1,j⟩)) :=
  ((indexedSumTest e e' rn).dite
    (r.reindex (fun p : {p : Σ a,I a ⊕ J a // p.2.isLeft=true} =>
      indexedCode ea (sumEquiv e e') p.val) (sumLeft e e') (sumLeft_code e e'))
    ((indexedSumRight e e' rn).then s)).congr (by
      rintro ⟨a,i|j⟩ <;> simp [sumLeft,sumRight])

def splitProduct (e : (a : α) → I a ≃ Fin (n a)) (e' : (a : α) → J a ≃ Fin (m a))
    (rm : Realizes ea natCode m) :
    Realizes (indexedCode ea (prodEquiv e e'))
      (indexedCode (indexedCode ea e) (fun p : Σ a,I a => e' p.1))
      (fun p => ⟨⟨p.1,p.2.1⟩,p.2.2⟩) :=
  let a := indexedFirst (ea:=ea) (prodEquiv e e')
  let i := indexedIndex (ea:=ea) (prodEquiv e e')
  (((a.both (i.ndiv (a.then rm))).both (i.nmod (a.then rm)))).changeOutput
    (indexedCode (indexedCode ea e) (fun p : Σ a,I a => e' p.1))
    (fun p => ⟨⟨p.1,p.2.1⟩,p.2.2⟩) (by
      rintro ⟨a,i,j⟩
      have hj := (e' a j).isLt
      have hm : 0 < m a := by omega
      change prodCode (prodCode ea natCode) natCode
        ((a,((e' a j).val+m a*(e a i).val)/m a),
          ((e' a j).val+m a*(e a i).val)%m a)=
        prodCode (prodCode ea natCode) natCode ((a,(e a i).val),(e' a j).val)
      simp [Nat.add_mul_div_left _ _ hm,Nat.add_mod,Nat.div_eq_of_lt hj,Nat.mod_eq_of_lt hj])

def indexedProductLeft (e : (a : α) → I a ≃ Fin (n a))
    (e' : (a : α) → J a ≃ Fin (m a)) (rm : Realizes ea natCode m) :
    Realizes (indexedCode ea (prodEquiv e e')) (indexedCode ea e)
      (fun p => ⟨p.1,p.2.1⟩) :=
  (splitProduct e e' rm).then (indexedFirst (fun p : Σ a,I a => e' p.1))

def indexedProductRight (e : (a : α) → I a ≃ Fin (n a))
    (e' : (a : α) → J a ≃ Fin (m a)) (rm : Realizes ea natCode m) :
    Realizes (indexedCode ea (prodEquiv e e')) (indexedCode ea e')
      (fun p => ⟨p.1,p.2.2⟩) :=
  let s := splitProduct e e' rm
  let a := s.then (indexedFirst (fun p : Σ a,I a => e' p.1)) |>.then (indexedFirst e)
  let i := s.then (indexedIndex (fun p : Σ a,I a => e' p.1))
  (a.both i).changeOutput (indexedCode ea e') (fun p => ⟨p.1,p.2.2⟩) (fun _ => rfl)

def Realizes.finEq {n : α → ℕ} {f g : (a : α) → Fin (n a)}
    (r : Realizes ea natCode (fun a => (f a).val))
    (s : Realizes ea natCode (fun a => (g a).val)) :
    Realizes ea boolCode (fun a => decide (f a=g a)) :=
  (r.neq s).congr (by intro a;simp only [Fin.ext_iff])
end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_Parameters
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
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

variable {α : Type*} {ea : α → Word} {p : α → Point}
abbrev responsePoint := rawPoint.then GraphStack.response
abbrev lapPoint := pointGraph.then laplacian

def differenceVector {α : Type*} {ea : α → Word} {d : α → ℕ}
    (rn : Realizes ea natCode d) (i j : (a : α) → Fin (d a))
    (ri : Realizes ea natCode (fun a => (i a).val))
    (rj : Realizes ea natCode (fun a => (j a).val)) :
    Realizes ea vectorCode (fun a => List.ofFn (qdiff (i a) (j a))) :=
  ((((rn.both ri).then basisVector).both ((rn.both rj).then basisVector)).then vectorSub).congr (by
    intro a
    rw [basis_data,basis_data]
    exact vectorSub_data _ _)
end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_PointPrograms
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Point programs. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack
open scoped BigOperators
variable {α : Type*} {ea : α → Word} {a : α → Point}

abbrev tripleHead := indexedProductLeft (ea:=pointCode) vEquiv pairEquiv (pointN.nmul pointN)
abbrev tripleTail := indexedProductRight (ea:=pointCode) vEquiv pairEquiv (pointN.nmul pointN)
abbrev pairHead := indexedProductLeft (ea:=pointCode) vEquiv vEquiv pointN
abbrev pairTail := indexedProductRight (ea:=pointCode) vEquiv vEquiv pointN
abbrev tripleI := tripleHead.then (indexedIndex vEquiv)
abbrev tripleJ := tripleTail.then pairHead |>.then (indexedIndex vEquiv)
abbrev tripleK := tripleTail.then pairTail |>.then (indexedIndex vEquiv)

def tripleCoordinate : Realizes tripleCode ratCode (fun p => p.1.v (mulIndex p.2)) :=
  let n := triplePoint.then pointN
  coordinate triplePoint (fun p => mulIndex p.2)
    ((n.nmul n).nadd ((tripleK.nadd (n.nmul tripleJ)).nadd ((n.nmul n).nmul tripleI)))

def tripleDistinct : Realizes tripleCode boolCode
    (fun p => decide (p.2.1≠p.2.2.1 ∧ p.2.2.1≠p.2.2.2 ∧ p.2.1≠p.2.2.2)) :=
  (tripleI.finEq tripleJ).not.and ((tripleJ.finEq tripleK).not.and (tripleI.finEq tripleK).not)

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_BlockAssembly
attribute [-instance] _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Block assembly. -/

section

namespace CurrentKS.Realization
open CleanRoutine Matrix KS.W23

def stitchedMatrixEntry :=
  let block := ((stI.nmod stK).both stMatrices).then (getD matrixCode [])
  (block.both ((stI.ndiv stK).both (stJ.ndiv stK))).then matrixEntry

def stitchProgramEntry : Realizes stitchCode ratCode stitchEntry :=
  let zero := constant stitchCode ratCode 0
  let diag := ((stI.nsub stCut).both stScalars).then (getD ratCode 0)
  ((stI.nlt stCut).ite
    ((stJ.nlt stCut).ite (((stI.nmod stK).neq (stJ.nmod stK)).ite stitchedMatrixEntry zero) zero)
    ((stI.neq stJ).ite diag zero)).congr (by intro p;simp [stitchEntry])

def stitchProgram : Realizes blocksCode matrixCode stitchData :=
  let tail := second natCode (prodCode (listCode matrixCode) vectorCode)
  let n := first natCode (prodCode (listCode matrixCode) vectorCode)
  let k := tail.then (first (listCode matrixCode) vectorCode) |>.then (lengthList matrixCode)
  let l := tail.then (second (listCode matrixCode) vectorCode) |>.then (lengthList ratCode)
  let dim := (n.nmul k).nadd l
  (((identity blocksCode).both dim).both dim).then stitchProgramEntry.matrixTabulate
end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_MatrixConstraintRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix constraint realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators
variable {α : Type*} {ea : α → Word} {I : α → Type*} [∀a,Fintype (I a)]
def Realizes.sumIndexedMatrices {n d : α → ℕ} {e : (a : α) → I a ≃ Fin (n a)}
    {A : (a : α) → I a → Matrix (Fin (d a)) (Fin (d a)) ℚ}
    (r : Realizes (indexedCode ea e) matrixCode (fun a => matrixData (A a.1 a.2)))
    (rn : Realizes ea natCode n) (rd : Realizes ea natCode d) :
    Realizes ea matrixCode (fun a => matrixData (∑i,A a i)) :=
  ((rd.both (r.tabulateIndexed rn)).then matrixSum).congr (by
    intro a
    rw [matrixSum_data]
    exact congrArg matrixData ((e a).symm.sum_comp (A a)))
end CurrentKS.Realization

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree RationalForms
open AlgorithmicThinTrees.GraphStack
open scoped BigOperators

namespace Stack

def triangleMatrixProgram : Realizes tripleCode matrixCode (fun p => matrixData (triangleAt p.2)) :=
  let n := triplePoint.then pointN
  let ij := (differenceVector n (fun p => p.2.1) (fun p => p.2.2.1) tripleI tripleJ).then
    Normalization.Stack.outer
  let jk := (differenceVector n (fun p => p.2.2.1) (fun p => p.2.2.2) tripleJ tripleK).then
    Normalization.Stack.outer
  let ik := (differenceVector n (fun p => p.2.1) (fun p => p.2.2.2) tripleI tripleK).then
    Normalization.Stack.outer
  (((ij.both jk).then matrixAdd).both ik).then matrixSub |>.congr (by
    intro a
    dsimp only [KS.W13.ExpressionMachine.BinaryOp.eval]
    rw [Normalization.Stack.outer_data,Normalization.Stack.outer_data,Normalization.Stack.outer_data,
      matrixAdd_data,matrixSub_data]
    rfl)

def weightedTriangleProgram : Realizes tripleCode matrixCode (fun a => matrixData (weightedTriangle a.1 a.2)) :=
  let val := tripleCoordinate.scaleMatrix triangleMatrixProgram
  (tripleDistinct.ite val (triplePoint.then pointN |>.then zeroMatrix)).congr (by
    intro a
    simp only [weightedTriangle,decide_eq_true_eq]
    split_ifs
    · exact matrixScale_data _ _
    · rfl)

def triangleSum : Realizes pointCode matrixCode (fun a =>
    matrixData (∑t : DistinctTriple a.p.graph.n,a.v (mulIndex t.val) • qtriangle t)) :=
  (weightedTriangleProgram.sumIndexedMatrices (A:=weightedTriangle) (pointN.nmul (pointN.nmul pointN)) pointN).congr (by
    intro a
    rw [weightedTriangle_sum])

def lowerMatrix : Realizes pointCode matrixCode (fun a => matrixData ((lowerForm a.p.graph.G).map (Affine.rat a.v))) :=
  ((responsePoint.both lapPoint).then matrixSub).congr (by
    intro a
    rw [matrixSub_data]
    congr 1
    ext i j
    simp [lowerForm,rat_matrixForm,Matrix.sub_apply])

def upperMatrix : Realizes pointCode matrixCode (fun a => matrixData ((upperForm a.p.graph.G).map (Affine.rat a.v))) :=
  (((((constant pointCode ratCode 3).scaleMatrix lapPoint).both responsePoint).then matrixSub).both triangleSum).then
    matrixSub |>.congr (by
      intro a
      rw [matrixScale_data,matrixSub_data,matrixSub_data]
      congr 1
      ext i j
      simp only [Matrix.map_apply,upperForm,Affine.rat_sub,Affine.rat_cst,Affine.rat_sum,
        Affine.rat_smul,Affine.rat_coord,rat_matrixForm,Matrix.sub_apply,Matrix.smul_apply,
        smul_eq_mul,Matrix.sum_apply]
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      ring)

def edgeMatrix : Realizes (indexedCode pointCode eEquiv) matrixCode (fun a =>
    matrixData ((matrixBlocks a.1.p.graph.G a.1.p.s a.1.p.u (.inr a.2)).map (Affine.rat a.1.v))) :=
  let p := indexedFirst (ea:=pointCode) eEquiv
  let e := indexedIndex (ea:=pointCode) eEquiv
  let isActive := (constant _ ratCode 0).lt (storedU p (fun a => a.2) e)
  let atom := ((graphEdge p (fun a => a.2) e).then GraphStack.incidence).then Normalization.Stack.outer
  let factor := ((constant _ ratCode 6).mul (p.then pointS)).mul (edgeCoord 0 p (fun a => a.2) e)
  let response := ((p.then responsePoint).both (factor.scaleMatrix atom)).then matrixSub
  (isActive.ite response (p.then pointN |>.then zeroMatrix)).congr (by
    intro a
    simp only [decide_eq_true_eq,matrixBlocks]
    split_ifs
    · rw [Normalization.Stack.outer_data,matrixScale_data,matrixSub_data]
      congr 1
      ext i j
      simp [edgeForm,rat_matrixForm,Matrix.sub_apply,smul_eq_mul,Matrix.vecMulVec_apply]
      ring
    · congr 1
      ext i j
      simp)

def specialMatrix : Realizes (indexedCode pointCode (fun _ : Point => Equiv.refl (Fin 2))) matrixCode
    (fun a => matrixData ((matrixBlocks a.1.p.graph.G a.1.p.s a.1.p.u (.inl a.2)).map (Affine.rat a.1.v))) :=
  let p := indexedFirst (ea:=pointCode) (fun _ : Point => Equiv.refl (Fin 2))
  let i := indexedIndex (ea:=pointCode) (fun _ : Point => Equiv.refl (Fin 2))
  ((i.finEq (constant _ natCode (0 : Fin 2).val)).ite (p.then lowerMatrix) (p.then upperMatrix)).congr (by
    intro a
    change (if decide (a.2 = 0) = true then
      matrixData ((lowerForm a.1.p.graph.G).map (Affine.rat a.1.v)) else
      matrixData ((upperForm a.1.p.graph.G).map (Affine.rat a.1.v))) =
      matrixData ((if a.2 = 0 then lowerForm a.1.p.graph.G else
        upperForm a.1.p.graph.G).map (Affine.rat a.1.v))
    simp only [decide_eq_true_eq]
    split_ifs <;> rfl)

def matrixConstraints : Realizes (indexedCode pointCode matrixBlockEquiv) matrixCode
    (fun a => matrixData ((matrixBlocks a.1.p.graph.G a.1.p.s a.1.p.u a.2).map (Affine.rat a.1.v))) :=
  (specialMatrix.sumCases edgeMatrix (constant pointCode natCode 2)).congr (by
    rintro ⟨a,b|e⟩ <;> rfl)
end Stack
end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_ScalarConstraintRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right
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

def scalarTriple : Realizes tripleCode ratCode (fun p => scalarValue p.1 (.inl p.2)) :=
  (tripleDistinct.ite tripleCoordinate (constant tripleCode ratCode 0)).congr (by
    intro p
    simp only [decide_eq_true_eq,scalarValue,scalarForms]
    split_ifs <;> simp)
abbrev esP := (indexedProductLeft (ea:=pointCode) (fun _ : Point => Equiv.refl (Fin 7))
  eEquiv pointM).then (indexedIndex (fun _ : Point => Equiv.refl (Fin 7)))
abbrev esEdge := indexedProductRight (ea:=pointCode) (fun _ : Point => Equiv.refl (Fin 7)) eEquiv pointM
abbrev esE := esEdge.then (indexedIndex eEquiv)

def esY := edgeCoord 0 esPoint (fun p => p.2.2) esE
def esZ := edgeCoord 1 esPoint (fun p => p.2.2) esE
def esX := edgeCoord 2 esPoint (fun p => p.2.2) esE
def esU := storedU esPoint (fun p => p.2.2) esE

def esActive := (constant edgeScalarCode ratCode 0).lt esU

def esCapacityRate : Realizes edgeScalarCode ratCode (fun a =>
    if 0<a.1.p.u a.2.2 then a.1.p.κ+a.1.p.u a.2.2-a.1.v (edgeIndex 1 a.2.2)+
      a.1.p.t*(5*a.1.v (edgeIndex 0 a.2.2)-4) else 0) :=
  let c (q : ℚ) := constant edgeScalarCode ratCode q
  (esActive.ite (((esK.add esU).sub esZ).add (esT.mul (((c 5).mul esY).sub (c 4))))
    (c 0)).congr (by intro a;simp)

def esCapacity : Realizes edgeScalarCode ratCode (fun a =>
    if 0<a.1.p.u a.2.2 then a.1.v (edgeIndex 1 a.2.2) else a.1.p.κ) :=
  (esActive.ite esZ esK).congr (by intro a;simp)

def scalarEdge : Realizes edgeScalarCode ratCode
    (fun a => scalarValue a.1 (.inr (.inl a.2))) :=
  (select7 esP esY ((constant _ ratCode 1).sub esY) esZ
    ((esK.add (constant _ ratCode 1)).sub esZ) esCapacityRate esX (esCapacity.sub esX)).congr (by
      rintro ⟨a,p,e⟩
      change ![a.v (edgeIndex 0 e),1-a.v (edgeIndex 0 e),a.v (edgeIndex 1 e),
        a.p.κ+1-a.v (edgeIndex 1 e),
        if 0<a.p.u e then a.p.κ+a.p.u e-a.v (edgeIndex 1 e)+a.p.t*(5*a.v (edgeIndex 0 e)-4) else 0,
        a.v (edgeIndex 2 e),(if 0<a.p.u e then a.v (edgeIndex 1 e) else a.p.κ)-a.v (edgeIndex 2 e)] p
          =scalarValue a (.inr (.inl (p,e)))
      fin_cases p <;> by_cases hu : 0<a.p.u e <;> simp [scalarValue,scalarForms,capacityForm,hu])
abbrev reR := (indexedProductLeft (ea:=pointCode) vEquiv eEquiv pointM).then (indexedIndex vEquiv)
abbrev reE := (indexedProductRight (ea:=pointCode) vEquiv eEquiv pointM).then (indexedIndex eEquiv)

def reA := flowCoord 0 rePoint (fun a => a.2.1) (fun a => a.2.2) reR reE
def reB := flowCoord 1 rePoint (fun a => a.2.1) (fun a => a.2.2) reR reE
def reX := edgeCoord 2 rePoint (fun a => a.2.2) reE
abbrev fsRE := indexedProductRight (ea:=pointCode) (fun _ : Point => Equiv.refl (Fin 3)) rootEdgeEquiv
  (pointN.nmul pointM)
abbrev fsP := (indexedProductLeft (ea:=pointCode) (fun _ : Point => Equiv.refl (Fin 3)) rootEdgeEquiv
  (pointN.nmul pointM)).then (indexedIndex (fun _ : Point => Equiv.refl (Fin 3)))

def scalarFlow : Realizes flowScalarCode ratCode
    (fun a => scalarValue a.1 (.inr (.inr (.inl a.2)))) :=
  (select3 fsP (fsRE.then reA) (fsRE.then reB)
    (((fsRE.then reA).add (fsRE.then reB)).sub (fsRE.then reX))).congr (by
      rintro ⟨a,p,r,e⟩
      change ![a.v (flowIndex 0 r e),a.v (flowIndex 1 r e),
        a.v (flowIndex 0 r e)+a.v (flowIndex 1 r e)-a.v (edgeIndex 2 e)] p = _
      fin_cases p <;> simp [scalarValue,scalarForms])
abbrev bsR := pairHead.then (indexedIndex vEquiv)
abbrev bsV := pairTail.then (indexedIndex vEquiv)
abbrev beR := beBudget.then bsR
abbrev beV := beBudget.then bsV
def beA := flowCoord 0 bePoint (fun a => a.1.2.1) (fun a => a.2) beR beE
def beB := flowCoord 1 bePoint (fun a => a.1.2.1) (fun a => a.2) beR beE

def budgetEdge : Realizes budgetEdgeCode ratCode (fun a =>
    (if a.1.1.p.graph.G.left a.2=a.1.2.2 then a.1.1.v (flowIndex 0 a.1.2.1 a.2) else 0)+
    (if a.1.1.p.graph.G.right a.2=a.1.2.2 then a.1.1.v (flowIndex 1 a.1.2.1 a.2) else 0)) :=
  ((((beGraphEdge.then GraphStack.edgeLeft).finEq beV).ite beA (constant _ ratCode 0)).add
    (((beGraphEdge.then GraphStack.edgeRight).finEq beV).ite beB (constant _ ratCode 0))).congr
      (by
        intro a
        change ((if decide (a.1.1.p.graph.G.left a.2 = a.1.2.2) = true then
          a.1.1.v (flowIndex 0 a.1.2.1 a.2) else 0) +
          (if decide (a.1.1.p.graph.G.right a.2 = a.1.2.2) = true then
          a.1.1.v (flowIndex 1 a.1.2.1 a.2) else 0)) = _
        simp only [decide_eq_true_eq])

def budgetIncoming := budgetEdge.sumFin (n:=fun a : Σ b : Point,Fin b.p.graph.n × Fin b.p.graph.n => a.1.p.graph.m)
  (f:=fun a e => (if a.1.p.graph.G.left e=a.2.2 then a.1.v (flowIndex 0 a.2.1 e) else 0)+
    (if a.1.p.graph.G.right e=a.2.2 then a.1.v (flowIndex 1 a.2.1 e) else 0)) (bsPoint.then pointM)

def scalarBudget : Realizes budgetCode ratCode
    (fun a => scalarValue a.1 (.inr (.inr (.inr (.inl a.2))))) :=
  ((((bsV.finEq bsR).ite (bsPoint.then pointE) (bsPoint.then pointQ)).sub budgetIncoming)).congr (by
    rintro ⟨a,r,v⟩
    simp only [scalarValue,scalarForms,Affine.rat_sub,Affine.rat_cst,Affine.rat_sum,Affine.rat_add,
      decide_eq_true_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> simp)
def edgeTotal := (edgeCoord 2 xePoint (fun a => a.2) xeE).sumFin (n:=fun a : Point => a.p.graph.m)
  (f:=fun a e => a.v (edgeIndex 2 e)) pointM

def scalarTotalBase : Realizes pointCode ratCode (fun a => scalarValue a (.inr (.inr (.inr (.inr 0))))) :=
  (edgeTotal.sub ((pointQ.mul ((pointN.then natToRat).sub (constant _ ratCode 1))).sub pointE)).congr (by
    intro a
    simp only [scalarValue,scalarForms,Affine.rat_sub,Affine.rat_cst,Affine.rat_sum,Affine.rat_coord])

def scalarTotal : Realizes (indexedCode pointCode (fun _ : Point => Equiv.refl (Fin 1))) ratCode
    (fun a => scalarValue a.1 (.inr (.inr (.inr (.inr a.2))))) :=
  ((indexedFirst (fun _ : Point => Equiv.refl (Fin 1))).then scalarTotalBase).congr (fun _ => rfl)

def scalarConstraints : Realizes scalarCode ratCode (fun a => scalarValue a.1 a.2) :=
  (scalarTriple.sumCases (scalarEdge.sumCases (scalarFlow.sumCases
    (scalarBudget.sumCases scalarTotal (pointN.nmul pointN))
      ((constant _ natCode 3).nmul (pointN.nmul pointM)))
      ((constant _ natCode 7).nmul pointM)) (pointN.nmul (pointN.nmul pointN))).congr (by
        rintro ⟨a,b⟩
        rcases b with t | b
        · rfl
        rcases b with e | b
        · rfl
        rcases b with f | b
        · rfl
        rcases b with v | b <;> rfl)

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_Realization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
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

def affinePoint : Realizes pointCode matrixCode (fun a =>
    matrixData ((affineMatrix a.p.graph.G a.p.s a.p.κ a.p.t a.p.q a.p.ε a.p.u).map (Affine.rat a.v))) :=
  ((pointN.both ((matrixConstraints.tabulateIndexed matrixCount).both
    (scalarConstraints.tabulateIndexed scalarCount))).then stitchProgram).congr (by
      intro a
      have h := stitch_data (n:=a.p.graph.n) (matrixBlockEquiv a) (scalarEquiv a)
        (fun b => (matrixBlocks a.p.graph.G a.p.s a.p.u b).map (Affine.rat a.v)) (scalarValue a)
      rw [rowIndex_blocks] at h
      exact h.trans (congrArg matrixData (affineMatrix_rat a)).symm)

def pencilEval := pointParser.then affinePoint

def buildPencil : Realizes paramsCode pencilCode (fun p => pencilData p.pencil) :=
  (((identity paramsCode).both paramsDim).then pencilEval.pencilFromEval).congr (by
    intro p
    apply pencilFromEval_data
    exact pencilEval_data p)
end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_SearchRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
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

abbrev graphSizeProgram := ((numVertices.then natToRat).add (numEdges.then natToRat)).add
  (constant graphCode ratCode 2)
def graphRadius : Realizes graphCode ratCode (fun G => radiusQ G.n G.m) :=
  ((constant graphCode ratCode 1).div (graphSizeProgram.pow 50)).congr (by
    intro G; simp only [radiusQ,_root_.zpow_neg,one_div];rfl)

def graphBound : Realizes graphCode ratCode (fun G => boundQ G.n G.m) :=
  ((constant graphCode ratCode 6).mul graphSizeProgram).mul
    ((graphDim.then natToRat).add (constant graphCode ratCode 1))

def initializeSearch : Realizes paramsCode searchStateCode Params.searchState :=
  (buildPencil.both
    (((paramsGraph.then graphRadius).both (paramsGraph.then graphBound)).both
      (paramsGraph.then graphZeros))).changeOutput searchStateCode Params.searchState (fun _ => rfl)
end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Realization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
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

abbrev graphBaseline : Realizes graphCode ratCode (fun G => baselineQ G.m) :=
  (constant graphCode ratCode 1).div ((numEdges.then natToRat).add (constant graphCode ratCode 1))

abbrev graphStep : Realizes graphCode ratCode (fun G => stepQ G.m) :=
  graphBaseline.div (constant graphCode ratCode 32)

def graphError : Realizes graphCode ratCode (fun G => errorQ G.n G.m) :=
  ((constant graphCode ratCode 1).div (graphSizeProgram.pow 10)).congr (by
    intro G; simp only [errorQ,_root_.zpow_neg,one_div];rfl)

def gainProgram : Realizes natCode ratCode gain :=
  (constant natCode ratCode 1).div ((unaryRoot 8 (by decide)).then natToRat)

def clockProgram : Realizes (prodCode natCode natCode) natCode
    (fun p => scheduleLength p.1 p.2) :=
  ((constant (prodCode natCode natCode) natCode 32).nmul
    ((first natCode natCode).then natSucc)).nmul
      ((second natCode natCode).then (unaryRoot 16 (by decide)))
abbrev loopStep := loopGraph.then graphStep
abbrev loopBase := loopGraph.then graphBaseline
abbrev loopGain := loopCount.then gainProgram
abbrev loopTarget : Realizes loopCode ratCode (fun a => target a.graph.m a.count a.state.quality (gain a.count)) :=
  (loopQuality.sub ((loopGain.mul (loopCount.then natToRat)).mul loopStep)).sub
    ((constant loopCode ratCode 2).mul loopStep)

def loopParams : Realizes loopCode paramsCode Loop.params :=
  (loopGraph.both
    ((loopScale.cons (loopBase.cons (loopStep.cons (loopTarget.cons
      ((loopGraph.then graphError).then (singleton ratCode)))))).both loopCapacity)).changeOutput
        paramsCode Loop.params (fun _ => rfl)

def initializeLoop : Realizes extractionInputCode loopCode (fun p => ⟨p.1,p.2,initial p.1.G p.2⟩) :=
  (extractionGraph.both (extractionCount.both
    ((constant extractionInputCode ratCode (1/2)).both
      ((extractionCount.then natToRat).both
        ((extractionGraph.then laplacian).both
          (((constant extractionInputCode ratCode 1).both (extractionGraph.then numEdges)).then
            (replicateList ratCode))))))).changeOutput loopCode (fun p => ⟨p.1,p.2,initial p.1.G p.2⟩)
              (by intro p; simp only [loopCode,Loop.data,initial,List.ofFn_const])

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end


