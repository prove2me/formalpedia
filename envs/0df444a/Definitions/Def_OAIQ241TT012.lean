-- Prove2me | Definitions.Def_OAIQ241TT012
-- name    : OAIQ241TT012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:05:34.69936+00:00
-- url     : https://prove2.me/theorems/5daf1cf3-674c-4a2c-b3d4-4476d5382a5a
-- title:
--   Definitions bundle OAIQ241TT012 of the split of OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 86 declarations of OpenAI's Lean: 6 definitions and 80 theorems. The definitions and types are `OAI.CurrentKS.Realization.ratCeil`, `OAI.CurrentKS.Realization.saSigma`, `OAI.CurrentKS.Realization.searchFuelRealizes`, `OAI.CurrentKS.Realization.searchInit`, `OAI.CurrentKS.Realization.searchMeshRealizes`, `OAI.CurrentKS.Realization.searchStepRealizes`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `MatrixSigning_Arithmetic_ComplexScalarNodes`, `MatrixSigning_Arithmetic_RationalSignClassifier`, `MatrixSigning_Arithmetic_SparseScalarNodes`, `MatrixSigning_Arithmetic_ZeroPaddedRow`, `MatrixSigning_Complexity_ComplexScalarCosts`, `MatrixSigning_Complexity_SchurCellCost`, `MatrixSigning_Complexity_TerminalWitnessCost`, `MatrixSigning_Encoding_FramedArrayReplacement`, `MatrixSigning_Machines_ControllerRuntime`, `MatrixSigning_Machines_ControllerTerminalBound`, `MatrixSigning_Machines_SchurCellMachine`, `MatrixSigning_Machines_SchurColumnLoop`, `MatrixSigning_Machines_SchurEntryMachine`, `MatrixSigning_Machines_SchurOperands`, `MatrixSigning_Machines_SchurReadStage`, `MatrixSigning_Machines_SchurRowLoop`, `MatrixSigning_Machines_SchurTableCorrectness`, `MatrixSigning_Machines_TerminalReadStage`, `MatrixSigning_Machines_TerminalSparseAssembly`, `MatrixSigning_Machines_TerminalVectorReplace`, `MatrixSigning_Matrices_PivotControllerBody`, `MatrixSigning_Matrices_PivotControllerLoop`, `MatrixSigning_Matrices_PivotDecisionMachine`, `MatrixSigning_Matrices_PivotDecisionPorts`, `MatrixSigning_Matrices_PivotReachableBounds`, `MatrixSigning_Matrices_PivotReplayLoop`, `MatrixSigning_Matrices_PivotRowBody`, `MatrixSigning_Matrices_PivotRowClassify`, `MatrixSigning_Matrices_PivotRowFinish`, `MatrixSigning_Matrices_PivotRowInitialize`, `MatrixSigning_Matrices_PivotRowLoop`, `MatrixSigning_Matrices_PivotRowRead`, `MatrixSigning_Matrices_PivotTerminalMachine`, `MatrixSigning_Optimization_PivotDescentBounds`, `MatrixSigning_Optimization_PivotDescentMachine`, `MatrixSigning_Optimization_PivotWitnessMachine`, `MatrixSigning_Optimization_StoredWitnessLift`, `MatrixSigning_Optimization_TerminalWitnessMachine`, `MatrixSigning_Potential_SchurLoopState`, `MatrixSigning_Realization_RatFieldsRealization`, `MatrixSigning_Realization_ScheduleRealization`, `MatrixSigning_Realization_SearchRealization`.
--
--   **Imports.** It imports the bundles `OAIQ241TT010` and `OAIQ241TT011` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ241TT014`.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ241TT010
import Definitions.Def_OAIQ241TT011

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

theorem mulNode_spec (a b dest : Fin 28) (ha : 16 ≤ a.val) (hb : 16 ≤ b.val)
    (hd : 16 ≤ dest.val) (before : Registers) (hclear : CoreEmpty before)
    (q r : ℚ) (hq : before a = KS.W01.encodeRat q) (hr : before b = KS.W01.encodeRat r)
    (hempty : before dest = []) :
    RunSpec (mulNode a b dest ha hb) before
      (Function.update before dest (KS.W01.encodeRat (q * r))) (mulNodeTicks q r) := by
  have hp := pair_spec a b ha hb before hclear
  rw [hq,hr] at hp
  exact (hp.compose (scalar_multiplication_spec before hclear q r)).compose
    (store_spec before hclear dest hd hempty _)

theorem addNode_spec (a b dest : Fin 28) (ha : 16 ≤ a.val) (hb : 16 ≤ b.val)
    (hd : 16 ≤ dest.val) (before : Registers) (hclear : CoreEmpty before)
    (q r : ℚ) (hq : before a = KS.W01.encodeRat q) (hr : before b = KS.W01.encodeRat r)
    (hempty : before dest = []) :
    RunSpec (addNode a b dest ha hb) before
      (Function.update before dest (KS.W01.encodeRat (q + r))) (addNodeTicks q r) := by
  have hp := pair_spec a b ha hb before hclear
  rw [hq,hr] at hp
  exact (hp.compose (scalar_addition_spec before hclear q r)).compose
    (store_spec before hclear dest hd hempty _)

end KS.W15.ComplexMachine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalSignClassifier
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_ratFields
attribute [-simp] _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W01.sumBudget_cons _root_.OAI.KS.W12.FixedDot.machine_inputStack _root_.OAI.KS.W12.FixedDot.machine_outputStack _root_.OAI.KS.W12.FixedDot.machine_stackCount _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W15.RationalMultiply.machine_inputStack _root_.OAI.KS.W15.RationalMultiply.machine_outputStack _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W19.FixedRun.pack_on_port
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

theorem classified_length (q : ℚ) (j : Fin 13) :
    (classifiedCanonical q j).length ≤ KS.W01.ratLength q + readTicks q := by
  let bits := List.replicate (readTicks q) false
  have hr := read_spec q bits (by simp [bits])
  have hg := readProgram.toMachine.run_stack_length_le
    ⟨some readProgram.initial, SingleRationalParser.inputState (KS.W01.encodeRat q)⟩ bits j
  rw [hr] at hg
  have hi : (SingleRationalParser.inputState (KS.W01.encodeRat q) j).length ≤ KS.W01.ratLength q := by
    fin_cases j <;> simp [SingleRationalParser.inputState, KS.W01.ratLength]
  simpa only [bits, List.length_replicate] using hg.trans (Nat.add_le_add_right hi _)

theorem canonical_spec (q : ℚ) :
    RunSpec program (SingleRationalParser.inputState (KS.W01.encodeRat q)) (outputState q)
      (256 * (KS.W01.ratLength q + 1)) := by
  have h := (read_spec q).compose (clearList_spec 9 scratchPorts (classifiedCanonical q))
  rw [cleared_classified] at h
  apply h.mono
  have hb := clearListTicks_le scratchPorts (classifiedCanonical q)
    (KS.W01.ratLength q + readTicks q) (classified_length q)
  change clearListTicks scratchPorts (classifiedCanonical q) ≤
    12 * (KS.W01.ratLength q + readTicks q + 1) + 1 at hb
  unfold readTicks at hb ⊢
  omega

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

theorem negNode_spec (a dest : Fin 28) (ha : 16 ≤ a.val) (hd : 16 ≤ dest.val)
    (before : Registers) (hclear : CoreEmpty before) (q : ℚ)
    (hq : before a = encodeRat q) (hempty : before dest = []) :
    RunSpec (negNode a dest ha) before
      (Function.update before dest (encodeRat (-q))) (negNodeTicks q) := by
  have hc := copy_spec a (0 : Fin 28) 1 (stored_ne_core a ha 0) (stored_ne_core a ha 1)
    (by decide) before (hclear 0) (hclear 1)
  rw [hq] at hc
  have hp : RunSpec (literalProgram (0 : Fin 28) negativeOneWire)
      (Function.update before 0 (encodeRat q))
      (Function.update before 0 (encodeRat (-1) ++ encodeRat q)) 6 := by
    have h := literal_spec (0 : Fin 28) negativeOneWire (Function.update before 0 (encodeRat q))
    have he : negativeOneWire.length + 1 = 6 := rfl
    rw [he] at h
    simpa only [Function.update_self,Function.update_idem,negativeOneWire_eq] using h
  have hm : RunSpec mulProgram (Function.update before 0 (encodeRat (-1) ++ encodeRat q))
      (Function.update before 10 (encodeRat (-q))) (RationalMultiply.totalTicks (-1) q) := by
    simpa only [neg_one_mul] using scalar_multiplication_spec before hclear (-1) q
  exact ((hc.compose hp).compose hm).compose (store_spec before hclear dest hd hempty _)

end KS.W15.ComplexMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_SparseScalarNodes
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_ratFields
attribute [-simp] _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.SparseScalarNodes
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W15.ComplexMachine

theorem scalar_division_spec (before : Registers) (hclear : CoreEmpty before) (q r : ℚ) :
    RunSpec divProgram (Function.update before 0 (KS.W01.encodeRat q ++ KS.W01.encodeRat r))
      (Function.update before 10 (KS.W01.encodeRat (q/r))) (divTicks q r) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ divPorts _ _ _ _ _
    (KS.W30.RationalDivision.program_spec q r)
  · intro i; fin_cases i <;> simp [divPorts,KS.W30.RationalDivision.inputState,
      KS.W30.RationalDivision.inputBits,Function.update,coreEmpty_apply before hclear] <;> rfl
  · intro i; fin_cases i <;> simp [divPorts,KS.W30.RationalDivision.outputState,
      Function.update,coreEmpty_apply before hclear] <;> rfl
  · intro j hj
    have h0 : j ≠ 0 := hj 0
    have h10 : j ≠ 10 := hj 10
    simp [Function.update,h0,h10]

theorem divNode_spec (a b dest : Fin 28) (ha : 16 ≤ a.val) (hb : 16 ≤ b.val)
    (hd : 16 ≤ dest.val) (before : Registers) (hclear : CoreEmpty before)
    (q r : ℚ) (hq : before a = KS.W01.encodeRat q) (hr : before b = KS.W01.encodeRat r)
    (hempty : before dest = []) :
    RunSpec (divNode a b dest ha hb) before
      (Function.update before dest (KS.W01.encodeRat (q/r))) (divNodeTicks q r) := by
  have hp := pair_spec a b ha hb before hclear
  rw [hq,hr] at hp
  exact (hp.compose (scalar_division_spec before hclear q r)).compose
    (store_spec before hclear dest hd hempty _)

theorem coefficient_spec (s : Registers) (a b : ℚ) (hc : CoreEmpty s)
    (ha : s 16 = KS.W01.encodeRat a) (hb : s 17 = KS.W01.encodeRat b)
    (h18 : s 18 = []) (h19 : s 19 = []) (h20 : s 20 = []) (h21 : s 21 = [])
    (h24 : s 24 = []) (h25 : s 25 = []) :
    RunSpec program s (after s a b) (ticks a b) := by
  let s1 := put s 20 1
  let s2 := put s1 21 2
  let s3 := put s2 18 (a+1)
  let s4 := put s3 19 (2*b)
  let s5 := put s4 24 (-(a+1))
  have h1 : RunSpec (KS.W15.WireProgram.literalProgram 20 (KS.W01.encodeRat 1)) s s1
      ((KS.W01.encodeRat 1).length+1) := by
    simpa [s1,put,h20] using KS.W15.WireProgram.literal_spec (20 : Fin 28) (KS.W01.encodeRat 1) s
  have h2 : RunSpec (KS.W15.WireProgram.literalProgram 21 (KS.W01.encodeRat 2)) s1 s2
      ((KS.W01.encodeRat 2).length+1) := by
    simpa [s2,s1,put,h21] using KS.W15.WireProgram.literal_spec (21 : Fin 28) (KS.W01.encodeRat 2) s1
  have hc1 : CoreEmpty s1 := coreEmpty_update s hc 20 (by decide) _
  have hc2 : CoreEmpty s2 := coreEmpty_update s1 hc1 21 (by decide) _
  have h3 : RunSpec (addNode 16 20 18 (by decide) (by decide)) s2 s3 (addNodeTicks a 1) := by
    apply addNode_spec 16 20 18 (by decide) (by decide) (by decide) s2 hc2 a 1
    · simp [s2,s1,put,ha]
    · simp [s2,s1,put]
    · simp [s2,s1,put,h18]
  have hc3 : CoreEmpty s3 := coreEmpty_update s2 hc2 18 (by decide) _
  have h4 : RunSpec (mulNode 21 17 19 (by decide) (by decide)) s3 s4 (mulNodeTicks 2 b) := by
    apply mulNode_spec 21 17 19 (by decide) (by decide) (by decide) s3 hc3 2 b
    · simp [s3,s2,s1,put]
    · simp [s3,s2,s1,put,hb]
    · simp [s3,s2,s1,put,h19]
  have hc4 : CoreEmpty s4 := coreEmpty_update s3 hc3 19 (by decide) _
  have h5 : RunSpec (negNode 18 24 (by decide)) s4 s5 (negNodeTicks (a+1)) := by
    apply negNode_spec 18 24 (by decide) (by decide) s4 hc4 (a+1)
    · simp [s4,s3,put]
    · simp [s4,s3,s2,s1,put,h24]
  have hc5 : CoreEmpty s5 := coreEmpty_update s4 hc4 24 (by decide) _
  have h6 : RunSpec (divNode 24 19 25 (by decide) (by decide)) s5 (after s a b)
      (divNodeTicks (-(a+1)) (2*b)) := by
    apply divNode_spec 24 19 25 (by decide) (by decide) (by decide) s5 hc5 (-(a+1)) (2*b)
    · simp [s5,put]
    · simp [s5,s4,put]
    · simp [s5,s4,s3,s2,s1,put,h25]
  exact h1.compose (h2.compose (h3.compose (h4.compose (h5.compose h6))))

end KS.W19.SparseScalarNodes

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_ZeroPaddedRow
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W06.RationalSignClassifier.program_output _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.RowDot
open Matrix
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07
open scoped BigOperators

theorem prependZero_spec {k : ℕ} (port : Fin k) (s : Fin k → List Bool) :
    RunSpec (prependZero port) s (Function.update s port (zeroFrame ++ s port)) 11 := by
  let s1 := Function.update s port (true :: s port)
  let s2 := Function.update s1 port (true :: s1 port)
  let s3 := Function.update s2 port (false :: s2 port)
  let s4 := Function.update s3 port (true :: s3 port)
  let s5 := Function.update s4 port (false :: s4 port)
  let s6 := Function.update s5 port (false :: s5 port)
  let s7 := Function.update s6 port (false :: s6 port)
  let s8 := Function.update s7 port (true :: s7 port)
  let s9 := Function.update s8 port (false :: s8 port)
  let s10 := Function.update s9 port (false :: s9 port)
  have h := ((((((((((literalPush_spec port true s).compose (literalPush_spec port true s1)).compose
    (literalPush_spec port false s2)).compose (literalPush_spec port true s3)).compose
    (literalPush_spec port false s4)).compose (literalPush_spec port false s5)).compose
    (literalPush_spec port false s6)).compose (literalPush_spec port true s7)).compose
    (literalPush_spec port false s8)).compose (literalPush_spec port false s9)).compose
    (literalPush_spec port false s10)
  have hz : zeroFrame = [false, false, false, true, false, false, false, true, false, true, true] := by decide
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  funext j
  by_cases hj : j = port <;>
    simp [hz, hj, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10]

theorem copyZeroPadded_spec {k n : ℕ} (ports : Fin 3 ↪ Fin k) (s : Fin k → List Bool)
    (y : Fin n → ℚ) (hs : s (ports 0) = vectorTape y)
    (hd : s (ports 1) = []) (ht : s (ports 2) = []) :
    RunSpec (copyZeroPadded ports) s
      (Function.update s (ports 1) (vectorTape (zeroPadded y)))
      (2 * (vectorTape y).length + 13) := by
  have hc : RunSpec (KS.W01.FixedCopy.program ports) s
      (Function.update s (ports 1) (vectorTape y)) (2 * (vectorTape y).length + 2) := by
    intro bits hbits
    exact KS.W01.FixedCopy.run_copy_restore ports s (vectorTape y) bits hs hd ht hbits
  have h := hc.compose (prependZero_spec (ports 1) (Function.update s (ports 1) (vectorTape y)))
  simpa [copyZeroPadded, zeroPadded, vectorTape_cons, zeroFrame, Function.update_idem,
    Nat.add_assoc] using h

end KS.W12.RowDot

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

theorem divide_spec (x p c : ℚ) :
    RunSpec divide
      (workspace (KS.W01.encodeRat p ++ KS.W01.encodeRat c) [] (KS.W01.encodeRat x) [] [] [])
      (workspace [] (KS.W01.encodeRat (p / c)) (KS.W01.encodeRat x) [] [] [])
      (KS.W29.polynomialFuel 1100000 3 (KS.W30.RationalDivision.inputBits p c).length) := by
  have h := first_spec (by decide : 15 ≤ 23) _ _ _
    (workspace [] [] (KS.W01.encodeRat x) [] [] []) _
    (KS.W30.RationalDivision.program_spec p c)
  have hb : extend (KS.W30.RationalDivision.inputState (KS.W30.RationalDivision.inputBits p c))
      (workspace [] [] (KS.W01.encodeRat x) [] [] []) =
      workspace (KS.W01.encodeRat p ++ KS.W01.encodeRat c) [] (KS.W01.encodeRat x) [] [] [] := by
    funext j; fin_cases j <;> rfl
  have ha : extend (KS.W30.RationalDivision.outputState (KS.W01.encodeRat (p/c)))
      (workspace [] [] (KS.W01.encodeRat x) [] [] []) =
      workspace [] (KS.W01.encodeRat (p/c)) (KS.W01.encodeRat x) [] [] [] := by
    funext j; fin_cases j <;> rfl
  rw [hb, ha] at h
  exact h

theorem full_spec (x a b c : ℚ) :
    RunSpec program
      (workspace [] [] (KS.W01.encodeRat x) (KS.W01.encodeRat a)
        (KS.W01.encodeRat b) (KS.W01.encodeRat c))
      (workspace [] (KS.W01.encodeRat (x - a * b / c)) [] [] [] []) (ticks x a b c) := by
  exact (prepare_product_spec _ _ _ _).compose ((multiply_spec x a b c).compose
    ((prepare_division_spec _ _ _).compose ((divide_spec x (a*b) c).compose
      ((prepare_subtraction_spec _ _).compose (subtract_spec x (a*b/c))))))

end KS.W07.SchurCellMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_SchurCellCost
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.sumBudget_cons _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurCellMachine

open KS.W01

theorem ticks_le_cellBudget (x a b c : ℚ) (B : ℕ)
    (hx : x.num.natAbs ≤ 2 ^ B ∧ x.den ≤ 2 ^ B)
    (ha : a.num.natAbs ≤ 2 ^ B ∧ a.den ≤ 2 ^ B)
    (hb : b.num.natAbs ≤ 2 ^ B ∧ b.den ≤ 2 ^ B)
    (hc : c.num.natAbs ≤ 2 ^ B ∧ c.den ≤ 2 ^ B) :
    ticks x a b c ≤ cellBudget B := by
  have lx := ratLength_le_of_parts x B B hx.1 hx.2
  have la := ratLength_le_of_parts a B B ha.1 ha.2
  have lb := ratLength_le_of_parts b B B hb.1 hb.2
  have lc := ratLength_le_of_parts c B B hc.1 hc.2
  have hp := KS.W30.mul_parts_le_two_pow a b B B ha.1 ha.2 hb.1 hb.2
  have lp := ratLength_le_of_parts (a*b) (B+B) (B+B) hp.1 hp.2
  have hq := KS.W30.div_parts_le_two_pow (a*b) c (B+B) B hp.1 hp.2 hc.1 hc.2
  have lq := ratLength_le_of_parts (a*b/c) (B+B+B) (B+B+B) hq.1 hq.2
  let H := 16 * B + 40
  have hab : (KS.W15.RationalMultiply.inputBits a b).length + 1 ≤ H := by
    simp only [KS.W15.RationalMultiply.inputBits,List.length_append]
    change ratLength a + ratLength b + 1 ≤ H
    dsimp [H]; omega
  have hpc : (KS.W30.RationalDivision.inputBits (a*b) c).length + 1 ≤ H := by
    simp only [KS.W30.RationalDivision.inputBits,List.length_append]
    change ratLength (a*b) + ratLength c + 1 ≤ H
    dsimp [H]; omega
  have hxq : (encodeRat x ++ encodeRat (a*b/c)).length + 1 ≤ H := by
    rw [List.length_append]
    change ratLength x + ratLength (a*b/c) + 1 ≤ H
    dsimp [H]; omega
  have hm := (KS.W15.RationalMultiply.totalTicks_le_polynomial a b).trans
    (Nat.mul_le_mul_left 2048 (Nat.pow_le_pow_left hab 3))
  have hd := Nat.mul_le_mul_left 1100000 (Nat.pow_le_pow_left hpc 3)
  have hs := Nat.mul_le_mul_left 600000 (Nat.pow_le_pow_left hxq 3)
  have hH : H ≤ H^3 := Nat.le_self_pow (by decide : 3 ≠ 0) H
  unfold ticks cellBudget
  change _ ≤ 4000000 * H^3
  dsimp [KS.W29.polynomialFuel] at hm ⊢
  have htransfer : (4*ratLength a+2*ratLength b+4) +
      (4*ratLength (a*b)+2*ratLength c+4) +
      (4*ratLength x+2*ratLength (a*b/c)+4) ≤ 10*H := by
    dsimp [H]; omega
  omega

end KS.W07.SchurCellMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurReadStage
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.sumBudget_cons _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W17.FixedPSD.withSaved_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurReadStage
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem reader_spec {n : ℕ} (M : DenseRatMatrix n) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (i j : Fin n) (before : Fin 32 → List Bool) (hw : WorkClear before)
    (hm : before 31 = KS.W08.denseMatrixTape M) :
    RunSpec reader
      (readPrepared before (Computability.encodeNat j.val) (Computability.encodeNat i.val)
        (Computability.encodeNat n))
      (Function.update before 0 (KS.W01.encodeRat (DenseRatMatrix.decode M i j)))
      (1024*(n+1)^2*(B+1)) := by
  have hsmall : RunSpec KS.W08.MatrixRead.program
      (KS.W08.MatrixRead.workspace (KS.W08.denseMatrixTape M)
        (Computability.encodeNat j.val) (Computability.encodeNat i.val) (Computability.encodeNat n) [])
      (KS.W08.MatrixRead.workspace (KS.W08.denseMatrixTape M)
        (KS.W01.encodeRat (DenseRatMatrix.decode M i j)) [] [] [])
      (1024*(n+1)^2*(B+1)) := by
    intro bits hbits
    exact KS.W08.MatrixRead.run_matrix_read M B hnum hden i j bits hbits.ge
  have hw1 := hw 1 (by decide)
  have hw2 := hw 2 (by decide)
  have hw3 := hw 3 (by decide)
  have hw4 := hw 4 (by decide)
  have hw5 := hw 5 (by decide)
  have hw6 := hw 6 (by decide)
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ readPorts _ _ _ _ _ hsmall
  · intro r
    fin_cases r <;> simp [readPorts, readPrepared, KS.W08.MatrixRead.workspace, hm, hw3, hw4, hw5, hw6]
  · intro r
    fin_cases r <;> simp [readPorts, KS.W08.MatrixRead.workspace, hm, hw1, hw2, hw3, hw4, hw5, hw6]
  · intro r hr
    have h0 := hr 0
    have h1 := hr 1
    have h2 := hr 2
    change r ≠ 0 at h0
    change r ≠ 1 at h1
    change r ≠ 2 at h2
    simp [readPrepared, Function.update_of_ne h0, Function.update_of_ne h1,
      Function.update_of_ne h2]

theorem full_spec {n : ℕ} (M : DenseRatMatrix n) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (i j : Fin n) (before : Fin 32 → List Bool) (hw : WorkClear before)
    (hm : before 31 = KS.W08.denseMatrixTape M) (hd : before 26 = Computability.encodeNat n)
    (row col : Bool) (hr : before (rowSource row) = Computability.encodeNat i.val)
    (hc : before (colSource col) = Computability.encodeNat j.val)
    (k : Fin 4) (hk : before (destination k) = []) :
    RunSpec (program row col k) before
      (Function.update before (destination k) (KS.W01.encodeRat (DenseRatMatrix.decode M i j)))
      (prepareTicks before row col + (1024*(n+1)^2*(B+1) +
        (2*KS.W01.ratLength (DenseRatMatrix.decode M i j)+2))) := by
  have hp := prepare_spec before hw row col
  rw [hr,hc,hd] at hp
  have hread := reader_spec M B hnum hden i j before hw hm
  have hmove := WireAppend.spec (0 : Fin 32) (destination k) 16
    (Ne.symm (destination_ne_core k 0 (by decide))) (by decide)
    (Ne.symm (destination_ne_core k 16 (by decide)))
    (Function.update before 0 (KS.W01.encodeRat (DenseRatMatrix.decode M i j)))
    (by simpa using hw 16 (by decide))
  have hout : WireAppend.after 0 (destination k)
      (Function.update before 0 (KS.W01.encodeRat (DenseRatMatrix.decode M i j))) =
      Function.update before (destination k) (KS.W01.encodeRat (DenseRatMatrix.decode M i j)) := by
    funext r
    have hd0 : destination k ≠ 0 := destination_ne_core k 0 (by decide)
    by_cases h0 : r=0
    · subst r
      simp [WireAppend.after, Ne.symm hd0, hw 0 (by decide)]
    · by_cases hdest : r=destination k
      · subst r
        simp [WireAppend.after, hd0, hk]
      · simp [WireAppend.after, h0, hdest]
  rw [hout] at hmove
  simp only [Function.update_self] at hmove
  exact hp.compose (hread.compose hmove)

end KS.W07.SchurReadStage

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_TerminalReadStage
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.sumBudget_cons _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W17.FixedPSD.withSaved_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.TerminalReadStage
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W07

theorem read_spec {n : ℕ} (M : DenseRatMatrix n) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (i j : Fin n) (s : Fin 35 → List Bool) (hw : WorkClear s)
    (hm : s 31 = KS.W08.denseMatrixTape M) (hd : s 26 = Computability.encodeNat n)
    (diagonal : Bool) (hr : s (sourceRow diagonal) = Computability.encodeNat i.val)
    (hc : s 33 = Computability.encodeNat j.val) (he : s (destination diagonal) = []) :
    RunSpec (program diagonal) s
      (Function.update s (destination diagonal) (KS.W01.encodeRat (DenseRatMatrix.decode M i j)))
      (readTicks M B i j s diagonal) := by
  have hwork : SchurReadStage.WorkClear (fun k => s (ports k)) := by
    intro k hk
    apply hw
    fin_cases k <;> simp_all [ports]
  have hrow : s (ports (SchurReadStage.rowSource diagonal)) = Computability.encodeNat i.val := by
    cases diagonal <;> simpa [ports,SchurReadStage.rowSource,sourceRow] using hr
  have hdest : ports (SchurReadStage.destination (slot diagonal)) = destination diagonal := by
    cases diagonal <;> rfl
  have h := SchurReadStage.full_spec M B hnum hden i j (fun k => s (ports k)) hwork
    hm hd diagonal true hrow hc (slot diagonal) (by
      exact (congrArg s hdest).trans he)
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ ports _ _ _ _ _ h
  · intro k; rfl
  · intro k
    by_cases hk : k = SchurReadStage.destination (slot diagonal)
    · subst k
      simp only [Function.update_self]
      exact (congrArg (Function.update s (destination diagonal)
        (KS.W01.encodeRat (DenseRatMatrix.decode M i j))) hdest).trans
          (Function.update_self _ _ _)
    · have hne : ports k ≠ destination diagonal := by
        rw [← hdest]
        exact fun h => hk (ports.injective h)
      simp [Function.update_of_ne,hk,hne]
  · intro k hk
    have hne : k ≠ destination diagonal := by simpa only [hdest] using hk (SchurReadStage.destination (slot diagonal))
    simp [Function.update_of_ne,hne]

end KS.W19.TerminalReadStage

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_FramedArrayReplacement
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationMachine.input_port _root_.OAI.KS.W03.MultiplicationMachine.output_port _root_.OAI.KS.W03.MultiplicationMachine.stack_count _root_.OAI.KS.W03.MultiplicationMachine.state_count _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W06.RationalSignClassifier.program_output _root_.OAI.KS.W12.FixedDot.machine_inputStack _root_.OAI.KS.W12.FixedDot.machine_outputStack _root_.OAI.KS.W12.FixedDot.machine_stackCount _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W15.RationalMultiply.machine_inputStack _root_.OAI.KS.W15.RationalMultiply.machine_outputStack _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W11.FramedArrayRewrite
open KS.W01.FixedStack KS.W03.MachineCombinators
open KS.W29.FixedSequential
open KS.W04.ReusableArrayLookup (run_halted_of_length_ge run_compose_bounded)

theorem run_replace (xs : List (List Bool)) (i : ℕ) (hi : i < xs.length)
    (new tail bits : List Bool)
    (hlen : 2 * (xs.flatMap KS.W01.frame ++ tail).length +
      2 * (KS.W01.frame new).length + i + 3 ≤ bits.length) :
    program.toMachine.run
      (config (some program.initial) (xs.flatMap KS.W01.frame ++ tail)
        (KS.W01.frame new) [] [] (List.replicate i true)) bits =
      config none ((xs.set i new).flatMap KS.W01.frame ++ tail) [] [] [] [] := by
  have hx : xs = xs.take i ++ xs[i] :: xs.drop (i + 1) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have ht : (xs.take i).length = i := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hflat : xs.flatMap KS.W01.frame ++ tail =
      (xs.take i).flatMap KS.W01.frame ++ KS.W01.frame xs[i] ++
        ((xs.drop (i + 1)).flatMap KS.W01.frame ++ tail) := by
    conv_lhs => rw [hx]
    simp only [List.flatMap_append, List.flatMap_cons, List.append_assoc]
  have hset : (xs.set i new).flatMap KS.W01.frame ++ tail =
      (xs.take i).flatMap KS.W01.frame ++ KS.W01.frame new ++
        ((xs.drop (i + 1)).flatMap KS.W01.frame ++ tail) := by
    rw [List.set_eq_take_append_cons_drop, ite_eq_left hi]
    simp only [List.flatMap_append, List.flatMap_cons, List.append_assoc]
  have hb := replaceFuel_linear (xs.take i) xs[i] new
    ((xs.drop (i + 1)).flatMap KS.W01.frame ++ tail)
  rw [← hflat, ht] at hb
  have h := run_replace_prefix (xs.take i) xs[i] new
    ((xs.drop (i + 1)).flatMap KS.W01.frame ++ tail) bits (hb.trans hlen)
  simpa only [← hflat, ← hset, ht] using h

end KS.W11.FramedArrayRewrite

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_TerminalVectorReplace
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationMachine.input_port _root_.OAI.KS.W03.MultiplicationMachine.output_port _root_.OAI.KS.W03.MultiplicationMachine.stack_count _root_.OAI.KS.W03.MultiplicationMachine.state_count _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W06.RationalSignClassifier.program_output _root_.OAI.KS.W12.FixedDot.machine_inputStack _root_.OAI.KS.W12.FixedDot.machine_outputStack _root_.OAI.KS.W12.FixedDot.machine_stackCount _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W15.RationalMultiply.machine_inputStack _root_.OAI.KS.W15.RationalMultiply.machine_outputStack _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.TerminalVectorReplace
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators Matrix

theorem replace_spec (s : Fin 35 → List Bool) (xs : List (List Bool)) (i : ℕ)
    (hi : i < xs.length) (new : List Bool) (hs : s 23 = xs.flatMap KS.W01.frame)
    (h0 : s 0 = []) (h1 : s 1 = []) (h2 : s 2 = []) (h3 : s 3 = []) :
    RunSpec program (prepared s new i)
      (Function.update s 23 ((xs.set i new).flatMap KS.W01.frame))
      (2*(xs.flatMap KS.W01.frame).length + 2*(KS.W01.frame new).length+i+3) := by
  have hsmall : RunSpec KS.W11.FramedArrayRewrite.program
      (KS.W11.FramedArrayRewrite.«stacks» (xs.flatMap KS.W01.frame)
        (KS.W01.frame new) [] [] (List.replicate i true))
      (KS.W11.FramedArrayRewrite.«stacks» ((xs.set i new).flatMap KS.W01.frame) [] [] [] [])
      (2*(xs.flatMap KS.W01.frame).length+2*(KS.W01.frame new).length+i+3) := by
    intro bits hb
    have h := KS.W11.FramedArrayRewrite.run_replace xs i hi new [] bits (by simpa using hb.ge)
    simp only [List.append_nil] at h
    exact h
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ ports _ _ _ _ _ hsmall
  · intro j; fin_cases j <;> simp [ports,prepared,KS.W11.FramedArrayRewrite.«stacks»,hs,h1,h2]
  · intro j; fin_cases j <;> simp [ports,KS.W11.FramedArrayRewrite.«stacks»,h0,h1,h2,h3]
  · intro j hj
    have ha := hj 0
    have hb := hj 1
    have hc := hj 4
    change j ≠ 23 at ha
    change j ≠ 0 at hb
    change j ≠ 3 at hc
    simp [prepared,Function.update_of_ne,ha,hb,hc]

theorem unit_spec (s : Fin 35 → List Bool) (n : ℕ) (hn : 0 < n)
    (hd : s 26 = Computability.encodeNat n)
    (h0 : s 0 = []) (h1 : s 1 = []) (h2 : s 2 = []) (h3 : s 3 = [])
    (h16 : s 16 = []) (h23 : s 23 = []) :
    RunSpec unitProgram s
      (Function.update s 23 ((unitPayloads n).flatMap KS.W01.frame))
      (TerminalZeroVector.ticks n + (oneFrame.length+1+
        (2*((zeroPayloads n).flatMap KS.W01.frame).length+2*oneFrame.length+3))) := by
  have hz := TerminalZeroVector.zero_vector_spec s n hd h0 h1 h2 h16 h23
  rw [zeroTape_eq] at hz
  let mid := Function.update s 23 ((zeroPayloads n).flatMap KS.W01.frame)
  have hl := KS.W15.WireProgram.literal_spec (0 : Fin 35) oneFrame mid
  have hp := replace_spec mid (zeroPayloads n) 0 (by simpa [zeroPayloads] using hn)
    (KS.W01.encodeRat 1) rfl (by simpa [mid] using h0) (by simpa [mid] using h1)
    (by simpa [mid] using h2) (by simpa [mid] using h3)
  have he : Function.update mid 0 (oneFrame ++ mid 0) = prepared mid (KS.W01.encodeRat 1) 0 := by
    funext j; fin_cases j <;> simp [mid,prepared,oneFrame,h0,h3]
  rw [he] at hl
  have ho : Function.update mid 23 (((zeroPayloads n).set 0 (KS.W01.encodeRat 1)).flatMap KS.W01.frame) =
      Function.update s 23 ((unitPayloads n).flatMap KS.W01.frame) := by
    simp [mid,unitPayloads]
  rw [ho] at hp
  exact hz.compose (hl.compose hp)

end KS.W19.TerminalVectorReplace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_TerminalSparseAssembly
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_ratFields
attribute [-simp] _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.BinaryMultiply.shift_value _root_.OAI.KS.W03.MultiplicationMachine.input_port _root_.OAI.KS.W03.MultiplicationMachine.output_port _root_.OAI.KS.W03.MultiplicationMachine.stack_count _root_.OAI.KS.W03.MultiplicationMachine.state_count _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W08.denseMatrixBinaryCursor_value _root_.OAI.KS.W12.FixedDot.machine_inputStack _root_.OAI.KS.W12.FixedDot.machine_outputStack _root_.OAI.KS.W12.FixedDot.machine_stackCount _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W15.RationalMultiply.machine_inputStack _root_.OAI.KS.W15.RationalMultiply.machine_outputStack _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_quotient _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_remainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.TerminalSparseAssembly
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W19.TerminalVectorReplace

theorem setOne_spec (s : Fin 35 → List Bool) (xs : List (List Bool)) (j : ℕ)
    (hj : j < xs.length) (hs : s 23 = xs.flatMap KS.W01.frame)
    (hindex : s 30 = Computability.encodeNat j)
    (h0 : s 0 = []) (h1 : s 1 = []) (h2 : s 2 = []) (h3 : s 3 = []) :
    RunSpec setOneProgram s
      (Function.update (Function.update s 30 []) 23 ((xs.set j (KS.W01.encodeRat 1)).flatMap KS.W01.frame))
      (oneFrame.length+1 + ((4*j+4*(Computability.encodeNat j).length+2) +
        (2*(xs.flatMap KS.W01.frame).length+2*oneFrame.length+j+3))) := by
  let base := Function.update s 30 []
  let first := Function.update s 0 oneFrame
  have hl : RunSpec (KS.W15.WireProgram.literalProgram 0 oneFrame) s first (oneFrame.length+1) := by
    simpa [first,h0] using KS.W15.WireProgram.literal_spec (0 : Fin 35) oneFrame s
  have hu0 : RunSpec KS.W03.BinaryToUnary.program
      ![Computability.encodeNat j,[],[]] ![[],List.replicate j true,[]]
      (4*j+4*(Computability.encodeNat j).length+2) := by
    apply KS.W03.MachineRoundTrip.runSpec_ofMachine
    intro bits hb
    have h := KS.W03.BinaryToUnary.run_input_linear (Computability.encodeNat j) bits
      (by simpa only [bitsValue_encodeNat] using hb.ge)
    simp only [KS.W03.BinaryToUnary.init_eq,KS.W03.BinaryToUnary.cfg,
      bitsValue_encodeNat] at h
    exact h
  have hu : RunSpec unaryProgram first (prepared base (KS.W01.encodeRat 1) j)
      (4*j+4*(Computability.encodeNat j).length+2) := by
    apply KS.W01.FixedPortRunSpec.lift_runSpec _ unaryPorts _ _ _ _ _ hu0
    · intro i; fin_cases i <;> simp [unaryPorts,first,hindex,h1,h3]
    · intro i; fin_cases i <;> simp [unaryPorts,base,prepared,h1]
    · intro i hi
      have ha := hi 0
      have hb := hi 1
      change i ≠ 30 at ha
      change i ≠ 3 at hb
      by_cases hi0 : i = 0
      · subst i; simp [first,base,prepared,oneFrame]
      · simp [first,base,prepared,oneFrame,Function.update_of_ne,ha,hb,hi0]
  have hr := replace_spec base xs j hj (KS.W01.encodeRat 1)
    (by simpa [base] using hs) (by simpa [base] using h0) (by simpa [base] using h1)
    (by simpa [base] using h2) (by simpa [base] using h3)
  exact hl.compose (hu.compose hr)

theorem head_spec (s : Fin 35 → List Bool) (n : ℕ) (hn : 0<n) (c : ℚ)
    (hd : s 26 = Computability.encodeNat n) (hc : s 28 = KS.W01.encodeRat c)
    (h0 : s 0 = []) (h1 : s 1 = []) (h2 : s 2 = []) (h3 : s 3 = [])
    (h16 : s 16 = []) (h23 : s 23 = []) :
    RunSpec headProgram s
      (Function.update (Function.update s 28 []) 23
        (((zeroPayloads n).set 0 (KS.W01.encodeRat c)).flatMap KS.W01.frame)) (headTicks n c) := by
  let mid := Function.update s 23 ((zeroPayloads n).flatMap KS.W01.frame)
  let base := Function.update mid 28 []
  let framed := Function.update mid 28 (KS.W01.frame (KS.W01.encodeRat c))
  have hz := TerminalZeroVector.zero_vector_spec s n hd h0 h1 h2 h16 h23
  rw [zeroTape_eq] at hz
  have hf := KS.W11.FrameWireCodec.frame_spec framePorts mid (KS.W01.encodeRat c)
  have hi : KS.W28.FixedPositiveSerializer.registers framePorts mid [] (KS.W01.encodeRat c) [] = mid := by
    funext j; fin_cases j <;> simp [framePorts,KS.W28.FixedPositiveSerializer.registers,mid,h0,h1,hc]
  have ho : KS.W28.FixedPositiveSerializer.registers framePorts mid [] (KS.W01.frame (KS.W01.encodeRat c)) [] = framed := by
    funext j; fin_cases j <;> simp [framePorts,KS.W28.FixedPositiveSerializer.registers,mid,framed,h0,h1]
  rw [hi,ho] at hf
  have hm := KS.W07.WireAppend.spec (28 : Fin 35) 0 16 (by decide) (by decide) (by decide)
    framed (by simpa [framed,mid] using h16)
  have he : KS.W07.WireAppend.after 28 0 framed = prepared base (KS.W01.encodeRat c) 0 := by
    funext j; fin_cases j <;> simp [KS.W07.WireAppend.after,framed,mid,base,prepared,h0,h3]
  rw [he] at hm
  have hr := replace_spec base (zeroPayloads n) 0 (by simpa [zeroPayloads] using hn)
    (KS.W01.encodeRat c) (by simp [base,mid]) (by simpa [base,mid] using h0)
    (by simpa [base,mid] using h1) (by simpa [base,mid] using h2) (by simpa [base,mid] using h3)
  have hout : Function.update base 23 (((zeroPayloads n).set 0 (KS.W01.encodeRat c)).flatMap KS.W01.frame) =
      Function.update (Function.update s 28 []) 23
        (((zeroPayloads n).set 0 (KS.W01.encodeRat c)).flatMap KS.W01.frame) := by
    funext j; fin_cases j <;> simp [base,mid]
  rw [hout] at hr
  have h := hz.compose (hf.compose (hm.compose hr))
  simp [headProgram,headTicks,framed,mid] at h ⊢
  exact h

theorem sparse_spec {n : ℕ} (s : Fin 35 → List Bool) (j : Fin (n+1)) (hj : j ≠ 0) (c : ℚ)
    (hd : s 26 = Computability.encodeNat (n+1)) (hc : s 28 = KS.W01.encodeRat c)
    (hindex : s 30 = Computability.encodeNat j.val)
    (h0 : s 0 = []) (h1 : s 1 = []) (h2 : s 2 = []) (h3 : s 3 = [])
    (h16 : s 16 = []) (h23 : s 23 = []) :
    RunSpec program s
      (Function.update (Function.update (Function.update s 28 []) 30 []) 23
        (KS.W12.RowDot.vectorTape (sparseVector j c))) (ticks (n+1) j.val c) := by
  let xs := (zeroPayloads (n+1)).set 0 (KS.W01.encodeRat c)
  let mid := Function.update (Function.update s 28 []) 23 (xs.flatMap KS.W01.frame)
  have hh := head_spec s (n+1) (by omega) c hd hc h0 h1 h2 h3 h16 h23
  have hi := setOne_spec mid xs j.val (by simpa [xs,zeroPayloads] using j.isLt) rfl
    (by simpa [mid] using hindex) (by simpa [mid] using h0) (by simpa [mid] using h1)
    (by simpa [mid] using h2) (by simpa [mid] using h3)
  have ht : (xs.set j.val (KS.W01.encodeRat 1)).flatMap KS.W01.frame =
      KS.W12.RowDot.vectorTape (sparseVector j c) := sparse_tape j hj c
  rw [ht] at hi
  have he : Function.update (Function.update mid 30 []) 23
      (KS.W12.RowDot.vectorTape (sparseVector j c)) =
      Function.update (Function.update (Function.update s 28 []) 30 []) 23
        (KS.W12.RowDot.vectorTape (sparseVector j c)) := by
    funext k; fin_cases k <;> simp [mid]
  rw [he] at hi
  exact hh.compose hi

end KS.W19.TerminalSparseAssembly

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

theorem collect_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B) (j : Fin (n+1)) :
    RunSpec collect (inputState saved M j) (collected saved M j) (collectTicks saved M B j) := by
  let s := Function.update (inputState saved M j) 33 (Computability.encodeNat j.val)
  let t := Function.update s 19 (KS.W01.encodeRat (DenseRatMatrix.decode M j j))
  have hc := KS.W15.WireProgram.copy_spec (30 : Fin 35) 33 16 (by decide) (by decide) (by decide)
    (inputState saved M j) rfl rfl
  have hs : TerminalReadStage.WorkClear s := by
    intro i hi
    fin_cases i <;> simp_all [s,inputState]
  have ht : TerminalReadStage.WorkClear t := by
    intro i hi
    fin_cases i <;> simp_all [t,s,inputState]
  have h1 := TerminalReadStage.read_spec M B hnum hden j j s hs rfl rfl true rfl rfl rfl
  have h2 := TerminalReadStage.read_spec M B hnum hden 0 j t ht rfl rfl false rfl rfl rfl
  exact hc.compose (h1.compose h2)

end KS.W19.TerminalWitnessMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_TerminalWitnessCost
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.sumBudget_cons _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W17.FixedPSD.withSaved_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.TerminalWitnessMachine
open KS.W01 KS.W07

theorem coefficient_length (a b : ℚ) :
    ratLength (SparseScalarNodes.coefficient a b) ≤ 80*(ratLength a+ratLength b+10) := by
  have h1 := ratLength_add_le a 1
  have h2 := ratLength_mul_le 2 b
  have h3 := ratLength_neg_le (a+1)
  have h4 := SparseScalarNodes.ratLength_div_le (-(a+1)) (2*b)
  have l1 : ratLength (1 : ℚ) = 7 := by decide
  have l2 : ratLength (2 : ℚ) = 9 := by decide
  rw [l1] at h1
  rw [l2] at h2
  change ratLength (-(a+1)/(2*b)) ≤ _
  omega

theorem ticks_polynomial {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (B L : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (hn : n+1 ≤ L) (hB : B ≤ L) (j : Fin (n+1)) :
    ticks saved M B j ≤ 1000000000000000000*(L+1)^3 := by
  let a := DenseRatMatrix.decode M j j
  let b := DenseRatMatrix.decode M 0 j
  have la : ratLength a ≤ 4*L+7 := by
    have h := ratLength_le_of_parts a B B (hnum j j) (hden j j)
    omega
  have lb : ratLength b ≤ 4*L+7 := by
    have h := ratLength_le_of_parts b B B (hnum 0 j) (hden 0 j)
    omega
  have lj := raw_length_le j.val
  have ln := raw_length_le (n+1)
  have hj := j.isLt
  have lp : L+1 ≤ (L+1)^3 := Nat.le_self_pow (by decide) _
  have hread : (n+1+1)^2*(B+1) ≤ (L+1)^3 := by
    calc
      _ ≤ (L+1)^2*(L+1) := Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2) (by omega)
      _ = (L+1)^3 := by ring
  have hcollect : collectTicks saved M B j ≤ 100000*(L+1)^3 := by
    unfold collectTicks TerminalReadStage.readTicks KS.W07.SchurReadStage.prepareTicks
    simp [TerminalReadStage.ports,KS.W07.SchurReadStage.rowSource,KS.W07.SchurReadStage.colSource,inputState]
    change ratLength (DenseRatMatrix.decode M j j) ≤ _ at la
    change ratLength (DenseRatMatrix.decode M 0 j) ≤ _ at lb
    nlinarith [Nat.mul_le_mul_left 1024 hread]
  have hbase : 200*(ratLength a+ratLength b+1) ≤ 3000*(L+1) := by omega
  have hscalar := (SparseScalarNodes.ticks_polynomial a b).trans
    (Nat.mul_le_mul_left 3000000 (Nat.pow_le_pow_left hbase 3))
  have hclean := cleanupTicks_linear saved M j
  have hcoeff := coefficient_length a b
  have hassemble := assemblyTicks_linear n j (coefficient M j)
  unfold ticks scalarTicks SparseCoefficientStage.ticks
  change collectTicks saved M B j + (SparseScalarNodes.ticks a b + _ + _) ≤ _
  change ratLength (coefficient M j) ≤ _ at hcoeff
  rw [mul_pow] at hscalar
  norm_num only [show (3000 : ℕ)^3 = 27000000000 by decide] at hscalar
  dsimp only [a,b] at la lb hscalar hcoeff ⊢
  omega

end KS.W19.TerminalWitnessMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_StoredWitnessLift
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationMachine.input_port _root_.OAI.KS.W03.MultiplicationMachine.output_port _root_.OAI.KS.W03.MultiplicationMachine.stack_count _root_.OAI.KS.W03.MultiplicationMachine.state_count _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W06.RationalSignClassifier.program_output _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W17.FixedPSD.withSaved_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.StoredWitnessLift
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07
open KS.W12.RowDot

theorem full_spec {n : ℕ} (M : DenseRatMatrix (n + 1)) (y : Fin n → ℚ) :
    RunSpec program (saved M y)
      (Function.update (saved M y) 17 (vectorTape (Fin.cons (schurHead M y) y))) (ticks M y) := by
  let z := KS.W01.encodeRat (schurHead M y)
  let padded := vectorTape (zeroPadded y)
  have h1 : RunSpec (copyZeroPadded padPorts) (saved M y) (work M y padded [] [])
      (2 * (vectorTape y).length + 13) := by
    convert copyZeroPadded_spec padPorts (saved M y) y rfl rfl rfl using 1
    all_goals try with_reducible_and_instances rfl
    funext j
    fin_cases j <;> rfl
  have h2 : RunSpec headProgram (work M y padded [] []) (work M y padded z []) (headBudget M y) := by
    apply KS.W01.FixedPortRunSpec.lift_runSpec _ _ _ _ _ _ _ (schurHead_polynomial_spec M y)
    · intro j
      fin_cases j <;> rfl
    · intro j
      fin_cases j <;> rfl
    · intro j hj
      have h10 : j ≠ 10 := hj 10
      simp [work, h10]
  have h3 : RunSpec (KS.W11.FrameWireCodec.frameProgram framePorts) (work M y padded z [])
      (work M y padded (KS.W01.frame z) []) (4 * z.length + 3) := by
    convert KS.W11.FrameWireCodec.frame_spec framePorts (work M y padded z []) z using 1 <;>
      funext j <;> fin_cases j <;>
      simp [work, saved, framePorts, KS.W28.FixedPositiveSerializer.registers]
  have h4 : RunSpec (KS.W01.FixedCopy.program copyPorts) (work M y padded (KS.W01.frame z) [])
      (work M y padded (KS.W01.frame z) (vectorTape y)) (2 * (vectorTape y).length + 2) := by
    intro bits hbits
    have h := KS.W01.FixedCopy.run_copy_restore copyPorts (work M y padded (KS.W01.frame z) [])
      (vectorTape y) bits rfl rfl rfl hbits
    refine (KS.W19.MachineTransport.run_ofMachine
      (KS.W01.FixedCopy.machine copyPorts)
      (⟨some (0 : Fin 2), work M y padded (KS.W01.frame z) []⟩ : Config 30 2)
      bits).trans (h.trans ?_)
    apply congrArg (fun ws : Fin 30 → List Bool =>
      (Config.mk (none : Option (Fin 2)) ws : Config 30 2))
    funext j
    fin_cases j <;> rfl
  have h5 : RunSpec (KS.W12.StackTransfer.program 10 17 26)
      (work M y padded (KS.W01.frame z) (vectorTape y))
      (work M y padded [] (KS.W01.frame z ++ vectorTape y))
      (2 * (KS.W01.frame z).length + 2) := by
    convert KS.W12.StackTransfer.spec (10 : Fin 30) 17 26 (by decide) (by decide) (by decide)
      (work M y padded (KS.W01.frame z) (vectorTape y)) rfl using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
    funext j
    fin_cases j <;> simp [KS.W12.StackTransfer.after, work, saved]
  have h6 : RunSpec (KS.W04.BinaryStackMoves.clearProgram 20)
      (work M y padded [] (KS.W01.frame z ++ vectorTape y))
      (Function.update (saved M y) 17 (vectorTape (Fin.cons (schurHead M y) y)))
      (padded.length + 1) := by
    convert KS.W15.RationalMultiply.clear_spec (20 : Fin 30)
      (work M y padded [] (KS.W01.frame z ++ vectorTape y)) using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
    funext j
    fin_cases j <;> simp [KS.W15.RationalMultiply.clearAfter, work, saved, vectorTape_cons, z]
  exact ((((h1.compose h2).compose h3).compose h4).compose h5).compose h6

end KS.W12.StoredWitnessLift

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_PivotWitnessMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W06.RationalSignClassifier.program_output _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W17.FixedPSD.withSaved_initial _root_.OAI.KS.W17.PivotHistory.restore_push _root_.OAI.KS.W17.schurWitnessLift_zero_pivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

theorem liftWitness_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1))
    (y : Fin n → ℚ) :
    RunSpec liftWitnessProgram (parentState saved M y)
      (Function.update (parentState saved M y) 17 (liftedTape M y))
      (KS.W12.StoredWitnessLift.ticks M y) := by
  have h := KS.W12.StoredWitnessLift.full_spec M y
  rw [schurHead_eq] at h
  apply KS.W01.FixedPortRunSpec.lift_runSpec
    KS.W12.StoredWitnessLift.program witnessPorts (KS.W12.StoredWitnessLift.saved M y)
    (Function.update (KS.W12.StoredWitnessLift.saved M y) 17 (liftedTape M y)) _ _ _ h
  · intro i; fin_cases i <;> simp [parentState, state, witnessPorts, KS.W12.StoredWitnessLift.saved]
  · intro i; fin_cases i <;> simp [parentState, state, witnessPorts, KS.W12.StoredWitnessLift.saved,
      Function.update]
  · intro j hj
    have hj17 : j ≠ 17 := by simpa [witnessPorts] using hj 17
    simp [Function.update, hj17]

theorem replay_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1))
    (y : Fin n → ℚ) :
    RunSpec replayProgram (parentState saved M y)
      (state saved [] [] [] (liftedTape M y)) (replayTicks M y) := by
  let b := Function.update (parentState saved M y) 17 (liftedTape M y)
  let c := Function.update (state saved [] [] [] []) 17 (liftedTape M y)
  have h1 := liftWitness_spec saved M y
  have h2 := KS.W04.CleanRationalCompare.clearList_spec (17 : Fin 35) [26,31,23] b
  have he : KS.W04.CleanRationalCompare.clearListState [26,31,23] b = c := by
    funext j; fin_cases j <;>
      simp [KS.W04.CleanRationalCompare.clearListState_apply, b, c, parentState, state, Function.update]
  have ht : KS.W04.CleanRationalCompare.clearListTicks [26,31,23] b =
      KS.W12.StoredWitnessLift.inputLength M y + 4 := by
    simp [KS.W04.CleanRationalCompare.clearListTicks, KS.W04.CleanRationalCompare.clearState,
      b, parentState, state, KS.W12.StoredWitnessLift.inputLength]
    omega
  rw [he, ht] at h2
  have h3 := KS.W07.WireAppend.spec (17 : Fin 35) 23 33 (by decide) (by decide) (by decide) c rfl
  have he3 : KS.W07.WireAppend.after 17 23 c = state saved [] [] [] (liftedTape M y) := by
    funext j; fin_cases j <;> simp [KS.W07.WireAppend.after, c, state]
  rw [he3] at h3
  have h := (h1.compose h2).compose h3
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (simp [replayProgram, replayTicks, witnessCleanup, c])
  omega

theorem popReplay_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1))
    (y : Fin n → ℚ) :
    RunSpec popReplayProgram
      (state (savedFrame (Computability.encodeNat (n+1)) (KS.W08.denseMatrixTape M) ++ saved)
        [] [] [] (KS.W12.RowDot.vectorTape y))
      (state saved [] [] [] (liftedTape M y))
      ((9 * (Computability.encodeNat (n+1)).length + 3 * (KS.W08.denseMatrixTape M).length + 7) +
        replayTicks M y) :=
  (restore_spec saved (Computability.encodeNat (n+1)) (KS.W08.denseMatrixTape M)
    (KS.W12.RowDot.vectorTape y)).compose (replay_spec saved M y)

end KS.W17.FixedPSD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotReplayLoop
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationMachine.input_port _root_.OAI.KS.W03.MultiplicationMachine.output_port _root_.OAI.KS.W03.MultiplicationMachine.stack_count _root_.OAI.KS.W03.MultiplicationMachine.state_count _root_.OAI.KS.W06.RationalSignClassifier.program_output _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W17.FixedPSD.withSaved_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

theorem restore_step_empty (wire : List Bool) (coin : Bool) :
    restoreAllProgram.toMachine.step (restoreConfig (state [] [] [] [] wire)) coin =
      ⟨none, state [] [] [] [] wire⟩ := by
  change (KS.W29.FixedLoop.loop popReplayProgram replayGuard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState popReplayProgram), _⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  apply congrArg₂ Config.mk
  · simp [KS.W29.FixedLoop.guardInstruction, replayGuard, state, observedHeads, KS.W29.topCode]
    rfl
  · funext j
    simp [KS.W29.FixedLoop.guardInstruction, replayGuard, Instruction.action, KS.W29.StackAction.apply]

theorem restore_step_nonempty (saved wire : List Bool) (hne : saved ≠ []) (coin : Bool) :
    restoreAllProgram.toMachine.step (restoreConfig (state saved [] [] [] wire)) coin =
      KS.W29.FixedLoop.liftBody popReplayProgram
        ⟨some popReplayProgram.initial, state saved [] [] [] wire⟩ := by
  change (KS.W29.FixedLoop.loop popReplayProgram replayGuard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState popReplayProgram), _⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  cases saved with
  | nil => exact (hne rfl).elim
  | cons b bs =>
    cases b <;> apply congrArg₂ Config.mk
    all_goals
      simp [KS.W29.FixedLoop.guardInstruction, replayGuard, state, observedHeads, KS.W29.topCode,
        Instruction.action, KS.W29.StackAction.apply] <;> rfl

theorem run_restoreAll {n N : ℕ} (h : PivotHistory n N) (y : Fin n → ℚ)
    (bits : List Bool) (hlen : restoreTicks h y ≤ bits.length) :
    restoreAllProgram.toMachine.run
      (restoreConfig (state (historyTape h) [] [] [] (KS.W12.RowDot.vectorTape y))) bits =
      ⟨none, state [] [] [] [] (KS.W12.RowDot.vectorTape (h.restore y))⟩ := by
  induction h generalizing bits with
  | nil n =>
    cases bits with
    | nil => simp [restoreTicks] at hlen
    | cons coin bs =>
      simp only [historyTape]
      erw [Machine.run.eq_2, restore_step_empty, Machine.run_halted _ _ rfl]
      rfl
  | @push n N M rest ih =>
    let A := DenseRatMatrix.ofMatrix M
    have hb := popReplay_spec (historyTape rest) A y
    have he : liftedTape A y = KS.W12.RowDot.vectorTape (schurWitnessLift M y) := by
      simp [liftedTape, A]
    rw [he] at hb
    have hne : historyTape (PivotHistory.push M rest) ≠ [] := by
      intro hnil
      have hh := congrArg List.length hnil
      simp only [historyTape, List.length_append, savedFrame, KS.W01.length_frame, List.length_nil] at hh
      omega
    cases bits with
    | nil => simp [restoreTicks] at hlen
    | cons coin bs =>
      have hbody : (9 * (Computability.encodeNat (n+1)).length +
          3 * (KS.W08.denseMatrixTape A).length + 7) + replayTicks A y ≤ bs.length := by
        simp only [restoreTicks, List.length_cons] at hlen
        change 1 + _ + _ ≤ _ at hlen
        dsimp only [A]
        omega
      obtain ⟨remaining, hremaining, hreturn⟩ := hb.loop_body_then replayGuard bs hbody
      dsimp only [A] at hremaining
      erw [Machine.run.eq_2, restore_step_nonempty _ _ hne]
      change (KS.W29.FixedLoop.loop popReplayProgram replayGuard).toMachine.run _ bs = _
      dsimp only [A] at hreturn
      simp only [historyTape]
      erw [hreturn]
      have hr : restoreTicks rest (schurWitnessLift M y) ≤ remaining.length := by
        simp only [restoreTicks, List.length_cons] at hlen
        omega
      exact ih (schurWitnessLift M y) remaining hr

theorem restoreAll_spec {n N : ℕ} (h : PivotHistory n N) (y : Fin n → ℚ) :
    RunSpec restoreAllProgram (state (historyTape h) [] [] [] (KS.W12.RowDot.vectorTape y))
      (state [] [] [] [] (KS.W12.RowDot.vectorTape (h.restore y))) (restoreTicks h y) := by
  intro bits hb
  exact run_restoreAll h y bits hb.ge

end KS.W17.FixedPSD

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurOperands
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.sumBudget_cons _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W17.FixedPSD.withSaved_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W07.SchurOperands
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open SchurReadStage

theorem collect_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (i j : Fin n) (s : Fin 32 → List Bool) (hw : WorkClear s)
    (hm : s 31 = KS.W08.denseMatrixTape M) (hd : s 26 = Computability.encodeNat (n+1))
    (hr : s 27 = Computability.encodeNat i.succ.val)
    (hc : s 28 = Computability.encodeNat j.succ.val)
    (hz : s 29 = []) (he : ∀ k : Fin 4, s (destination k) = []) :
    RunSpec collect s
      (operands s
        (KS.W01.encodeRat (DenseRatMatrix.decode M i.succ j.succ))
        (KS.W01.encodeRat (DenseRatMatrix.decode M i.succ 0))
        (KS.W01.encodeRat (DenseRatMatrix.decode M 0 j.succ))
        (KS.W01.encodeRat (DenseRatMatrix.decode M 0 0)))
      (readBudget M B i j s) := by
  let x := KS.W01.encodeRat (DenseRatMatrix.decode M i.succ j.succ)
  let a := KS.W01.encodeRat (DenseRatMatrix.decode M i.succ 0)
  let b := KS.W01.encodeRat (DenseRatMatrix.decode M 0 j.succ)
  let c := KS.W01.encodeRat (DenseRatMatrix.decode M 0 0)
  let s₁ := Function.update s (destination 0) x
  let s₂ := Function.update s₁ (destination 1) a
  let s₃ := Function.update s₂ (destination 2) b
  have hw₁ : WorkClear s₁ := workClear_update s hw 0 x
  have hw₂ : WorkClear s₂ := workClear_update s₁ hw₁ 1 a
  have hw₃ : WorkClear s₃ := workClear_update s₂ hw₂ 2 b
  have h₁ := SchurReadStage.full_spec M B hnum hden i.succ j.succ s hw hm hd
    true true hr hc 0 (he 0)
  have h₂ := SchurReadStage.full_spec M B hnum hden i.succ 0 s₁ hw₁
    (by simpa [s₁,destination] using hm) (by simpa [s₁,destination] using hd)
    true false (by simpa [s₁,destination,rowSource] using hr)
    (by simpa [s₁,destination,colSource,Computability.encodeNat,Computability.encodeNum] using hz) 1 (by simpa [s₁,destination] using he 1)
  have h₃ := SchurReadStage.full_spec M B hnum hden 0 j.succ s₂ hw₂
    (by simpa [s₂,s₁,destination] using hm) (by simpa [s₂,s₁,destination] using hd)
    false true (by simpa [s₂,s₁,destination,rowSource,Computability.encodeNat,Computability.encodeNum] using hz)
    (by simpa [s₂,s₁,destination,colSource] using hc) 2 (by simpa [s₂,s₁,destination] using he 2)
  have h₄ := SchurReadStage.full_spec M B hnum hden 0 0 s₃ hw₃
    (by simpa [s₃,s₂,s₁,destination] using hm) (by simpa [s₃,s₂,s₁,destination] using hd)
    false false (by simpa [s₃,s₂,s₁,destination,rowSource,Computability.encodeNat,Computability.encodeNum] using hz)
    (by simpa [s₃,s₂,s₁,destination,colSource,Computability.encodeNat,Computability.encodeNum] using hz) 3
    (by simpa [s₃,s₂,s₁,destination] using he 3)
  have h := h₁.compose (h₂.compose (h₃.compose h₄))
  simpa [collect,readBudget,prepareTicks,rowSource,colSource,s₁,s₂,s₃,destination,
    x,a,b,c,operands,Nat.add_assoc] using h

theorem scalar_spec (s : Fin 32 → List Bool) (hw : WorkClear s)
    (he : ∀ k : Fin 4, s (destination k) = []) (x a b c : ℚ) :
    RunSpec scalar (operands s (KS.W01.encodeRat x) (KS.W01.encodeRat a)
      (KS.W01.encodeRat b) (KS.W01.encodeRat c))
      (Function.update s 10 (KS.W01.encodeRat (x-a*b/c)))
      (SchurCellMachine.ticks x a b c) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ scalarPorts _ _ _ _ _
    (SchurCellMachine.full_spec x a b c)
  · intro k
    fin_cases k <;> simp [scalarPorts,operands,SchurCellMachine.workspace]
    all_goals exact hw _ (by decide)
  · intro k
    fin_cases k <;> simp [scalarPorts,SchurCellMachine.workspace]
    all_goals first | exact hw _ (by decide) | exact he 0 | exact he 1 | exact he 2 | exact he 3
  · intro k hk
    have hlt : ¬ k.val < 23 := by
      intro h
      exact hk ⟨k.val,h⟩ (Fin.ext rfl)
    have h10 : k ≠ 10 := by intro h; subst k; omega
    have h19 : k ≠ 19 := by intro h; subst k; omega
    have h20 : k ≠ 20 := by intro h; subst k; omega
    have h21 : k ≠ 21 := by intro h; subst k; omega
    have h22 : k ≠ 22 := by intro h; subst k; omega
    simp [operands,Function.update_of_ne,h10,h19,h20,h21,h22]

theorem full_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (i j : Fin n) (s : Fin 32 → List Bool) (hw : WorkClear s)
    (hm : s 31 = KS.W08.denseMatrixTape M) (hd : s 26 = Computability.encodeNat (n+1))
    (hr : s 27 = Computability.encodeNat i.succ.val)
    (hc : s 28 = Computability.encodeNat j.succ.val)
    (hz : s 29 = []) (he : ∀ k : Fin 4, s (destination k) = []) :
    RunSpec program s
      (Function.update s 10 (KS.W01.encodeRat (KS.W17.schurTail (DenseRatMatrix.decode M) i j)))
      (readBudget M B i j s + SchurCellMachine.ticks
        (DenseRatMatrix.decode M i.succ j.succ) (DenseRatMatrix.decode M i.succ 0)
        (DenseRatMatrix.decode M 0 j.succ) (DenseRatMatrix.decode M 0 0)) := by
  exact (collect_spec M B hnum hden i j s hw hm hd hr hc hz he).compose
    (scalar_spec s hw he _ _ _ _)

end KS.W07.SchurOperands

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurEntryMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurEntryMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem full_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (i j : Fin n) (s : Fin 32 → List Bool) (hw : SchurReadStage.WorkClear s)
    (hm : s 31 = KS.W08.denseMatrixTape M) (hd : s 26 = Computability.encodeNat (n+1))
    (hr : s 27 = Computability.encodeNat i.succ.val)
    (hc : s 28 = Computability.encodeNat j.succ.val)
    (hz : s 29 = []) (he : ∀ k : Fin 4, s (SchurReadStage.destination k) = []) :
    RunSpec program s
      (Function.update s 23
        ((KS.W01.frame (KS.W01.encodeRat (KS.W17.schurTail (DenseRatMatrix.decode M) i j))).reverse ++ s 23))
      ((SchurOperands.readBudget M B i j s + SchurCellMachine.ticks
        (DenseRatMatrix.decode M i.succ j.succ) (DenseRatMatrix.decode M i.succ 0)
        (DenseRatMatrix.decode M 0 j.succ) (DenseRatMatrix.decode M 0 0)) +
        (6*KS.W01.ratLength (KS.W17.schurTail (DenseRatMatrix.decode M) i j)+5)) :=
  (SchurOperands.full_spec M B hnum hden i j s hw hm hd hr hc hz he).compose
    (append_spec s (hw _ (by decide)) (hw _ (by decide)) (hw _ (by decide)) _)

end KS.W07.SchurEntryMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_SchurLoopState
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.sumBudget_cons _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W17.FixedPSD.withSaved_initial _root_.OAI.KS.W17.schurEntryExpr_eval _root_.OAI.KS.W17.schurTail_zero_pivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurLoopState
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem column_body_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (i j : Fin n) (rows cols : ℕ) :
    RunSpec SchurTableMachine.columnBody (columnState M i.val j.val rows cols)
      (columnState M i.val (j.val+1) rows cols) (columnTicks M B i j rows cols) := by
  let s := columnState M i.val j.val rows cols
  let wire := KS.W01.frame (KS.W01.encodeRat (KS.W17.schurTail (DenseRatMatrix.decode M) i j))
  have he := SchurEntryMachine.full_spec M B hnum hden i j s
    (column_workClear M _ _ _ _) rfl rfl rfl rfl rfl
    (by intro k; fin_cases k <;> rfl)
  let mid := Function.update s 23 (wire.reverse ++ s 23)
  have hinc := SchurCounters.increment_spec SchurTableMachine.columnIncrementPorts mid
    (j.val+1) rfl rfl rfl
  have hprefix : «prefix» M (i.val*n+(j.val+1)) =
      «prefix» M (i.val*n+j.val) ++ wire := by
    simpa only [Nat.add_assoc] using prefix_step M i j
  have hout : Function.update mid 28 (Computability.encodeNat (j.val+1+1)) =
      columnState M i.val (j.val+1) rows cols := by
    funext k
    fin_cases k <;> simp [mid,s,wire,columnState,hprefix,List.reverse_append,Nat.add_assoc]
  change RunSpec (SchurCounters.incrementProgram SchurTableMachine.columnIncrementPorts) mid
    (Function.update mid 28 (Computability.encodeNat (j.val+1+1))) _ at hinc
  rw [hout] at hinc
  exact he.compose hinc

end KS.W07.SchurLoopState

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurColumnLoop
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationMachine.input_port _root_.OAI.KS.W03.MultiplicationMachine.output_port _root_.OAI.KS.W03.MultiplicationMachine.stack_count _root_.OAI.KS.W03.MultiplicationMachine.state_count _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W06.RationalSignClassifier.program_output _root_.OAI.KS.W12.FixedDot.machine_inputStack _root_.OAI.KS.W12.FixedDot.machine_outputStack _root_.OAI.KS.W12.FixedDot.machine_stackCount _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil _root_.OAI.KS.W17.FixedPSD.withSaved_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurLoopState
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem columnTicks_le {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (i j : Fin n) (rows cols : ℕ) : columnTicks M B i j rows cols ≤ columnBudget n B := by
  have hlen (q : ℚ) (hn : q.num.natAbs ≤ 2^B) (hd : q.den ≤ 2^B) :
      KS.W01.ratLength q ≤ 4*B+7 := by
    have h := KS.W01.ratLength_le_of_parts q B B hn hd
    omega
  have lx := hlen _ (hnum i.succ j.succ) (hden i.succ j.succ)
  have la := hlen _ (hnum i.succ 0) (hden i.succ 0)
  have lb := hlen _ (hnum 0 j.succ) (hden 0 j.succ)
  have lc := hlen _ (hnum 0 0) (hden 0 0)
  have hs := SchurCellMachine.ticks_le_cellBudget
    (DenseRatMatrix.decode M i.succ j.succ) (DenseRatMatrix.decode M i.succ 0)
    (DenseRatMatrix.decode M 0 j.succ) (DenseRatMatrix.decode M 0 0) B
    ⟨hnum i.succ j.succ,hden i.succ j.succ⟩ ⟨hnum i.succ 0,hden i.succ 0⟩
    ⟨hnum 0 j.succ,hden 0 j.succ⟩ ⟨hnum 0 0,hden 0 0⟩
  have hq := SchurTable.entry_parts_le M B hnum hden i j
  have lq := KS.W01.ratLength_le_of_parts _ (4*B+3) (4*B+3) hq.1 hq.2
  have rawLength (t : ℕ) : (Computability.encodeNat t).length ≤ t := by
    change KS.W01.natPayloadLength t ≤ t
    rw [KS.W01.natPayloadLength_eq_size]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have ln := rawLength (n+1)
  have li : (Computability.encodeNat (i.val+1)).length ≤ n+1 :=
    (rawLength (i.val+1)).trans (by omega)
  have lj : (Computability.encodeNat (j.val+1)).length ≤ n+1 :=
    (rawLength (j.val+1)).trans (by omega)
  have hread : 4096*(n+2)^2*(B+1) = 4*(1024*(n+2)^2*(B+1)) := by ring
  unfold columnTicks SchurOperands.readBudget SchurReadStage.prepareTicks columnBudget
  rw [hread]
  simp only [columnState,SchurReadStage.rowSource,SchurReadStage.colSource,
    Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Fin.isValue,Fin.reduceEq,List.length_nil]
  omega

theorem column_body_polynomial {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (i j : Fin n) (rows cols : ℕ) :
    RunSpec SchurTableMachine.columnBody (columnState M i.val j.val rows cols)
      (columnState M i.val (j.val+1) rows cols) (columnBudget n B) :=
  (column_body_spec M B hnum hden i j rows cols).mono (columnTicks_le M B hnum hden i j rows cols)

theorem run_columns {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (i : Fin n) (rows start count : ℕ) (hcount : start+count=n)
    (bits : List Bool) (hlen : count*(columnBudget n B+1)+1 ≤ bits.length) :
    SchurTableMachine.columnLoop.toMachine.run
      ⟨some SchurTableMachine.columnLoop.initial,columnState M i.val start rows count⟩ bits =
      ⟨none,columnState M i.val n rows 0⟩ := by
  induction count generalizing start bits with
  | zero =>
    have hstart : start=n := by omega
    subst start
    cases bits with
    | nil => simp at hlen
    | cons coin rest =>
      have hg : SchurTableMachine.columnLoop.toMachine.step
          ⟨some SchurTableMachine.columnLoop.initial,columnState M i.val n rows 0⟩ coin =
          ⟨none,columnState M i.val n rows 0⟩ := by
        simpa only [SchurTableMachine.columnLoop,KS.W29.FixedLoop.loop_initial] using
          SchurTableMachine.guard_empty SchurTableMachine.columnBody 25
            (columnState M i.val n rows 0) rfl coin
      rw [Machine.run,hg,Machine.run_halted _ _ rfl]
  | succ count ih =>
    have hstart : start<n := by omega
    let j : Fin n := ⟨start,hstart⟩
    cases bits with
    | nil => simp at hlen
    | cons coin rest =>
      have hb := column_body_polynomial M B hnum hden i j rows count
      have hr : columnBudget n B ≤ rest.length := by
        simp only [List.length_cons,Nat.succ_mul] at hlen
        omega
      obtain ⟨remaining,hremaining,hreturn⟩ := hb.loop_body_then
        (SchurTableMachine.guard 25) rest hr
      have hstep := SchurTableMachine.guard_cons SchurTableMachine.columnBody 25
        (columnState M i.val start rows (count+1)) (List.replicate count true)
        (by simp [columnState,List.replicate_succ]) coin
      rw [column_pop] at hstep
      simp only [SchurTableMachine.columnLoop,KS.W29.FixedLoop.loop_initial]
      rw [Machine.run,hstep,hreturn]
      have hnext : (start+1)+count=n := by omega
      have hnextlen : count*(columnBudget n B+1)+1 ≤ remaining.length := by
        simp only [List.length_cons,Nat.succ_mul] at hlen
        omega
      simpa only [SchurTableMachine.columnLoop,KS.W29.FixedLoop.loop_initial] using
        ih (start+1) hnext remaining hnextlen

theorem columns_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B) (i : Fin n) (rows : ℕ) :
    RunSpec SchurTableMachine.columnLoop (columnState M i.val 0 rows n)
      (columnState M i.val n rows 0) (n*(columnBudget n B+1)+1) := by
  intro bits hbits
  exact run_columns M B hnum hden i rows 0 n (by omega) bits hbits.ge

end KS.W07.SchurLoopState

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurRowLoop
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationMachine.input_port _root_.OAI.KS.W03.MultiplicationMachine.output_port _root_.OAI.KS.W03.MultiplicationMachine.stack_count _root_.OAI.KS.W03.MultiplicationMachine.state_count _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W06.RationalSignClassifier.program_output _root_.OAI.KS.W12.FixedDot.machine_inputStack _root_.OAI.KS.W12.FixedDot.machine_outputStack _root_.OAI.KS.W12.FixedDot.machine_stackCount _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil _root_.OAI.KS.W17.FixedPSD.withSaved_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurLoopState
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem row_body_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (i : Fin n) (rows : ℕ) :
    RunSpec SchurTableMachine.rowBody (rowState M i.val rows)
      (rowState M (i.val+1) rows) (rowTicks n B i.val) := by
  let s := rowState M i.val rows
  let u := Function.update s 25 (List.replicate n true)
  have hu := SchurDimension.unary_spec true s n rfl rfl rfl rfl rfl
  have hp := SchurCounters.push_spec (28 : Fin 32) true u
  have hone : Computability.encodeNat 1 = [true] := by decide
  have hstart : Function.update u 28 (true::u 28) = columnState M i.val 0 rows n := by
    funext k; fin_cases k <;> simp [u,s,columnState,rowState,hone]
  rw [hstart] at hp
  have hc := columns_spec M B hnum hden i rows
  let v := Function.update (columnState M i.val n rows 0) 28 []
  have hclear := KS.W15.RationalMultiply.clear_spec (28 : Fin 32)
    (columnState M i.val n rows 0)
  have hclearState : KS.W15.RationalMultiply.clearAfter 28
      (columnState M i.val n rows 0) = v := by
    funext k
    by_cases hk : k=28 <;> simp [KS.W15.RationalMultiply.clearAfter,v,hk]
  rw [hclearState] at hclear
  have hi := SchurCounters.increment_spec SchurTableMachine.rowIncrementPorts v
    (i.val+1) rfl rfl rfl
  have hout : Function.update v 27 (Computability.encodeNat (i.val+1+1)) =
      rowState M (i.val+1) rows := by
    funext k; fin_cases k <;> simp [v,columnState,rowState,Nat.add_mul]
  change RunSpec (SchurCounters.incrementProgram SchurTableMachine.rowIncrementPorts) v
    (Function.update v 27 (Computability.encodeNat (i.val+1+1))) _ at hi
  rw [hout] at hi
  exact hu.compose (hp.compose (hc.compose (hclear.compose hi)))

theorem row_body_polynomial {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (i : Fin n) (rows : ℕ) :
    RunSpec SchurTableMachine.rowBody (rowState M i.val rows)
      (rowState M (i.val+1) rows) (rowBudget n B) :=
  (row_body_spec M B hnum hden i rows).mono (rowTicks_le B i)

theorem run_rows {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (start count : ℕ) (hcount : start+count=n) (bits : List Bool)
    (hlen : count*(rowBudget n B+1)+1 ≤ bits.length) :
    SchurTableMachine.rowLoop.toMachine.run
      ⟨some SchurTableMachine.rowLoop.initial,rowState M start count⟩ bits =
      ⟨none,rowState M n 0⟩ := by
  induction count generalizing start bits with
  | zero =>
    have hstart : start=n := by omega
    subst start
    cases bits with
    | nil => simp at hlen
    | cons coin rest =>
      have hg : SchurTableMachine.rowLoop.toMachine.step
          ⟨some SchurTableMachine.rowLoop.initial,rowState M n 0⟩ coin =
          ⟨none,rowState M n 0⟩ := by
        simpa only [SchurTableMachine.rowLoop,KS.W29.FixedLoop.loop_initial] using
          SchurTableMachine.guard_empty SchurTableMachine.rowBody 24
            (rowState M n 0) rfl coin
      rw [Machine.run,hg,Machine.run_halted _ _ rfl]
  | succ count ih =>
    have hstart : start<n := by omega
    let i : Fin n := ⟨start,hstart⟩
    cases bits with
    | nil => simp at hlen
    | cons coin rest =>
      have hb := row_body_polynomial M B hnum hden i count
      have hr : rowBudget n B ≤ rest.length := by
        simp only [List.length_cons,Nat.succ_mul] at hlen
        omega
      obtain ⟨remaining,hremaining,hreturn⟩ := hb.loop_body_then
        (SchurTableMachine.guard 24) rest hr
      have hstep := SchurTableMachine.guard_cons SchurTableMachine.rowBody 24
        (rowState M start (count+1)) (List.replicate count true)
        (by simp [rowState,List.replicate_succ]) coin
      rw [row_pop] at hstep
      simp only [SchurTableMachine.rowLoop,KS.W29.FixedLoop.loop_initial]
      rw [Machine.run,hstep,hreturn]
      have hnext : (start+1)+count=n := by omega
      have hnextlen : count*(rowBudget n B+1)+1 ≤ remaining.length := by
        simp only [List.length_cons,Nat.succ_mul] at hlen
        omega
      simpa only [SchurTableMachine.rowLoop,KS.W29.FixedLoop.loop_initial] using
        ih (start+1) hnext remaining hnextlen

theorem rows_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B) :
    RunSpec SchurTableMachine.rowLoop (rowState M 0 n) (rowState M n 0)
      (n*(rowBudget n B+1)+1) := by
  intro bits hbits
  exact run_rows M B hnum hden 0 n (by omega) bits hbits.ge

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

theorem finishTicks_le {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B) :
    finishTicks M ≤ n+5+3*(n*n*(32*B+39)) := by
  have hp := SchurTable.entry_parts_le M B hnum hden
  have ht := KS.W08.denseMatrixTape_length_le (tailMatrix M) (4*B+3)
    (fun i j => by simpa [tailMatrix] using (hp i j).1)
    (fun i j => by simpa [tailMatrix] using (hp i j).2)
  have ld : (Computability.encodeNat (n+1)).length ≤ n+1 := by
    change KS.W01.natPayloadLength (n+1) ≤ n+1
    rw [KS.W01.natPayloadLength_eq_size]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hexp : 8*(4*B+3)+15 = 32*B+39 := by omega
  rw [hexp] at ht
  unfold finishTicks
  omega

theorem full_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B) :
    RunSpec program (inputState M) (outputState M) (totalTicks n B) := by
  exact ((initialize_spec M).mono (initializeTicks_le n)).compose
    ((rows_spec M B hnum hden).compose ((finish_spec M).mono (finishTicks_le M B hnum hden)))

end KS.W07.SchurTableMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_PivotDescentMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil _root_.OAI.KS.W17.FixedPSD.withSaved_initial _root_.OAI.KS.W17.schurTail_zero_pivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

theorem schur_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b) :
    RunSpec schurProgram (matrixState saved M)
      (state saved (Computability.encodeNat (n+1)) (KS.W08.denseMatrixTape M)
        (Computability.encodeNat n) (KS.W08.denseMatrixTape (child M)))
      (KS.W07.SchurTableMachine.totalTicks n b) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec KS.W07.SchurTableMachine.program schurPorts
    (KS.W07.SchurTableMachine.inputState M) (KS.W07.SchurTableMachine.outputState M) _ _ _
    (KS.W07.SchurTableMachine.full_spec M b hnum hden)
  · intro i; fin_cases i <;> simp [matrixState,state,schurPorts,KS.W07.SchurTableMachine.inputState]
  · intro i; fin_cases i <;> simp [state,schurPorts,child,KS.W07.SchurTableMachine.outputState]
  · intro j hj
    have h23 : j ≠ 23 := by simpa [schurPorts] using hj 23
    have h30 : j ≠ 30 := by simpa [schurPorts] using hj 30
    simp [matrixState,state,h23,h30]

theorem fullDescend_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b) :
    RunSpec fullDescendProgram (matrixState saved M)
      (matrixState (savedFrame (Computability.encodeNat (n+1)) (KS.W08.denseMatrixTape M) ++ saved) (child M))
      (descentTicks M b) :=
  (schur_spec saved M b hnum hden).compose
    (descend_spec saved (Computability.encodeNat (n+1)) (KS.W08.denseMatrixTape M)
      (Computability.encodeNat n) (KS.W08.denseMatrixTape (child M)))

end KS.W17.FixedPSD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotRowRead
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W17.FixedPSD.withSaved_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.PivotRowRead
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07
open KS.W07.SchurReadStage

theorem full_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b)
    (j : Fin (n+1)) (before : Fin 32 → List Bool) (hw : WorkClear before)
    (hm : before 31 = KS.W08.denseMatrixTape M)
    (hd : before 26 = Computability.encodeNat (n+1))
    (hj : before 28 = Computability.encodeNat j.val) :
    RunSpec program before (Function.update before 0 (KS.W01.encodeRat (DenseRatMatrix.decode M 0 j)))
      ((2*(Computability.encodeNat j.val).length+2) +
        (2*(Computability.encodeNat (n+1)).length+2) + 1024*(n+2)^2*(b+1)) := by
  have h0 := hw 0 (by decide)
  have h1 := hw 1 (by decide)
  have h2 := hw 2 (by decide)
  have h16 := hw 16 (by decide)
  have hc := copy_spec (28 : Fin 32) 0 (by decide) (by decide) (by decide) before h0 h16
  rw [hj] at hc
  have hd2 := copy_spec (26 : Fin 32) 2 (by decide) (by decide) (by decide)
    (Function.update before 0 (Computability.encodeNat j.val))
    (by simpa using h2) (by simpa using h16)
  simp only [Function.update_of_ne (show (26 : Fin 32) ≠ 0 by decide), hd] at hd2
  have hr := reader_spec M b hnum hden 0 j before hw hm
  have he : Function.update (Function.update before 0 (Computability.encodeNat j.val)) 2
      (Computability.encodeNat (n+1)) =
      readPrepared before (Computability.encodeNat j.val) (Computability.encodeNat (0 : ℕ))
        (Computability.encodeNat (n+1)) := by
    funext k
    fin_cases k <;> simp [readPrepared, h1, Computability.encodeNat, Computability.encodeNum, Function.update]
  rw [he] at hd2
  exact (hc.compose hd2).compose hr

end KS.W17.PivotRowRead

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotRowClassify
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.sumBudget_cons _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W17.FixedPSD.withSaved_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.PivotRowClassify
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07
open KS.W07.SchurReadStage

theorem full_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b)
    (j : Fin (n+1)) (before : Fin 32 → List Bool) (hw : WorkClear before)
    (hm : before 31 = KS.W08.denseMatrixTape M)
    (hd : before 26 = Computability.encodeNat (n+1))
    (hj : before 28 = Computability.encodeNat j.val) (hf : before 29 = []) :
    RunSpec program before
      (Function.update before 29 (KS.W06.RationalSignClassifier.outputCode (DenseRatMatrix.decode M 0 j)))
      (ticks M b j) := by
  let q := DenseRatMatrix.decode M 0 j
  let code := KS.W06.RationalSignClassifier.outputCode q
  have hread := PivotRowRead.full_spec M b hnum hden j before hw hm hd hj
  have hclass : RunSpec classifier (Function.update before 0 (KS.W01.encodeRat q))
      (Function.update before 9 code) (256*(KS.W01.ratLength q+1)) := by
    apply KS.W01.FixedPortRunSpec.lift_runSpec
      KS.W06.RationalSignClassifier.program classifierPorts
      (KS.W06.SingleRationalParser.inputState (KS.W01.encodeRat q))
      (KS.W06.RationalSignClassifier.outputState q) _ _ _
      (KS.W06.RationalSignClassifier.canonical_spec q)
    · intro i
      have hi : before (classifierPorts i) = [] := hw _ (by have := i.isLt; simp [classifierPorts]; omega)
      fin_cases i <;> simp_all [classifierPorts, KS.W06.SingleRationalParser.inputState, Function.update]
    · intro i
      have hi : before (classifierPorts i) = [] := hw _ (by have := i.isLt; simp [classifierPorts]; omega)
      fin_cases i <;> simp_all [classifierPorts, KS.W06.RationalSignClassifier.outputState,
        Function.update, code]
    · intro i hi
      have h0 : i ≠ 0 := by simpa [classifierPorts] using hi 0
      have h9 : i ≠ 9 := by simpa [classifierPorts] using hi 9
      simp [Function.update, h0, h9]
  have hmoving := KS.W07.WireAppend.spec (9 : Fin 32) 29 16 (by decide) (by decide) (by decide)
    (Function.update before 9 code) (by simpa using hw 16 (by decide))
  have he : KS.W07.WireAppend.after 9 29 (Function.update before 9 code) =
      Function.update before 29 code := by
    have h9 := hw 9 (by decide)
    funext i; fin_cases i <;> simp [KS.W07.WireAppend.after, Function.update, hf, h9]
  rw [he] at hmoving
  exact (hread.compose hclass).compose hmoving

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

theorem full_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b)
    (j : Fin (n+1)) (before : Fin 32 → List Bool) (hw : WorkClear before)
    (hm : before 31 = KS.W08.denseMatrixTape M) (hd : before 26 = Computability.encodeNat (n+1))
    (hj : before 28 = Computability.encodeNat j.val) (hf : before 24 = []) (h29 : before 29 = []) :
    RunSpec program before (after before (DenseRatMatrix.decode M 0 j) j.val) (ticks M b j) :=
  (PivotRowClassify.full_spec M b hnum hden j before hw hm hd hj h29).compose
    (branch_spec before (DenseRatMatrix.decode M 0 j) j.val (hw 0 (by decide)) (hw 1 (by decide)) hf hj h29)

end KS.W17.PivotRowBody

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotRowLoop
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W12.FixedDot.machine_inputStack _root_.OAI.KS.W12.FixedDot.machine_outputStack _root_.OAI.KS.W12.FixedDot.machine_stackCount _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil _root_.OAI.KS.W15.RationalMultiply.machine_inputStack _root_.OAI.KS.W15.RationalMultiply.machine_outputStack _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W17.FixedPSD.withSaved_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W17.PivotRowLoop
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

theorem body_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (b a k : ℕ) (ha : a < n+1)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b) :
    RunSpec PivotRowBody.program (state M a k false)
      (if entry M a = 0 then state M (a+1) k false else state M a k true) (entryTicks M b a) := by
  have hw : KS.W07.SchurReadStage.WorkClear (state M a k false) := by
    intro j hj
    have h24 : j ≠ 24 := by intro h; subst j; omega
    have h25 : j ≠ 25 := by intro h; subst j; omega
    have h26 : j ≠ 26 := by intro h; subst j; omega
    have h28 : j ≠ 28 := by intro h; subst j; omega
    have h31 : j ≠ 31 := by intro h; subst j; omega
    simp [state,h24,h25,h26,h28,h31]
  have h := PivotRowBody.full_spec M b hnum hden ⟨a,ha⟩ (state M a k false) hw rfl rfl rfl rfl rfl
  convert h using 1
  · by_cases hz : entry M a = 0
    · have hq : DenseRatMatrix.decode M 0 ⟨a,ha⟩ = 0 := by simpa [entry,ha] using hz
      simp only [hz, ite_true, if_true, PivotRowBody.after, hq]
      funext j; fin_cases j <;> simp [state, Function.update]
    · have hq : DenseRatMatrix.decode M 0 ⟨a,ha⟩ ≠ 0 := by simpa [entry,ha] using hz
      simp only [hz, ite_false, if_false, PivotRowBody.after, hq]
      funext j; fin_cases j <;> simp [state, Function.update]
  · simp [entryTicks,ha]

theorem run_scan {n : ℕ} (M : DenseRatMatrix (n+1)) (b a k : ℕ)
    (hbound : a+k ≤ n+1)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b)
    (bits : List Bool) (hlen : ticks M b a k ≤ bits.length) :
    program.toMachine.run (config (state M a k false)) bits =
      let o := outcome M a k
      ⟨none,state M o.index o.remaining o.found⟩ := by
  induction k generalizing a bits with
  | zero =>
    cases bits with
    | nil => simp [ticks] at hlen
    | cons coin bs =>
      erw [Machine.run.eq_2,step_empty,Machine.run_halted _ _ rfl]
      rfl
  | succ k ih =>
    have ha : a<n+1 := by omega
    have hb := body_spec M b a k ha hnum hden
    cases bits with
    | nil => simp [ticks] at hlen
    | cons coin bs =>
      have ht : entryTicks M b a ≤ bs.length := by simp only [ticks,List.length_cons] at hlen; omega
      obtain ⟨remaining,hr,hreturn⟩ := hb.loop_body_then guard bs ht
      erw [Machine.run.eq_2,step_call]
      change (KS.W29.FixedLoop.loop PivotRowBody.program guard).toMachine.run _ bs = _
      erw [hreturn]
      by_cases hz : entry M a = 0
      · have hremaining : ticks M b (a+1) k ≤ remaining.length := by
          simp only [ticks,hz,ite_true, if_true,List.length_cons] at hlen
          omega
        have hi := ih (a+1) (by omega) remaining hremaining
        simp only [hz,ite_true, if_true,outcome] at hi ⊢
        exact hi
      · have hn : 1 ≤ remaining.length := by
          simp only [ticks,hz,ite_false, if_false,List.length_cons] at hlen
          omega
        simp only [hz,ite_false, if_false,outcome]
        cases remaining with
        | nil => simp at hn
        | cons c cs =>
          change program.toMachine.run (config (state M a k true)) (c :: cs) = _
          erw [Machine.run.eq_2,step_found,Machine.run_halted _ _ rfl]

end KS.W17.PivotRowLoop

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotRowInitialize
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.PivotRowLoop
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

theorem offDiagonal_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b) :
    RunSpec offDiagonalProgram (initial M)
      (state M (outcome M 1 n).index (outcome M 1 n).remaining (outcome M 1 n).found)
      (initializeTicks n + ticks M b 1 n) := by
  have h : RunSpec program (state M 1 n false)
      (state M (outcome M 1 n).index (outcome M 1 n).remaining (outcome M 1 n).found)
      (ticks M b 1 n) := by
    intro bits hb
    exact run_scan M b 1 n (by omega) hnum hden bits hb.ge
  exact (initialize_spec M).compose h

end KS.W17.PivotRowLoop

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotRowFinish
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W17.PivotRowLoop
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

theorem complete_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b) :
    RunSpec completeProgram (initial M)
      (finished M (outcome M 1 n).index (outcome M 1 n).found)
      (initializeTicks n+ticks M b 1 n+finishTicks (outcome M 1 n).index (outcome M 1 n).remaining) :=
  (offDiagonal_spec M b hnum hden).compose
    (finish_spec M (outcome M 1 n).index (outcome M 1 n).remaining (outcome M 1 n).found)

end KS.W17.PivotRowLoop

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotDecisionMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W07.SchurLoopState.prefix_zero _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil _root_.OAI.KS.W17.FixedPSD.withSaved_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W17.PivotDecision
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

theorem full_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b) :
    RunSpec program (PivotRowLoop.initial M) (result M) (ticks M b) := by
  let s := PivotRowLoop.initial M
  let q := DenseRatMatrix.decode M 0 0
  let t := Function.update s 29 (KS.W06.RationalSignClassifier.outputCode q)
  have hw : KS.W07.SchurReadStage.WorkClear s := by
    intro j hj
    have h24 : j ≠ 24 := by intro h; subst j; omega
    have h25 : j ≠ 25 := by intro h; subst j; omega
    have h26 : j ≠ 26 := by intro h; subst j; omega
    have h28 : j ≠ 28 := by intro h; subst j; omega
    have h31 : j ≠ 31 := by intro h; subst j; omega
    simp [s,PivotRowLoop.initial,PivotRowLoop.state,h24,h25,h26,h28,h31]
  have hr := PivotRowClassify.full_spec M b hnum hden 0 s hw rfl rfl rfl rfl
  by_cases hz : q=0
  · have hc := KS.W04.CleanRationalCompare.clear_spec (29 : Fin 32) t
    have he : KS.W04.CleanRationalCompare.clearState 29 t = s := by
      funext j; fin_cases j <;> simp [KS.W04.CleanRationalCompare.clearState,t,s,
        PivotRowLoop.initial,PivotRowLoop.state]
    rw [he] at hc
    have hrow := PivotRowLoop.complete_spec M b hnum hden
    have hzrun := hc.compose hrow
    have hs : ∀ coin, select (observedHeads
        (⟨some (KS.W29.FixedBranch.start zeroProgram returnProgram),t⟩ :
          Config 32 (zeroProgram.states+returnProgram.states+1))) coin =
        ⟨.left,KS.W06.RationalCompare.stayActions 32⟩ := by
      intro coin; simp [select,t,hz,KS.W06.RationalSignClassifier.outputCode,observedHeads,
        KS.W29.topCode,KS.W06.RationalCompare.stayActions]
    have hd := KS.W06.RationalCompare.branch_spec_left zeroProgram returnProgram 29 select _ _ _ hs hzrun
    have h := hr.compose hd
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl) <;> simp [result,ticks,hz,q,t,rowTicks,KS.W06.RationalSignClassifier.outputCode])
    omega
  · have hret := KS.W04.CleanRationalCompare.halt_spec (29 : Fin 32) t
    have hs : ∀ coin, select (observedHeads
        (⟨some (KS.W29.FixedBranch.start zeroProgram returnProgram),t⟩ :
          Config 32 (zeroProgram.states+returnProgram.states+1))) coin =
        ⟨.right,KS.W06.RationalCompare.stayActions 32⟩ := by
      intro coin
      by_cases hn : q<0 <;> simp [select,t,hz,hn,KS.W06.RationalSignClassifier.outputCode,observedHeads,
        KS.W29.topCode,KS.W06.RationalCompare.stayActions]
    have hd := KS.W06.RationalCompare.branch_spec_right zeroProgram returnProgram 29 select _ _ _ hs hret
    have h := hr.compose hd
    simp [program,result,ticks,hz,q,t] at h ⊢
    exact h

end KS.W17.PivotDecision

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotDecisionPorts
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

theorem decision_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b) :
    RunSpec decisionProgram (matrixState saved M) (withSaved saved (PivotDecision.result M))
      (PivotDecision.ticks M b) := by
  rw [← withSaved_initial saved M]
  apply KS.W01.FixedPortRunSpec.lift_runSpec PivotDecision.program schurPorts _ _ _ _ _
    (PivotDecision.full_spec M b hnum hden)
  · intro i; simp [withSaved,schurPorts,i.isLt]
  · intro i; simp [withSaved,schurPorts,i.isLt]
  · intro j hj
    have hge : ¬j.val<32 := by
      intro h
      exact hj ⟨j.val,h⟩ (Fin.ext rfl)
    simp [withSaved,hge]

theorem decision_nonterminal_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b)
    (ht : pivotTerminal (DenseRatMatrix.decode M) = none) :
    RunSpec decisionProgram (matrixState saved M) (matrixState saved M) (PivotDecision.ticks M b) := by
  simpa only [PivotDecision.result_nonterminal M ht,withSaved_initial] using decision_spec saved M b hnum hden

end KS.W17.FixedPSD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotTerminalMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

theorem unitTerminal_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) :
    RunSpec unitTerminal (Function.update (matrixState saved M) 29 [false])
      (terminalState saved M (Pi.single 0 1)) (2+unitTicks n) := by
  have hc := KS.W04.CleanRationalCompare.clear_spec (29 : Fin 35)
    (Function.update (matrixState saved M) 29 [false])
  have he : KS.W04.CleanRationalCompare.clearState 29
      (Function.update (matrixState saved M) 29 [false]) = matrixState saved M := by
    funext j; fin_cases j <;> simp [KS.W04.CleanRationalCompare.clearState,matrixState,state,Function.update]
  rw [he] at hc
  have hu := KS.W19.TerminalVectorReplace.unit_spec (matrixState saved M) (n+1) (by omega)
    rfl rfl rfl rfl rfl rfl rfl
  rw [KS.W19.TerminalVectorReplace.unit_tape] at hu
  exact hc.compose hu

theorem terminal_unit_case {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) :
    RunSpec terminalProgram (Function.update (matrixState saved M) 29 [false])
      (terminalState saved M (Pi.single 0 1)) ((2+unitTicks n)+1) := by
  apply KS.W06.RationalCompare.branch_spec_left unitTerminal sparseTerminal 23 terminalSelect
    _ _ _ _ (unitTerminal_spec saved M)
  intro coin
  simp [terminalSelect,observedHeads,KS.W29.topCode,Function.update,KS.W06.RationalCompare.stayActions]

theorem terminal_negative_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1))
    (hn : DenseRatMatrix.decode M 0 0 < 0) :
    RunSpec terminalProgram (withSaved saved (PivotDecision.result M))
      (terminalState saved M (Pi.single 0 1)) ((2+unitTicks n)+1) := by
  rw [PivotDecision.result_negative M hn]
  have he : withSaved saved (Function.update (PivotRowLoop.initial M) 29 [false]) =
      Function.update (matrixState saved M) 29 [false] := by
    funext j; fin_cases j <;> simp [withSaved,PivotRowLoop.initial,PivotRowLoop.state,
      matrixState,state,Function.update,Computability.encodeNat,Computability.encodeNum]
  rw [he]
  exact terminal_unit_case saved M

theorem finishTerminal_spec {n N : ℕ} (h : PivotHistory n N) (M : DenseRatMatrix n) (q : Fin n → ℚ) :
    RunSpec finishTerminal (terminalState (historyTape h) M q)
      (state [] [] [] [] (KS.W12.RowDot.vectorTape (h.restore q)))
      ((KS.W08.denseMatrixTape M).length+(Computability.encodeNat n).length+3+restoreTicks h q) := by
  have hc := KS.W04.CleanRationalCompare.clearList_spec (23 : Fin 35) [31,26]
    (terminalState (historyTape h) M q)
  have he : KS.W04.CleanRationalCompare.clearListState [31,26] (terminalState (historyTape h) M q) =
      state (historyTape h) [] [] [] (KS.W12.RowDot.vectorTape q) := by
    funext j; fin_cases j <;> simp [KS.W04.CleanRationalCompare.clearListState_apply,
      terminalState,matrixState,state,Function.update]
  have ht : KS.W04.CleanRationalCompare.clearListTicks [31,26] (terminalState (historyTape h) M q) =
      (KS.W08.denseMatrixTape M).length+(Computability.encodeNat n).length+3 := by
    simp [KS.W04.CleanRationalCompare.clearListTicks,KS.W04.CleanRationalCompare.clearState,
      terminalState,matrixState,state,Function.update]
    omega
  rw [he,ht] at hc
  exact hc.compose (restoreAll_spec h q)

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

theorem body_descend_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b)
    (ht : pivotTerminal (DenseRatMatrix.decode M) = none) :
    RunSpec controllerBody (matrixState saved M)
      (matrixState (savedFrame (Computability.encodeNat (n+1)) (KS.W08.denseMatrixTape M) ++ saved) (child M))
      (PivotDecision.ticks M b+(descentTicks M b+1)) := by
  have hd := fullDescend_spec saved M b hnum hden
  have hs : ∀ coin, afterDecisionSelect (observedHeads
      (⟨some (KS.W29.FixedBranch.start fullDescendProgram terminalRestoreProgram),matrixState saved M⟩ :
        Config 35 (fullDescendProgram.states+terminalRestoreProgram.states+1))) coin =
      ⟨.left,KS.W06.RationalCompare.stayActions 35⟩ := by
    intro coin; simp [afterDecisionSelect,matrixState,state,observedHeads,KS.W29.topCode,
      KS.W06.RationalCompare.stayActions]
  have hb := KS.W06.RationalCompare.branch_spec_left fullDescendProgram terminalRestoreProgram 23
    afterDecisionSelect _ _ _ hs hd
  exact (decision_nonterminal_spec saved M b hnum hden ht).compose hb

theorem body_negative_spec {n N : ℕ} (h : PivotHistory (n+1) N) (M : DenseRatMatrix (n+1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b)
    (hn : DenseRatMatrix.decode M 0 0 < 0) :
    RunSpec controllerBody (matrixState (historyTape h) M)
      (state [] [] [] [] (KS.W12.RowDot.vectorTape (h.restore (Pi.single 0 1))))
      (PivotDecision.ticks M b+(((2+unitTicks n)+1+finishTicks h M (Pi.single 0 1))+1)) := by
  have ht := (terminal_negative_spec (historyTape h) M hn).compose (finishTerminal_spec h M (Pi.single 0 1))
  have hs : ∀ coin, afterDecisionSelect (observedHeads
      (⟨some (KS.W29.FixedBranch.start fullDescendProgram terminalRestoreProgram),
        withSaved (historyTape h) (PivotDecision.result M)⟩ :
        Config 35 (fullDescendProgram.states+terminalRestoreProgram.states+1))) coin =
      ⟨.right,KS.W06.RationalCompare.stayActions 35⟩ := by
    intro coin
    rw [PivotDecision.result_negative M hn]
    simp [afterDecisionSelect,withSaved,observedHeads,KS.W29.topCode,Function.update,
      KS.W06.RationalCompare.stayActions]
  have hb := KS.W06.RationalCompare.branch_spec_right fullDescendProgram terminalRestoreProgram 23
    afterDecisionSelect _ _ _ hs ht
  exact (decision_spec (historyTape h) M b hnum hden).compose hb

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

theorem controller_step_clear (saved : List Bool) (b coin : Bool) :
    controllerProgram.toMachine.step (controllerConfig (state (b::saved) [] [] [] [])) coin =
      controllerConfig (state saved [] [] [] []) := by
  change (KS.W29.FixedLoop.loop controllerBody controllerGuard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState controllerBody),_⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  cases b <;> apply congrArg₂ Config.mk
  all_goals
    simp [KS.W29.FixedLoop.guardInstruction,controllerGuard,state,observedHeads,
      KS.W29.topCode,Instruction.action,KS.W29.StackAction.apply]
    first | rfl | (funext j; by_cases hj : j = 32 <;> simp [state, hj])

theorem controller_step_empty (coin : Bool) :
    controllerProgram.toMachine.step (controllerConfig (state [] [] [] [] [])) coin =
      ⟨none,state [] [] [] [] []⟩ := by
  change (KS.W29.FixedLoop.loop controllerBody controllerGuard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState controllerBody),_⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  apply congrArg₂ Config.mk
  · simp [KS.W29.FixedLoop.guardInstruction,controllerGuard,state,observedHeads,KS.W29.topCode]
    rfl
  · funext j
    simp [KS.W29.FixedLoop.guardInstruction,controllerGuard,state,observedHeads,
      KS.W29.topCode,Instruction.action,KS.W29.StackAction.apply]

theorem controller_run_clear (saved bits : List Bool) (hlen : saved.length+1 ≤ bits.length) :
    controllerProgram.toMachine.run (controllerConfig (state saved [] [] [] [])) bits =
      ⟨none,state [] [] [] [] []⟩ := by
  induction saved generalizing bits with
  | nil =>
    cases bits with
    | nil => simp at hlen
    | cons coin bs => erw [Machine.run.eq_2,controller_step_empty,Machine.run_halted _ _ rfl]
  | cons b saved ih =>
    cases bits with
    | nil => simp at hlen
    | cons coin bs =>
      erw [Machine.run.eq_2,controller_step_clear]
      exact ih bs (by simp only [List.length_cons] at hlen; omega)

theorem controller_step_finished (wire : List Bool) (hne : wire ≠ []) (coin : Bool) :
    controllerProgram.toMachine.step (controllerConfig (state [] [] [] [] wire)) coin =
      ⟨none,state [] [] [] [] wire⟩ := by
  change (KS.W29.FixedLoop.loop controllerBody controllerGuard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState controllerBody),_⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  cases wire with
  | nil => exact (hne rfl).elim
  | cons b bs =>
    cases b <;> apply congrArg₂ Config.mk
    all_goals
      simp [KS.W29.FixedLoop.guardInstruction,controllerGuard,state,observedHeads,
        KS.W29.topCode,Instruction.action,KS.W29.StackAction.apply]
      rfl

theorem controller_step_call {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (coin : Bool) :
    controllerProgram.toMachine.step (controllerConfig (matrixState saved M)) coin =
      KS.W29.FixedLoop.liftBody controllerBody ⟨some controllerBody.initial,matrixState saved M⟩ := by
  have hne : Computability.encodeNat (n+1) ≠ [] := by
    intro he
    have hz := (KS.W06.RationalSignClassifier.encodeNat_eq_nil (n+1)).mp he
    omega
  change (KS.W29.FixedLoop.loop controllerBody controllerGuard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState controllerBody),_⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  cases he : Computability.encodeNat (n+1) with
  | nil => exact (hne he).elim
  | cons b bs =>
    cases b <;> apply congrArg₂ Config.mk
    all_goals
      simp [KS.W29.FixedLoop.guardInstruction,controllerGuard,matrixState,state,he,observedHeads,
        KS.W29.topCode,Instruction.action,KS.W29.StackAction.apply] <;>
        first | rfl | (funext j; simp [state])

theorem controllerTicks_descend {n N : ℕ} (h : PivotHistory (n+1) N) (M : DenseRatMatrix (n+1))
    (ht : pivotTerminal (DenseRatMatrix.decode M) = none) :
    controllerTicks h M = 1+(PivotDecision.ticks M (localBits M)+(descentTicks M (localBits M)+1))+
      controllerTicks (.push (DenseRatMatrix.decode M) h) (child M) := by
  rcases pivotTerminal_none_cases (DenseRatMatrix.decode M) ht with ⟨hz,hr⟩ | hp
  · simp [controllerTicks,hz,hr]
  · simp [controllerTicks,hp.ne',not_lt.mpr hp.le]

end KS.W17.FixedPSD

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

theorem sparseTicks_payload_bound {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1))
    (j : Fin (n+1)) :
    KS.W19.TerminalWitnessMachine.ticks saved M (localBits M) j ≤
      1000000000000000000*(localBits M+1)^3 := by
  exact KS.W19.TerminalWitnessMachine.ticks_polynomial saved M (localBits M) (localBits M)
    (fun i j => (KS.W19.TerminalWitnessMachine.entry_parts_le_payload M i j).1)
    (fun i j => (KS.W19.TerminalWitnessMachine.entry_parts_le_payload M i j).2)
    (KS.W19.TerminalWitnessMachine.dimension_le_payload M) le_rfl j

theorem ControllerReachable.terminal_ticks_le {N n : ℕ} {A : DenseRatMatrix N}
    {M : DenseRatMatrix (n+1)} {h : PivotHistory (n+1) N} (hr : ControllerReachable A M h) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode A i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode A i j).den ≤ 2^b)
    (ht : pivotTerminal (DenseRatMatrix.decode M) ≠ none) :
    controllerTicks h M ≤ originalTerminalBound N b := by
  have hm : localBits M ≤ originalMatrixTapeBound N b := hr.matrix_tape_length b hnum hden
  have hdec : PivotDecision.ticks M (localBits M) ≤ 100000000*(originalMatrixTapeBound N b+1)^4 := by
    have hwire : (KS.W08.denseMatrixTape M).length ≤ originalMatrixTapeBound N b := hm
    exact (KS.W23.PivotScannerBounds.decision_payload_ticks M).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hwire 1) 4))
  by_cases hn : DenseRatMatrix.decode M 0 0 < 0
  · have hu := (unitTicks_payload_bound M).trans (Nat.mul_le_mul_left 100 (Nat.add_le_add_right hm 1))
    have hq : uniformNegativeWitness (n+1) (DenseRatMatrix.decode M) = some (Pi.single 0 1) := by
      simp [uniformNegativeWitness,pivotTerminal,hn]
    have hf := hr.finish_ticks_le b hnum hden (Pi.single 0 1) hq
    simp only [controllerTicks,hn,ite_true, if_true]
    unfold originalTerminalBound
    omega
  · by_cases hz : DenseRatMatrix.decode M 0 0 = 0
    · cases hj : firstNonzeroOffDiagonal (DenseRatMatrix.decode M) with
      | none => exact (ht (by simp [pivotTerminal,hz,hj])).elim
      | some j =>
        have hs : KS.W19.TerminalWitnessMachine.ticks (historyTape h) M (localBits M) j.succ ≤
            1000000000000000000*(originalMatrixTapeBound N b+1)^3 := by
          exact (sparseTicks_payload_bound (historyTape h) M j.succ).trans
            (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))
        have hq : uniformNegativeWitness (n+1) (DenseRatMatrix.decode M) =
            some (zeroPivotWitness (DenseRatMatrix.decode M) 0 j.succ) := by
          simp [uniformNegativeWitness,pivotTerminal,hz,hj]
        have hf := hr.finish_ticks_le b hnum hden _ hq
        simp only [controllerTicks,hz,lt_self_iff_false,ite_true, if_true,ite_false, if_false,hj]
        unfold originalTerminalBound
        omega
    · exact (ht (by simp [pivotTerminal,hn,hz])).elim

end KS.W17.FixedPSD

end

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

theorem child_parts_payload {n : ℕ} (M : DenseRatMatrix (n+1)) (i j : Fin n) :
    (DenseRatMatrix.decode (child M) i j).num.natAbs ≤ 2^(4*(W08.denseMatrixTape M).length+3) ∧
    (DenseRatMatrix.decode (child M) i j).den ≤ 2^(4*(W08.denseMatrixTape M).length+3) := by
  simpa only [child, DenseRatMatrix.decode_ofMatrix] using
    SchurTable.entry_parts_le M (W08.denseMatrixTape M).length
      (fun i j => (entry_parts_le_payload M i j).1)
      (fun i j => (entry_parts_le_payload M i j).2) i j

theorem child_tape_payload_bound {n : ℕ} (M : DenseRatMatrix (n+1)) :
    (W08.denseMatrixTape (child M)).length ≤ 39*((W08.denseMatrixTape M).length+1)^3 := by
  let L := (W08.denseMatrixTape M).length
  have ht := W08.denseMatrixTape_length_le (child M) (4*L+3)
    (fun i j => (child_parts_payload M i j).1)
    (fun i j => (child_parts_payload M i j).2)
  have hn : n+1 ≤ L := dimension_le_payload M
  have hsq : n*n ≤ (L+1)^2 := by
    have h := Nat.mul_le_mul (show n ≤ L+1 by omega) (show n ≤ L+1 by omega)
    simpa only [pow_two] using h
  have hc : 8*(4*L+3)+15 ≤ 39*(L+1) := by omega
  calc
    (W08.denseMatrixTape (child M)).length ≤ n*n*(8*(4*L+3)+15) := ht
    _ ≤ (L+1)^2*(39*(L+1)) := Nat.mul_le_mul hsq hc
    _ = 39*(L+1)^3 := by ring

theorem descent_payload_ticks {n : ℕ} (M : DenseRatMatrix (n+1)) :
    descentTicks M (W08.denseMatrixTape M).length ≤ payloadBudget (W08.denseMatrixTape M).length := by
  have hs := schur_payload_ticks M
  have hc := child_tape_payload_bound M
  have hn := dimension_le_payload M
  have hrn := raw_length_le n
  have hrs := raw_length_le (n+1)
  have hp1 : (W08.denseMatrixTape M).length+1 ≤ ((W08.denseMatrixTape M).length+1)^5 :=
    Nat.le_self_pow (by decide) _
  have hp3 : ((W08.denseMatrixTape M).length+1)^3 ≤ ((W08.denseMatrixTape M).length+1)^5 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  unfold descentTicks payloadBudget descentCoefficient
  omega

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

theorem step_payload_bound {n : ℕ} (M : DenseRatMatrix (n+1)) :
    stepTicks M ≤ stepBudget (localBits M) := by
  have hd := PivotDescentBounds.descent_payload_ticks M
  have hc := PivotScannerBounds.decision_payload_ticks M
  have hp : ((KS.W08.denseMatrixTape M).length+1)^4 ≤ ((KS.W08.denseMatrixTape M).length+1)^5 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hp1 : 1 ≤ ((KS.W08.denseMatrixTape M).length+1)^5 :=
    Nat.one_le_pow' 5 (KS.W08.denseMatrixTape M).length
  unfold stepTicks stepBudget stepCoefficient localBits
  unfold PivotDescentBounds.payloadBudget at hd
  rw [Nat.add_mul, Nat.add_mul]
  omega

theorem reachable_step_bound {N n : ℕ} {A : DenseRatMatrix N}
    {M : DenseRatMatrix (n+1)} {h : PivotHistory (n+1) N}
    (hr : ControllerReachable A M h) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode A i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode A i j).den ≤ 2^b) :
    stepTicks M ≤ stepBudget (originalMatrixTapeBound N b) :=
  (step_payload_bound M).trans (stepBudget_mono (hr.matrix_tape_length b hnum hden))

end KS.W23.PivotReachableBounds

end

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

theorem ControllerReachable.controller_ticks_le {N n : ℕ} {A : DenseRatMatrix N}
    {M : DenseRatMatrix n} {h : PivotHistory n N} (hr : ControllerReachable A M h) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode A i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode A i j).den ≤ 2^b) :
    controllerTicks h M ≤ (n+1)*originalControllerStepBound N b := by
  induction n with
  | zero =>
    have hh := hr.history_tape_length b hnum hden
    have hd := h.dimension_depth
    simp only [zero_add] at hd
    simp only [controllerTicks,zero_add,one_mul]
    rw [hd] at hh
    unfold originalControllerStepBound
    omega
  | succ n ih =>
    by_cases ht : pivotTerminal (DenseRatMatrix.decode M) = none
    · have hs := KS.W23.PivotReachableBounds.reachable_step_bound hr b hnum hden
      have hc := ih (M:=child M) (h:=PivotHistory.push (DenseRatMatrix.decode M) h)
        (ControllerReachable.descend hr ht)
      have hsg : KS.W23.PivotReachableBounds.stepBudget (originalMatrixTapeBound N b) ≤
          originalControllerStepBound N b := by unfold originalControllerStepBound; omega
      rw [controllerTicks_descend h M ht]
      unfold KS.W23.PivotReachableBounds.stepTicks at hs
      nlinarith
    · have hb := hr.terminal_ticks_le b hnum hden ht
      have hbg : originalTerminalBound N b ≤ originalControllerStepBound N b := by
        unfold originalControllerStepBound
        omega
      nlinarith

end KS.W17.FixedPSD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_RatFieldsRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.CurrentKS.Realization.poly_matrixView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine
open KS.W29.FixedSequential KS.W03.MachineCombinators

def ratCeil : Realizes ratCode natCode (fun q => ⌈q⌉₊) :=
  ((((identity ratCode).neg.then ratFloor).neg).then ratNumToNat).congr (by
    intro q
    change (-((⌊-q⌋ : ℤ) : ℚ)).num.toNat=⌈q⌉₊
    rw [Int.floor_neg,Int.cast_neg,neg_neg,Rat.num_intCast,Int.ceil_toNat])

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ScheduleRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α : Type*} {ea : α → Word} {f g : α → ℚ}

def saSigma := (saLam.pow 2).div saNu

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_SearchRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

def searchStepRealizes : Realizes searchStateCode ratCode
    (fun s => RationalSDP.searchStep s.n s.r) :=
  (searchParameters.then (first ratCode ratCode)).div
    ((searchDim.then natToRat).add (constant searchStateCode ratCode 1))
def searchMeshRealizes : Realizes searchStateCode ratCode
    (fun s => RationalSDP.searchMesh s.n s.r s.R) :=
  let dim1 := (searchDim.then natToRat).add (constant searchStateCode ratCode 1)
  let S := searchStepRealizes
  let R := searchParameters.then (second ratCode ratCode)
  (S.pow 2).div (((constant searchStateCode ratCode 16).mul dim1).mul
    ((R.add S).add (constant searchStateCode ratCode 1)))
def searchFuelRealizes : Realizes searchStateCode natCode
    (fun s => RationalSDP.searchFuel s.n s.r s.R) :=
  let R := searchParameters.then (second ratCode ratCode)
  ((((constant searchStateCode ratCode 4).mul (R.pow 2)).div
    (searchStepRealizes.pow 2)).then ratCeil).then natSucc

def searchInit : Realizes searchStateCode pencilStateCode SearchState.init :=
  (searchPencil.both ((searchStepRealizes.both searchMeshRealizes).both searchY)).changeOutput
    pencilStateCode SearchState.init (fun _ => rfl)

end CurrentKS.Realization

end

end OAI
end


