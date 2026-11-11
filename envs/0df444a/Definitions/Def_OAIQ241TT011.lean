-- Prove2me | Definitions.Def_OAIQ241TT011
-- name    : OAIQ241TT011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:59:50.130667+00:00
-- url     : https://prove2.me/theorems/b4f49249-6bd8-4778-ac74-43bbd2ba80ef
-- title:
--   Definitions bundle OAIQ241TT011 of the split of OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 59 declarations of OpenAI's Lean: 33 definitions, 8 instances and 18 theorems. The definitions and types are `OAI.AlgorithmicThinTrees.InputStack.bEndpoint`, `OAI.AlgorithmicThinTrees.InputStack.bMultiplicityRat`, `OAI.AlgorithmicThinTrees.InputStack.bN`, `OAI.AlgorithmicThinTrees.InputStack.bP`, `OAI.AlgorithmicThinTrees.InputStack.binaryTail`, `OAI.AlgorithmicThinTrees.InputStack.eEndpoint`, `OAI.AlgorithmicThinTrees.InputStack.eK`, `OAI.AlgorithmicThinTrees.InputStack.eM`, `OAI.AlgorithmicThinTrees.InputStack.eN`, `OAI.AlgorithmicThinTrees.InputStack.ePrepare`, `OAI.AlgorithmicThinTrees.InputStack.explicitTail`, `OAI.AlgorithmicThinTrees.InputStack.goodFields`, `OAI.AlgorithmicThinTrees.InputStack.goodN`, `OAI.AlgorithmicThinTrees.InputStack.lookupPair`, `OAI.AlgorithmicThinTrees.InputStack.pairsOutput`, `OAI.AlgorithmicThinTrees.InputStack.singletonTest`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.meshRaw`, `OAI.AlgorithmicThinTrees.Signing.Stack.stack`, `OAI.CurrentKS.Realization.Realizes.blockWith`, `OAI.CurrentKS.Realization.binarySucc`, `OAI.CurrentKS.Realization.binaryToRat`, `OAI.CurrentKS.Realization.blockDiagonal`, `OAI.CurrentKS.Realization.fromBlocks`, `OAI.CurrentKS.Realization.maskArray`, `OAI.CurrentKS.Realization.natToBinary`, `OAI.CurrentKS.Realization.ratNumToNat`, `OAI.CurrentKS.Realization.realizedMachine`, `OAI.CurrentKS.Realization.solveTopRow`, `OAI.CurrentKS.Realization.wordCons`, `OAI.CurrentKS.WordHead.flag`, `OAI.CurrentKS.WordHead.program`, `OAI.KS.W07.SchurCellMachine.ticks`, `OAI.KS.W07.SchurLoopState.columnTicks`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `MatrixSigning_Arithmetic_ComplexScalarNodes`, `MatrixSigning_Complexity_PolynomialRoots`, `MatrixSigning_Complexity_PolynomialStored`, `MatrixSigning_Encoding_FramedArrayReplacement`, `MatrixSigning_Encoding_WireProgramPrimitives`, `MatrixSigning_Encoding_ZeroArrayConstructor`, `MatrixSigning_Machines_SchurCellMachine`, `MatrixSigning_Machines_SchurTableMachine`, `MatrixSigning_Machines_TerminalVectorReplace`, `MatrixSigning_Machines_TerminalZeroVector`, `MatrixSigning_Matrices_PivotDecisionCorrectness`, `MatrixSigning_Potential_SchurLoopState`, `MatrixSigning_Realization_BinaryNaturalRealization`, `MatrixSigning_Realization_MatrixStructureRealization`, `MatrixSigning_Realization_PencilCompileRealization`, `MatrixSigning_Realization_RatFieldsRealization`, `MatrixSigning_Realization_ValueEvalRealization`, `ThinTrees_Arithmetic_BinaryArithmetic`, `ThinTrees_Arithmetic_WordHead`, `ThinTrees_Continuation_BitBound`, `ThinTrees_Encoding_AlgorithmicMain`, `ThinTrees_Encoding_InputArrays`, `ThinTrees_Encoding_InputDispatch`, `ThinTrees_Encoding_InputExpansion`, `ThinTrees_Encoding_InputOutput`, `ThinTrees_Encoding_SelectionRealization`, `ThinTrees_RationalMatrix_InverseRealization`, `ThinTrees_Signing_Realization`.
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
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_WireProgramPrimitives
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W15.WireProgram
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem literal_spec {k : Nat} (port : Fin k) (word : List Bool)
    (before : Fin k → List Bool) :
    RunSpec (literalProgram port word) before
      (Function.update before port (word ++ before port)) (word.length + 1) := by
  induction word generalizing before with
  | nil => simpa [literalProgram] using stay_spec port before
  | cons b bs ih =>
      have h := (ih before).compose
        (push_spec port b (Function.update before port (bs ++ before port)))
      simpa [literalProgram, List.length_cons, Nat.add_assoc] using h

end KS.W15.WireProgram

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_ComplexScalarNodes
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalSignClassifier.program_output _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W15.ComplexMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W15.WireProgram

theorem pair_spec (a b : Fin 28) (ha : 16 ≤ a.val) (hb : 16 ≤ b.val)
    (before : Registers) (hclear : CoreEmpty before) :
    RunSpec (pairProgram a b ha hb) before
      (Function.update before 0 (before a ++ before b)) (pairTicks (before a) (before b)) := by
  have h0 : before (0 : Fin 28) = [] := hclear 0
  have h1 : before (1 : Fin 28) = [] := hclear 1
  have h2 : before (2 : Fin 28) = [] := hclear 2
  have ha0 : a ≠ (0 : Fin 28) := stored_ne_core a ha 0
  let s1 := Function.update before (0 : Fin 28) (before b)
  let s2 := Function.update s1 (2 : Fin 28) (before a)
  have hc1 := copy_spec b (0 : Fin 28) 1 (stored_ne_core b hb 0) (stored_ne_core b hb 1)
    (by decide) before h0 h1
  have hc2 : RunSpec
      (copyProgram a (2 : Fin 28) 1 (stored_ne_core a ha 2) (stored_ne_core a ha 1) (by decide))
      s1 s2 (2 * (before a).length + 2) := by
    have h := copy_spec a (2 : Fin 28) 1 (stored_ne_core a ha 2) (stored_ne_core a ha 1)
      (by decide) s1 (by simpa [s1] using h2) (by simpa [s1] using h1)
    simpa [s1,s2,ha0] using h
  have ht := transfer_spec (2 : Fin 28) 0 1 (by decide) (by decide) (by decide) s2
    (by simpa [s1,s2] using h1)
  have h := (hc1.compose hc2).compose ht
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  · funext j
    by_cases hj0 : j = 0 <;> by_cases hj1 : j = 1 <;> by_cases hj2 : j = 2 <;>
      simp_all [transferAfter,s1,s2,Function.update]
  · simp [pairTicks,s1,s2]
    omega

theorem scalar_multiplication_spec (before : Registers) (hclear : CoreEmpty before) (q r : ℚ) :
    RunSpec mulProgram (Function.update before 0 (KS.W01.encodeRat q ++ KS.W01.encodeRat r))
      (Function.update before 10 (KS.W01.encodeRat (q * r))) (RationalMultiply.totalTicks q r) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ _ _ _ _ _ _ (RationalMultiply.full_spec q r)
  · intro i
    fin_cases i <;> simp [mulPorts_apply,KS.W06.RationalCompare.fields,RationalMultiply.inputBits,Function.update,
      coreEmpty_apply before hclear]
  · intro i
    fin_cases i <;> simp [mulPorts_apply,KS.W01.SignedRationalSerializer.outputState,Function.update,
      coreEmpty_apply before hclear]
  · intro j hj
    have hj0 : j ≠ 0 := hj 0
    have hj10 : j ≠ 10 := hj 10
    simp [Function.update,hj0,hj10]

theorem scalar_addition_spec (before : Registers) (hclear : CoreEmpty before) (q r : ℚ) :
    RunSpec addProgram (Function.update before 0 (KS.W01.encodeRat q ++ KS.W01.encodeRat r))
      (Function.update before 10 (KS.W01.encodeRat (q + r))) (KS.W13.RationalAdd.totalTicks q r) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ _ _ _ _ _ _ (KS.W13.RationalAdd.full_spec q r)
  · intro i
    fin_cases i <;> simp [corePorts_apply,KS.W13.RationalAdd.inputState,KS.W13.RationalAdd.extend,
      KS.W06.RationalCompare.fields,Function.update,
      coreEmpty_apply before hclear]
  · intro i
    fin_cases i <;> simp [corePorts_apply,KS.W13.RationalAdd.outputState,KS.W13.RationalAdd.extend,
      KS.W01.SignedRationalSerializer.outputState,Function.update,
      coreEmpty_apply before hclear]
  · intro j hj
    have hj0 : j ≠ 0 := hj 0
    have hj10 : j ≠ 10 := hj 10
    simp [Function.update,hj0,hj10]

theorem store_spec (before : Registers) (hclear : CoreEmpty before)
    (dest : Fin 28) (hd : 16 ≤ dest.val) (hempty : before dest = []) (wire : List Bool) :
    RunSpec (storeProgram dest) (Function.update before 10 wire)
      (Function.update before dest wire) (2 * wire.length + 2) := by
  have hd10 : dest ≠ (10 : Fin 28) := stored_ne_core dest hd 10
  have hd1 : dest ≠ (1 : Fin 28) := stored_ne_core dest hd 1
  have h10 : before (10 : Fin 28) = [] := hclear 10
  have h1 : before (1 : Fin 28) = [] := hclear 1
  have ht := transfer_spec (10 : Fin 28) dest 1 hd10.symm (by decide) hd1
    (Function.update before 10 wire) (by simpa using h1)
  convert ht using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  · funext j
    by_cases hj10 : j = 10 <;> by_cases hjd : j = dest <;>
      simp_all [transferAfter,Function.update]

end KS.W15.ComplexMachine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_BinaryNaturalRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

def binarySucc : Realizes binaryNatCode binaryNatCode Nat.succ where
  cost := fun n => 2*(binaryNatCode n).length+6
  routine := {
    scratch := 2
    program := KS.W07.SchurCounters.incrementProgram ⟨![1,0,2],by decide⟩
    spec := fun n => by
      have h := KS.W07.SchurCounters.increment_spec
        (⟨![1,0,2],by decide⟩ : Fin 3 ↪ Fin 3) (io (binaryNatCode n)) n rfl rfl rfl
      have he : Function.update (io (binaryNatCode n)) (0 : Fin 3)
          (Computability.encodeNat (n+1))=io (binaryNatCode (n+1)) := by
        funext j;fin_cases j <;> rfl
      change KS.W03.MachineCombinators.RunSpec _ _
        (Function.update (io (binaryNatCode n)) (0 : Fin 3)
          (Computability.encodeNat (n+1))) _ at h
      rw [he] at h
      exact h }

def natToBinary : Realizes natCode binaryNatCode id :=
  (((identity natCode).both (constant natCode binaryNatCode 0)).then binarySucc.iterate).congr (by
    intro n
    change Nat.succ^[n] 0=n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply',ih])

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_RatFieldsRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.CurrentKS.Realization.poly_matrixView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine
open KS.W29.FixedSequential KS.W03.MachineCombinators

def ratNumToNat : Realizes ratCode natCode (fun q : ℚ => q.num.toNat) :=
  (((constant ratCode ratCode 0).le (identity ratCode)).ite
    (ratNumBinary.then binaryToNat) (constant ratCode natCode 0)).congr (by
      intro q
      change (if decide (0≤q) then KS.W01.intPayload q.num else 0)=q.num.toNat
      have h := @Rat.num_nonneg q
      cases hn : q.num with
      | ofNat n =>
        have hq : 0≤q := h.mp (by rw [hn];exact Int.natCast_nonneg n)
        simp [hq,KS.W01.intPayload]
      | negSucc n =>
        have hq : ¬0≤q := by intro hp;have := h.mpr hp;rw [hn] at this;omega
        simp [hq])

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialRoots
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23 RationalGridSize

instance poly_wordTail : PolyTime wordTail := ⟨⟨1,fun _ => le_rfl⟩⟩
instance poly_ratFields : PolyTime ratFields := by unfold ratFields;infer_instance
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_MatrixStructureRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

variable {α : Type*}

def fromBlocks : Realizes (prodCode (prodCode matrixCode matrixCode) (prodCode matrixCode matrixCode))
    matrixCode fromBlocksData :=
  let top := (first (prodCode matrixCode matrixCode) (prodCode matrixCode matrixCode)).then
    ((appendList ratCode).zipWith [] [])
  let bot := (second (prodCode matrixCode matrixCode) (prodCode matrixCode matrixCode)).then
    ((appendList ratCode).zipWith [] [])
  (top.both bot).then (appendList vectorCode)

end CurrentKS.Realization

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

theorem run_replace_prefix («prefix» : List (List Bool)) (old new tail bits : List Bool)
    (hlen : replaceFuel «prefix» old new ≤ bits.length) :
    program.toMachine.run
      (config (some program.initial)
        («prefix».flatMap KS.W01.frame ++ KS.W01.frame old ++ tail)
        (KS.W01.frame new) [] [] (List.replicate «prefix».length true)) bits =
      config none («prefix».flatMap KS.W01.frame ++ KS.W01.frame new ++ tail) [] [] [] [] := by
  apply run_compose_bounded prefixProgram replaceTailProgram
    («stacks» («prefix».flatMap KS.W01.frame ++ KS.W01.frame old ++ tail)
      (KS.W01.frame new) [] [] (List.replicate «prefix».length true))
    («stacks» (KS.W01.frame old ++ tail) (KS.W01.frame new)
      («prefix».flatMap KS.W01.frame).reverse [] [])
    («stacks» («prefix».flatMap KS.W01.frame ++ KS.W01.frame new ++ tail) [] [] [] [])
    (KS.W11.FramedArray.scanFuel «prefix»)
    (2 * old.length + 2 * (KS.W01.frame new).length +
      («prefix».flatMap KS.W01.frame).length + 4)
  · intro bs hb
    have h := run_prefix «prefix»
      (KS.W01.frame old ++ tail) (KS.W01.frame new) bs hb
    simp only [List.append_assoc] at h ⊢
    exact h
  · intro bs hb
    have h := run_replaceTail old tail (KS.W01.frame new) («prefix».flatMap KS.W01.frame).reverse bs
        (by simpa only [List.length_reverse] using hb)
    simp only [List.reverse_reverse] at h ⊢
    exact h
  · unfold replaceFuel at hlen
    omega

end KS.W11.FramedArrayRewrite

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_ZeroArrayConstructor
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationMachine.input_port _root_.OAI.KS.W03.MultiplicationMachine.output_port _root_.OAI.KS.W03.MultiplicationMachine.stack_count _root_.OAI.KS.W03.MultiplicationMachine.state_count _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W06.RationalSignClassifier.program_output _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W15.RationalMultiply.machine_inputStack _root_.OAI.KS.W15.RationalMultiply.machine_outputStack _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W11.ZeroArrayConstructor
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem run_loop (count accum bits : List Bool)
    (hlen : count.length * (zeroFrame.length + 2) + 1 ≤ bits.length) :
    loopProgram.toMachine.run ⟨some loopProgram.initial, «stacks» count accum []⟩ bits =
      ⟨none, «stacks» [] ((zeroTape count.length).reverse ++ accum) []⟩ := by
  induction count generalizing accum bits with
  | nil =>
      cases bits with
      | nil => simp at hlen
      | cons coin rest =>
          rw [Machine.run, guard_nil, Machine.run_halted _ _ rfl]
          rfl
  | cons mark count ih =>
      cases bits with
      | nil => simp at hlen
      | cons coin rest =>
          have hb : zeroFrame.length + 1 ≤ rest.length := by
            simp only [List.length_cons, Nat.add_mul] at hlen
            omega
          obtain ⟨remaining, hremaining, he⟩ :=
            (emit_spec zeroFrame count accum []).loop_body_then guard rest hb
          have ht : count.length * (zeroFrame.length + 2) + 1 ≤ remaining.length := by
            simp only [List.length_cons, Nat.add_mul] at hlen
            omega
          rw [Machine.run, guard_cons]
          erw [he]
          have h := ih (zeroFrame.reverse ++ accum) remaining ht
          simp only [List.length_cons, zeroTape_succ, List.reverse_append, List.append_assoc] at h ⊢
          exact h

theorem zero_spec (count : List Bool) :
    RunSpec program («stacks» count [] []) («stacks» [] [] (zeroTape count.length))
      ((2 * zeroFrame.length + 2) * count.length + 2) := by
  have hl : RunSpec loopProgram («stacks» count [] [])
      («stacks» [] (zeroTape count.length).reverse [])
      (count.length * (zeroFrame.length + 2) + 1) := by
    intro bits hbits
    simpa only [List.append_nil] using run_loop count [] bits hbits.ge
  have h := hl.compose (finish_spec (zeroTape count.length))
  have ht : (count.length * (zeroFrame.length + 2) + 1) + ((zeroTape count.length).length + 1) =
      (2 * zeroFrame.length + 2) * count.length + 2 := by
    rw [zeroTape_length]
    ring
  rw [ht] at h
  exact h

theorem zero_spec_linear (count : List Bool) :
    RunSpec program («stacks» count [] []) («stacks» [] [] (zeroTape count.length))
      (24 * count.length + 2) := by
  simpa only [zeroFrame_length] using zero_spec count

end KS.W11.ZeroArrayConstructor

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_TerminalZeroVector
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.BinaryMultiply.shift_value _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationMachine.input_port _root_.OAI.KS.W03.MultiplicationMachine.output_port _root_.OAI.KS.W03.MultiplicationMachine.stack_count _root_.OAI.KS.W03.MultiplicationMachine.state_count _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W06.RationalSignClassifier.program_output _root_.OAI.KS.W08.denseMatrixBinaryCursor_value _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W15.RationalMultiply.machine_inputStack _root_.OAI.KS.W15.RationalMultiply.machine_outputStack _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_quotient _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_remainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.TerminalZeroVector
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem zero_vector_spec (s : Fin 35 → List Bool) (n : ℕ)
    (hd : s 26 = Computability.encodeNat n)
    (h0 : s 0 = []) (h1 : s 1 = []) (h2 : s 2 = [])
    (h16 : s 16 = []) (h23 : s 23 = []) :
    RunSpec program s (Function.update s 23 (KS.W11.ZeroArrayConstructor.zeroTape n)) (ticks n) := by
  have hc : RunSpec copyProgram s (Function.update s 0 (Computability.encodeNat n))
      (2*(Computability.encodeNat n).length+2) := by
    apply KS.W03.MachineRoundTrip.runSpec_ofMachine
    intro bits hb
    exact KS.W01.FixedCopy.run_copy_restore copyPorts s (Computability.encodeNat n) bits hd h0 h16 hb
  have hu0 : RunSpec KS.W03.BinaryToUnary.program
      ![Computability.encodeNat n,[],[]] ![[],List.replicate n true,[]]
      (4*n+4*(Computability.encodeNat n).length+2) := by
    apply KS.W03.MachineRoundTrip.runSpec_ofMachine
    intro bits hb
    have h := KS.W03.BinaryToUnary.run_input_linear (Computability.encodeNat n) bits
      (by simpa only [bitsValue_encodeNat] using hb.ge)
    simp only [KS.W03.BinaryToUnary.init_eq, KS.W03.BinaryToUnary.cfg,
      bitsValue_encodeNat] at h
    exact h
  have hu : RunSpec unaryProgram (Function.update s 0 (Computability.encodeNat n))
      (Function.update s 1 (List.replicate n true))
      (4*n+4*(Computability.encodeNat n).length+2) := by
    apply KS.W01.FixedPortRunSpec.lift_runSpec _ unaryPorts _ _ _ _ _ hu0
    · intro j; fin_cases j <;> simp [unaryPorts,h1,h2]
    · intro j; fin_cases j <;> simp [unaryPorts,h0,h2]
    · intro j hj
      have ha := hj 0
      have hb := hj 1
      change j ≠ 0 at ha
      change j ≠ 1 at hb
      simp [Function.update_of_ne,ha,hb]
  have hz0 := KS.W11.ZeroArrayConstructor.zero_spec_linear (List.replicate n true)
  simp only [List.length_replicate] at hz0
  have hz : RunSpec zeroProgram (Function.update s 1 (List.replicate n true))
      (Function.update s 23 (KS.W11.ZeroArrayConstructor.zeroTape n)) (24*n+2) := by
    apply KS.W01.FixedPortRunSpec.lift_runSpec _ zeroPorts _ _ _ _ _ hz0
    · intro j; fin_cases j <;> simp [zeroPorts,KS.W11.ZeroArrayConstructor.«stacks»,h0,h23]
    · intro j; fin_cases j <;> simp [zeroPorts,KS.W11.ZeroArrayConstructor.«stacks»,h0,h1]
    · intro j hj
      have ha := hj 0
      have hb := hj 2
      change j ≠ 1 at ha
      change j ≠ 23 at hb
      simp [Function.update_of_ne,ha,hb]
  have h := hc.compose (hu.compose hz)
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (simp [program,ticks] <;> omega)

end KS.W19.TerminalZeroVector

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_TerminalVectorReplace
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.TerminalVectorReplace
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators Matrix

theorem unit_tape (n : ℕ) :
    ((unitPayloads (n+1)).flatMap KS.W01.frame) =
      KS.W12.RowDot.vectorTape (Pi.single (0 : Fin (n+1)) (1 : ℚ)) := by
  simp [unitPayloads,zeroPayloads,KS.W12.RowDot.vectorTape,List.replicate_succ,
    List.ofFn_succ,Pi.single_apply,List.ofFn_const]

end KS.W19.TerminalVectorReplace

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

def ticks (x a b c : ℚ) : ℕ :=
  (4 * KS.W01.ratLength a + 2 * KS.W01.ratLength b + 4) +
  (KS.W15.RationalMultiply.totalTicks a b +
  ((4 * KS.W01.ratLength (a * b) + 2 * KS.W01.ratLength c + 4) +
  (KS.W29.polynomialFuel 1100000 3 (KS.W30.RationalDivision.inputBits (a * b) c).length +
  ((4 * KS.W01.ratLength x + 2 * KS.W01.ratLength (a * b / c) + 4) +
    KS.W29.polynomialFuel 600000 3
      (KS.W01.encodeRat x ++ KS.W01.encodeRat (a * b / c)).length))))

theorem multiply_spec (x a b c : ℚ) :
    RunSpec multiply
      (workspace (KS.W01.encodeRat a ++ KS.W01.encodeRat b) [] (KS.W01.encodeRat x) [] []
        (KS.W01.encodeRat c))
      (workspace [] (KS.W01.encodeRat (a * b)) (KS.W01.encodeRat x) [] []
        (KS.W01.encodeRat c)) (KS.W15.RationalMultiply.totalTicks a b) := by
  have h := first_spec (by decide : 13 ≤ 23) _ _ _
    (workspace [] [] (KS.W01.encodeRat x) [] [] (KS.W01.encodeRat c)) _
    (KS.W15.RationalMultiply.full_spec a b)
  have hb : extend (KS.W06.RationalCompare.fields
      (KS.W15.RationalMultiply.inputBits a b) [] [] [] [] [] [])
      (workspace [] [] (KS.W01.encodeRat x) [] [] (KS.W01.encodeRat c)) =
      workspace (KS.W01.encodeRat a ++ KS.W01.encodeRat b) [] (KS.W01.encodeRat x) [] []
        (KS.W01.encodeRat c) := by
    funext j; fin_cases j <;> rfl
  have ha : extend (KS.W01.SignedRationalSerializer.outputState (KS.W01.encodeRat (a*b)))
      (workspace [] [] (KS.W01.encodeRat x) [] [] (KS.W01.encodeRat c)) =
      workspace [] (KS.W01.encodeRat (a*b)) (KS.W01.encodeRat x) [] [] (KS.W01.encodeRat c) := by
    funext j; fin_cases j <;> rfl
  rw [hb, ha] at h
  exact h

theorem subtract_spec (x q : ℚ) :
    RunSpec subtract (workspace (KS.W01.encodeRat x ++ KS.W01.encodeRat q) [] [] [] [] [])
      (workspace [] (KS.W01.encodeRat (x-q)) [] [] [] [])
      (KS.W29.polynomialFuel 600000 3 (KS.W01.encodeRat x ++ KS.W01.encodeRat q).length) := by
  have h := first_spec (by decide : 19 ≤ 23) _ _ _ (workspace [] [] [] [] [] []) _
    (KS.W13.RationalSubtract.polynomial_spec x q)
  have hb : extend (KS.W13.RationalSubtract.inputState (KS.W01.encodeRat x ++ KS.W01.encodeRat q))
      (workspace [] [] [] [] [] []) = workspace (KS.W01.encodeRat x ++ KS.W01.encodeRat q) [] [] [] [] [] := by
    funext j; fin_cases j <;> rfl
  have ha : extend (KS.W13.RationalSubtract.outputState (KS.W01.encodeRat (x-q)))
      (workspace [] [] [] [] [] []) = workspace [] (KS.W01.encodeRat (x-q)) [] [] [] [] := by
    funext j; fin_cases j <;> rfl
  rw [hb, ha] at h
  exact h

end KS.W07.SchurCellMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurTableMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationMachine.input_port _root_.OAI.KS.W03.MultiplicationMachine.output_port _root_.OAI.KS.W03.MultiplicationMachine.stack_count _root_.OAI.KS.W03.MultiplicationMachine.state_count _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W06.RationalSignClassifier.program_output
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurTableMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem guard_empty (body : Program 32) (port : Fin 32) (s : Fin 32 → List Bool)
    (hs : s port = []) (coin : Bool) :
    (KS.W29.FixedLoop.loop body (guard port)).toMachine.step
      ⟨some (KS.W29.FixedLoop.guardState body),s⟩ coin = ⟨none,s⟩ := by
  rw [KS.W29.FixedLoop.step_guard]
  apply congrArg₂ Config.mk
  · simp [guard,KS.W29.FixedLoop.guardInstruction,observedHeads,hs,KS.W29.topCode]
    rfl
  · funext j
    by_cases hj : j=port
    · subst j; simp [guard,KS.W29.FixedLoop.guardInstruction,observedHeads,hs,KS.W29.topCode,Instruction.action,KS.W29.StackAction.apply]
    · simp [guard,KS.W29.FixedLoop.guardInstruction,observedHeads,hs,KS.W29.topCode,Instruction.action,KS.W29.StackAction.apply,hj]

theorem guard_cons (body : Program 32) (port : Fin 32) (s : Fin 32 → List Bool)
    (count : List Bool) (hs : s port = true :: count) (coin : Bool) :
    (KS.W29.FixedLoop.loop body (guard port)).toMachine.step
      ⟨some (KS.W29.FixedLoop.guardState body),s⟩ coin =
      KS.W29.FixedLoop.liftBody body ⟨some body.initial,Function.update s port count⟩ := by
  rw [KS.W29.FixedLoop.step_guard]
  apply congrArg₂ Config.mk
  · simp [guard,KS.W29.FixedLoop.guardInstruction,observedHeads,hs,KS.W29.topCode]
  · funext j
    by_cases hj : j=port
    · subst j; simp [guard,KS.W29.FixedLoop.guardInstruction,observedHeads,hs,KS.W29.topCode,Instruction.action,KS.W29.StackAction.apply]
    · simp [guard,KS.W29.FixedLoop.guardInstruction,observedHeads,hs,KS.W29.topCode,Instruction.action,KS.W29.StackAction.apply,hj]

end KS.W07.SchurTableMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_SchurLoopState
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurLoopState
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def columnTicks {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ) (i j : Fin n) (rows cols : ℕ) : ℕ :=
  ((SchurOperands.readBudget M B i j (columnState M i.val j.val rows cols) +
    SchurCellMachine.ticks (DenseRatMatrix.decode M i.succ j.succ)
      (DenseRatMatrix.decode M i.succ 0) (DenseRatMatrix.decode M 0 j.succ)
      (DenseRatMatrix.decode M 0 0)) +
    (6*KS.W01.ratLength (KS.W17.schurTail (DenseRatMatrix.decode M) i j)+5)) +
    (2*(Computability.encodeNat (j.val+1)).length+6)

end KS.W07.SchurLoopState

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

theorem some_index {n : ℕ} (M : DenseRatMatrix (n+1)) (j : Fin n)
    (h : firstNonzeroOffDiagonal (DenseRatMatrix.decode M) = some j) :
    (PivotRowLoop.outcome M 1 n).found = true ∧ (PivotRowLoop.outcome M 1 n).index = j.succ.val := by
  have he := PivotRowLoop.offDiagonal_outcome M
  rw [h] at he
  cases hf : (PivotRowLoop.outcome M 1 n).found
  · simp [PivotRowLoop.foundIndex,hf] at he
  · refine ⟨rfl,?_⟩
    simpa [PivotRowLoop.foundIndex,hf] using he

theorem result_negative {n : ℕ} (M : DenseRatMatrix (n+1))
    (hn : DenseRatMatrix.decode M 0 0 < 0) :
    result M = Function.update (PivotRowLoop.initial M) 29 [false] := by
  simp [result,hn.ne,KS.W06.RationalSignClassifier.outputCode,hn]

theorem result_sparse {n : ℕ} (M : DenseRatMatrix (n+1)) (j : Fin n)
    (hz : DenseRatMatrix.decode M 0 0 = 0)
    (hj : firstNonzeroOffDiagonal (DenseRatMatrix.decode M) = some j) :
    result M = PivotRowLoop.finished M j.succ.val true := by
  obtain ⟨hf,hi⟩ := some_index M j hj
  simp [result,hz,hf,hi]

end KS.W17.PivotDecision

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_PencilCompileRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

def blockDiagonal : Realizes (prodCode matrixCode matrixCode) matrixCode blockDiagonalData :=
  let A := first matrixCode matrixCode
  let B := second matrixCode matrixCode
  let n := A.then (lengthList vectorCode)
  let m := B.then (lengthList vectorCode)
  ((A.both ((n.both m).then zeroRect)).both (((m.both n).then zeroRect).both B)).then fromBlocks

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialStored
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {α β γ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}

instance poly_binarySucc : PolyTime binarySucc := ⟨⟨2*X+6,fun _ => le_rfl⟩⟩
instance size_binarySucc : IterateSize binarySucc := by
  refine ⟨⟨2*X+2,?_⟩⟩
  intro x n
  rw [Nat.succ_iterate]
  change KS.W01.natPayloadLength (x+n)≤2*(KS.W01.natPayloadLength x+n)+2
  rw [KS.W01.natPayloadLength_eq_size,KS.W01.natPayloadLength_eq_size]
  have hx : x<2^(x.size+n) := (Nat.lt_size_self x).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hn : n<2^(x.size+n) := (Nat.lt_two_pow_self (n:=n)).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have ht : (x+n).size≤x.size+n+1 := Nat.size_le.mpr (by rw [pow_succ];omega)
  omega

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ValueEvalRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

def Realizes.blockWith {α : Type*} {ea : α → Word} {f g : α → MatrixData}
    (r : Realizes ea matrixCode f) (s : Realizes ea matrixCode g) :
    Realizes ea matrixCode (fun p => blockDiagonalData (f p,g p)) := (r.both s).then blockDiagonal

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_BinaryArithmetic
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Binary arithmetic. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

def wordCons (b : Bool) : Realizes wordCode wordCode (fun w => b::w) where
  cost := fun _ => 1
  routine := {
    scratch := 0
    program := KS.W07.SchurCounters.pushProgram 0 b
    spec := fun w => by
      have h := KS.W07.SchurCounters.push_spec (0 : Fin 1) b (io w)
      convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
      funext j; fin_cases j; rfl }
instance poly_wordCons (b : Bool) : PolyTime (wordCons b) := ⟨⟨1,fun _ => le_rfl⟩⟩

def binaryToRat : Realizes binaryNatCode ratCode (fun n => (n:ℚ)) :=
  ((((identity binaryNatCode).both (constant binaryNatCode KS.W01.encodeNat 1)).changeOutput
    wordCode (fun n => prodCode binaryNatCode KS.W01.encodeNat (n,1)) (fun _ => rfl)).then
    (wordCons false)).changeOutput ratCode (fun n => (n:ℚ)) (fun n => by
      simp only [ratCode,KS.W01.encodeRat,Rat.num_natCast,Rat.den_natCast,
        KS.W01.encodeInt,prodCode,PairRoutine.pair,binaryNatCode,KS.W01.encodeNat]
      rfl)

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_BitBound
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation bit bound. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack

def meshRaw : Realizes meshPointCode matrixObjectCode (fun a => ⟨a.graph.n,rawMatrix a.v⟩) :=
  ((meshGraph.then numVertices).both
    ((((meshGraph.then numVertices).both (meshGraph.then numEdges)).both meshVector).then raw)).changeOutput
      matrixObjectCode (fun a => ⟨a.graph.n,rawMatrix a.v⟩) (by
        intro a
        change prodCode natCode matrixCode (a.graph.n,
          (List.range a.graph.n).map (fun i => (List.range a.graph.n).map
            (fun j => (List.ofFn a.v).getD (j+a.graph.n*i) 0)))=_
        rw [raw_data];rfl)

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_RationalMatrix_InverseRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inverse realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23 Matrix
open AlgorithmicThinTrees

def solveTopRow : Realizes rhsCode ratCode
    (fun p => ((matrixData p.1.1.2.2).getD 0 []).getD (p.2+1) 0) :=
  let A := rhsBase.then solveColumnEntries
  let i := rhsIndex.then natSucc
  (A.both ((constant rhsCode natCode 0).both i)).then matrixEntry

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_Realization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Signing realization. -/

section

namespace AlgorithmicThinTrees.Signing.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix

def stack : Realizes pairCode frameCode FramePair.stack :=
  let dims := ((pairLeft.then frameDim).both (pairRight.then frameDim)).then natAdd
  let rows := ((pairLeft.then frameRows).both (pairRight.then frameRows)).then
    ((appendList ratCode).zipWith [] [])
  (dims.both rows).changeOutput frameCode FramePair.stack (by
    intro a
    change frameDataCode (_,_) = frameDataCode _
    congr 1
    change (a.a+a.b,zipDefault (fun p : List ℚ × List ℚ => p.1 ++ p.2) [] []
      (List.ofFn (fun i : Fin a.m => List.ofFn (a.u i)),
        List.ofFn (fun i : Fin a.m => List.ofFn (a.v i)))) =
      (a.a+a.b,List.ofFn (fun i : Fin a.m => List.ofFn (StackedSigning.stack (a.u i) (a.v i))))
    rw [zipDefault_ofFn]
    simp only [stack_data])

end AlgorithmicThinTrees.Signing.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_WordHead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word head. -/

section

namespace CurrentKS.WordHead
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open CleanRoutine PairRoutine

def flag : Program 3 := ofMachine (compile 0 0 1 dispatch)
def program : Program 3 := compose flag (compose (KS.W04.BinaryStackMoves.clearProgram 0)
  (transfer 1 2 0))
end CurrentKS.WordHead

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_InputArrays
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Input arrays. -/

section

namespace AlgorithmicThinTrees.InputStack
open StrongThinTree Finset CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open GraphicHalf.Stack

def eN := eNBinary.then binaryToNat
def eM := eMBinary.then binaryToNat
def eK := eKBinary.then binaryToNat
def bN := bNBinary.then binaryToNat
def bP := bPBinary.then binaryToNat

def eEndpoint (right : Bool) := (eEndpointBinary right).then binaryToNat

def bEndpoint (right : Bool) := (bEndpointBinary right).then binaryToNat

end AlgorithmicThinTrees.InputStack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_InputExpansion
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Input expansion. -/

section

namespace AlgorithmicThinTrees.InputStack
open StrongThinTree Finset CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open GraphicHalf.Stack GraphStack

def ePrepare : Realizes eCode problemCode eProblem :=
  ((eN.both (((eEndpoint false).tabulateFin eM).both ((eEndpoint true).tabulateFin eM))).both eK)
    |>.changeOutput problemCode eProblem (by
      intro x
      rw [makeProblem_code]
      rfl)

def bMultiplicityRat : Realizes bRecCode ratCode (fun x => (x.1.val.multiplicity x.2:ℚ)) :=
  ((bRecordBinary 2).then binaryToRat).congr (fun _ => rfl)

end AlgorithmicThinTrees.InputStack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_SelectionRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selection realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23 Finset
open AlgorithmicThinTrees.OrderedGraph

variable {α : Type*}

def maskArray (ea : α → Word) (z : α) : Realizes (prodCode boolsCode (listCode ea)) (listCode ea)
    (fun p => (zipDefault (fun q : Bool×α => if q.1 then [q.2] else []) false z p).flatten) :=
  ((maskEntry ea).zipWith false z).then (joinList ea)

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_InputOutput
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

def lookupPair : Realizes (prodCode indicesCode natCode) fieldsCode
    (fun p => [p.1.getD p.2 0,0]) :=
  (((((second indicesCode natCode).both (first indicesCode natCode)).then (getD natCode 0)).then
    natToBinary).both (constant (prodCode indicesCode natCode) fieldsCode [0])).then
      (consList binaryNatCode)

def pairsOutput : Realizes (prodCode indicesCode indicesCode) fieldsCode
    (fun p => (p.2.map (fun i => [p.1.getD i 0,0])).flatten) :=
  lookupPair.mapCtx.then (joinList binaryNatCode)

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

def binaryTail : Realizes (fun x : {x : Large // isBinary x.val=true} => largeCode x.val)
    bCode asBinary :=
  (wordTail.reindex (fun x : {x : Large // isBinary x.val=true} => largeCode x.val)
    (fun x => largeCode x.val) (fun _ => rfl)).changeOutput bCode asBinary (by
      rintro ⟨⟨x|x,hv,hn⟩,hb⟩
      · cases hb
      · rfl)
def explicitTail : Realizes (fun x : {x : Large // ¬isBinary x.val=true} => largeCode x.val)
    eCode asExplicit :=
  (wordTail.reindex (fun x : {x : Large // ¬isBinary x.val=true} => largeCode x.val)
    (fun x => largeCode x.val) (fun _ => rfl)).changeOutput eCode asExplicit (by
      rintro ⟨⟨x|x,hv,hn⟩,hb⟩
      · rfl
      · exact (hb rfl).elim)
instance poly_binaryTail : PolyTime binaryTail := by unfold binaryTail;infer_instance
instance poly_explicitTail : PolyTime explicitTail := by unfold explicitTail;infer_instance

def goodFields : Realizes goodCode fieldsCode (fun x => inputFields x.val) :=
  (wordTail.reindex goodCode goodCode (fun _ => rfl)).changeOutput fieldsCode
    (fun x => inputFields x.val) (fun x => (inputFields_code x.val).symm)
instance poly_goodFields : PolyTime goodFields := by unfold goodFields;infer_instance

def goodN : Realizes goodCode binaryNatCode (fun x => x.val.n) :=
  (goodFields.then (field 0)).congr (by rintro ⟨x|x,h⟩ <;> rfl)

def singletonTest : Realizes goodCode boolCode (fun x => decide (x.val.n=1)) :=
  ((goodN.then binaryToRat).le (constant goodCode ratCode 1)).congr (by
    intro x
    have hn : 1 ≤ x.val.n := valid_n x.property
    simp only [Nat.cast_le_one]
    have he : (x.val.n ≤ 1) ↔ x.val.n=1 := by omega
    simp only [he])

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

namespace CurrentKS.Realization
open CleanRoutine
variable {α : Type*} {ea : α → Word} {f : α → Word}

def realizedMachine (r : Realizes ea wordCode f) : CurrentKS.Machine :=
  ArchivedMachine.machine ({r.routine.program with input := 0,output := 0}.toMachine)

end CurrentKS.Realization

end

end OAI
end


