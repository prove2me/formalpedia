-- Prove2me | Definitions.Def_OAIQ241TT001
-- name    : OAIQ241TT001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:47:46.286413+00:00
-- url     : https://prove2.me/theorems/fc801c60-e144-4afe-bacc-77d842538076
-- title:
--   Definitions bundle OAIQ241TT001 of the split of OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 850 declarations of OpenAI's Lean: 508 definitions, 18 inductive types or structures, 4 instances and 320 theorems. The definitions and types are `OAI.AlgorithmicThinTrees.GraphicHalf.Numeric`, `OAI.AlgorithmicThinTrees.GraphicHalf.halfError`, `OAI.AlgorithmicThinTrees.GraphicHalf.positiveForm`, `OAI.AlgorithmicThinTrees.GraphicHalf.varianceBound`, `OAI.AlgorithmicThinTrees.MetricTests.DistinctTriple`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Form`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.MatBlock`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.ScalarBlock`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.triangleAt`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.State`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.State.active`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.State.packingTarget`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Triple`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Var`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.baselineQ`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.blockLength`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.blocks`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.dimension`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.edgeIndex`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.errorQ`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.flow`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.flowA`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.flowB`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.flowIndex`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.flowX`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.gain`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.index`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.matIndex`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.matrixForm`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.mulIndex`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.multiplier`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.order`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.qdiff`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.qproject`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.qresponse`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.qtriangle`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.radiusQ`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.rawMatrix`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.rowIndex` and 486 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `MatrixSigning_Arithmetic_ArithmeticBounds`, `MatrixSigning_Arithmetic_BinaryAdder`, `MatrixSigning_Arithmetic_BinaryAdderCompose`, `MatrixSigning_Arithmetic_BinaryDivision`, `MatrixSigning_Arithmetic_BinaryGCD`, `MatrixSigning_Arithmetic_BinaryMultiply`, `MatrixSigning_Arithmetic_BinaryRationalAdd`, `MatrixSigning_Arithmetic_BinaryRationalCanonical`, `MatrixSigning_Arithmetic_BinaryRationalCore`, `MatrixSigning_Arithmetic_BinaryRationalNormalize`, `MatrixSigning_Arithmetic_BinarySubtractor`, `MatrixSigning_Arithmetic_BorrowSubtractor`, `MatrixSigning_Arithmetic_CleanRationalCompare`, `MatrixSigning_Arithmetic_ComplexScalarNodes`, `MatrixSigning_Arithmetic_DivisionBodyTime`, `MatrixSigning_Arithmetic_DivisionCompatibility`, `MatrixSigning_Arithmetic_DivisionInput`, `MatrixSigning_Arithmetic_DivisionLoopBridge`, `MatrixSigning_Arithmetic_DivisionLoopModel`, `MatrixSigning_Arithmetic_DivisionMachine`, `MatrixSigning_Arithmetic_DivisionOutput`, `MatrixSigning_Arithmetic_EncodedDivision`, `MatrixSigning_Arithmetic_FixedBinaryAdder`, `MatrixSigning_Arithmetic_FloorRationalMachine`, `MatrixSigning_Arithmetic_GCDMachine`, `MatrixSigning_Arithmetic_GCDMachineRun`, `MatrixSigning_Arithmetic_GCDMachineStep`, `MatrixSigning_Arithmetic_MultiplicationBody`, `MatrixSigning_Arithmetic_MultiplicationInitialize`, `MatrixSigning_Arithmetic_MultiplicationLoop`, `MatrixSigning_Arithmetic_NegativeDivision`, `MatrixSigning_Arithmetic_RationalAddModel`, `MatrixSigning_Arithmetic_RationalAddPrimitives`, `MatrixSigning_Arithmetic_RationalAddProducts`, `MatrixSigning_Arithmetic_RationalAddProgram`, `MatrixSigning_Arithmetic_RationalAddSigned`, `MatrixSigning_Arithmetic_RationalBounds`, `MatrixSigning_Arithmetic_RationalCompareBranch`, `MatrixSigning_Arithmetic_RationalCompareCorrectness`, `MatrixSigning_Arithmetic_RationalCompareParser`, `MatrixSigning_Arithmetic_RationalComparePrimitives`, `MatrixSigning_Arithmetic_RationalCompareProgram`, `MatrixSigning_Arithmetic_RationalDivisionStages`, `MatrixSigning_Arithmetic_RationalMagnitudeDivision`, `MatrixSigning_Arithmetic_RationalMagnitudeMachine`, `MatrixSigning_Arithmetic_RationalMagnitudePositive`, `MatrixSigning_Arithmetic_RationalMagnitudeSetup`, `MatrixSigning_Arithmetic_RationalMultiplyNormalize`, `MatrixSigning_Arithmetic_RationalMultiplyProducts`, `MatrixSigning_Arithmetic_RationalReciprocalCore`, `MatrixSigning_Arithmetic_RationalReciprocalMachine`, `MatrixSigning_Arithmetic_RationalReciprocalSwap`, `MatrixSigning_Arithmetic_RationalSignAction`, `MatrixSigning_Arithmetic_RationalSignClassifier`, `MatrixSigning_Arithmetic_RationalSubtractProgram`, `MatrixSigning_Arithmetic_SignedRationalSerializer`, `MatrixSigning_Arithmetic_SingleRationalParser`, `MatrixSigning_Arithmetic_SparseScalarNodes`, `MatrixSigning_Arithmetic_SubtractionBorrow`, `MatrixSigning_Arithmetic_UnaryArithmetic`, `MatrixSigning_Arithmetic_ZeroPaddedRow`, `MatrixSigning_Complexity_ComplexScalarCosts`, `MatrixSigning_Complexity_GCDMachinePolynomial`, `MatrixSigning_Complexity_NaturalPolynomial`, `MatrixSigning_Complexity_PSDControllerPolynomial`, `MatrixSigning_Complexity_RationalCost`, `MatrixSigning_Complexity_SchurCellCost`, `MatrixSigning_Complexity_SchurPolynomialBound`, `MatrixSigning_Complexity_StorageCost`, `MatrixSigning_Encoding_BinaryEncoding`, `MatrixSigning_Encoding_FramedArrayPrefix`, `MatrixSigning_Encoding_FramedArrayRetrieval`, `MatrixSigning_Encoding_FramedArraySkip`, `MatrixSigning_Encoding_ReusableArrayLookup`, `MatrixSigning_Encoding_UnsignedPairSerializer`, `MatrixSigning_Encoding_WireAppend`, `MatrixSigning_Encoding_WireMagnitude`, `MatrixSigning_Encoding_WireProgramPrimitives`, `MatrixSigning_Encoding_ZeroArrayConstructor`, `MatrixSigning_Machines_BinaryAccumulator`, `MatrixSigning_Machines_BinaryMachine`, `MatrixSigning_Machines_BinaryNormalize`, `MatrixSigning_Machines_BinaryToUnaryMachine`, `MatrixSigning_Machines_CommonDenominatorLift`, `MatrixSigning_Machines_ControllerReachable`, `MatrixSigning_Machines_ControllerReplayBound`, `MatrixSigning_Machines_ControllerRuntime`, `MatrixSigning_Machines_ControllerTerminalBound`, `MatrixSigning_Machines_DenseFieldCounter`, `MatrixSigning_Machines_ExpressionPrimitives`, `MatrixSigning_Machines_FixedCompare`, `MatrixSigning_Machines_FixedDotControl`, `MatrixSigning_Machines_FixedDotMachine`, `MatrixSigning_Machines_FixedDotModel`, `MatrixSigning_Machines_FixedDotPrimitives`, `MatrixSigning_Machines_InverseHeight`, `MatrixSigning_Machines_LittleEndianCompare`, `MatrixSigning_Machines_MagnitudeProgram`, `MatrixSigning_Machines_NestedSchur`, `MatrixSigning_Machines_SchurBounds`, `MatrixSigning_Machines_SchurCellMachine`, `MatrixSigning_Machines_SchurColumnLoop`, `MatrixSigning_Machines_SchurDimension`, `MatrixSigning_Machines_SchurEntryMachine`, `MatrixSigning_Machines_SchurInputLength`, `MatrixSigning_Machines_SchurOperands`, `MatrixSigning_Machines_SchurReadStage`, `MatrixSigning_Machines_SchurRowLoop`, `MatrixSigning_Machines_SchurTableCorrectness`, `MatrixSigning_Machines_SchurTableMachine`, `MatrixSigning_Machines_SignedFloorMachine`, `MatrixSigning_Machines_SignedFloorModel`, `MatrixSigning_Machines_SparseCoefficientStage`, `MatrixSigning_Machines_TerminalReadStage`, `MatrixSigning_Machines_TerminalSparseAssembly`, `MatrixSigning_Machines_TerminalVectorReplace`, `MatrixSigning_Machines_TerminalZeroVector`, `MatrixSigning_Matrices_DenseElimination`, `MatrixSigning_Matrices_DenseMatrixSerialization`, `MatrixSigning_Matrices_DenseRatMatrix`, `MatrixSigning_Matrices_DeterminantBounds`, `MatrixSigning_Matrices_MatrixAddressArithmetic`, `MatrixSigning_Matrices_MatrixCursorPreparation`, `MatrixSigning_Matrices_MatrixReadProgram`, `MatrixSigning_Matrices_Pivot`, `MatrixSigning_Matrices_PivotDecisionPorts`, `MatrixSigning_Matrices_PivotHistory`, `MatrixSigning_Matrices_PivotHistoryBounds`, `MatrixSigning_Matrices_PivotHistoryMachine`, `MatrixSigning_Matrices_PivotReachableBounds`, `MatrixSigning_Matrices_PivotRowBody`, `MatrixSigning_Matrices_PivotRowClassify`, `MatrixSigning_Matrices_PivotRowCorrectness`, `MatrixSigning_Matrices_PivotRowFinish`, `MatrixSigning_Matrices_PivotRowInitialize`, `MatrixSigning_Matrices_PivotRowLoop`, `MatrixSigning_Matrices_PivotScannerBounds`, `MatrixSigning_Matrices_RowDotCounter`, `MatrixSigning_Matrices_RowDotMachine`, `MatrixSigning_Matrices_RowDotModel`, `MatrixSigning_Matrices_RowDotPrimitives`, `MatrixSigning_Matrices_RowDotRegisters`, `MatrixSigning_Matrices_SavedPivotPacketMachine`, `MatrixSigning_Matrices_UniformElimination`, `MatrixSigning_Optimization_EliminationWitnessHeight`, `MatrixSigning_Optimization_PivotDescentBounds`, `MatrixSigning_Optimization_PivotDescentMachine`, `MatrixSigning_Optimization_PivotWitnessMachine`, `MatrixSigning_Optimization_StoredWitnessLift`, `MatrixSigning_Optimization_TerminalWitnessBounds`, `MatrixSigning_Optimization_TerminalWitnessTapes`, `MatrixSigning_Realization_ArrayRealization`, `MatrixSigning_Realization_EndpointRealization`, `MatrixSigning_Realization_FaceArrayRealization`, `MatrixSigning_Realization_FaceChoiceRealization`, `MatrixSigning_Realization_FaceQueryRealization`, `MatrixSigning_Realization_FramedMapRoutine`, `MatrixSigning_Realization_OriginalFieldsRealization`, `MatrixSigning_Realization_OriginalSignRealization`, `MatrixSigning_Realization_PencilCompileRealization`, `MatrixSigning_Realization_RootRealization`, `MatrixSigning_Realization_RoundedStepRealization`, `MatrixSigning_Realization_ScalarRealization`, `MatrixSigning_Realization_SelectionRealization`, `MatrixSigning_Realization_StoredPSDRealization`, `MatrixSigning_Realization_VarianceRealization`, `MatrixSigning_Realization_VectorRealization`, `ThinTrees_Arithmetic_UnaryArithmetic`, `ThinTrees_Arithmetic_UnaryRoot`, `ThinTrees_Continuation_Coordinates`, `ThinTrees_Continuation_Encoding`, `ThinTrees_Continuation_Feasibility`, `ThinTrees_Continuation_Iteration`, `ThinTrees_Continuation_Pencil`, `ThinTrees_Continuation_Schedule`, `ThinTrees_Continuation_Search`, `ThinTrees_Continuation_SpectralSize`, `ThinTrees_Duality`, `ThinTrees_ExtractionBounds`, `ThinTrees_Flow_RootedRelaxation`, `ThinTrees_GraphMatrix`, `ThinTrees_Metric_CenteredMatrices`, `ThinTrees_Metric_ConeRepresentation`, `ThinTrees_Metric_MatrixBound`, `ThinTrees_Normalization_Algorithm`, `ThinTrees_Normalization_Descent`, `ThinTrees_Normalization_Realization`, `ThinTrees_Pencil_AffinePencil`, `ThinTrees_Pencil_BlockAssembly`, `ThinTrees_Pencil_FiniteFamilies`, `ThinTrees_Pencil_MatrixConstraintRealization`, `ThinTrees_Pencil_RationalAffineEval`, `ThinTrees_ShortcutDuality`, `ThinTrees_Signing_Realization`, `ThinTrees_Sparsification_GraphicHalf`, `ThinTrees_Sparsification_HalfNumeric`, `ThinTrees_Sparsification_ShortcutExtraction`.
--
--   **Imports.** It imports the published bundle `Def_AlgorithmicThinTrees`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ241TT004`, `OAIQ241TT005` and `OAIQ241TT006`; the proofs of `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedSequence.ordered_bound` and `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.capturePackage`.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_AlgorithmicThinTrees

section
-- module Solutions.OAIQ241_TT.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30

open scoped Rat

theorem divInt_num_natAbs_le (a b : ℤ) (hb : b ≠ 0) :
    (a /. b).num.natAbs ≤ a.natAbs := by
  by_cases ha : a = 0
  · simp [ha]
  · exact Int.natAbs_le_of_dvd_ne_zero (Rat.num_dvd a hb) ha

theorem divInt_den_le (a b : ℤ) (hb : b ≠ 0) :
    (a /. b).den ≤ b.natAbs := by
  simpa using Int.natAbs_le_of_dvd_ne_zero (Rat.den_dvd a b) hb

theorem divInt_num_size_le (a b : ℤ) (hb : b ≠ 0) (k : ℕ)
    (ha : a.natAbs < 2 ^ k) : Nat.size (a /. b).num.natAbs ≤ k := by
  exact Nat.size_le.mpr (lt_of_le_of_lt (divInt_num_natAbs_le a b hb) ha)

theorem divInt_den_size_le (a b : ℤ) (hb : b ≠ 0) (k : ℕ)
    (hsize : b.natAbs < 2 ^ k) : Nat.size (a /. b).den ≤ k := by
  exact Nat.size_le.mpr (lt_of_le_of_lt (divInt_den_le a b hb) hsize)

theorem matrix_den_dvd_prod {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    A.den ∣ ∏ p : Fin m × Fin n, (A p.1 p.2).den := by
  apply Matrix.den_dvd_iff.mpr
  intro i j
  exact Finset.dvd_prod_of_mem (fun p : Fin m × Fin n => (A p.1 p.2).den)
    (Finset.mem_univ (i, j))

theorem matrix_den_le_prod {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    A.den ≤ ∏ p : Fin m × Fin n, (A p.1 p.2).den := by
  apply Nat.le_of_dvd _ (matrix_den_dvd_prod A)
  apply Finset.prod_pos
  intro p _
  exact Nat.pos_of_ne_zero (A p.1 p.2).den_nz

theorem matrix_den_le_two_pow {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : ℕ)
    (hA : ∀ i j, (A i j).den ≤ 2 ^ b) :
    A.den ≤ 2 ^ (b * (m * n)) := by
  calc
    A.den ≤ ∏ p : Fin m × Fin n, (A p.1 p.2).den := matrix_den_le_prod A
    _ ≤ ∏ _p : Fin m × Fin n, 2 ^ b := by
      exact Finset.prod_le_prod' (fun entry _ => hA entry.1 entry.2)
    _ = 2 ^ (b * (m * n)) := by simp [← pow_mul]

theorem cleared_matrix_entry {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (i : Fin m) (j : Fin n) :
    (A.num i j : ℚ) = (A.den : ℚ) * A i j := by
  have h := Matrix.num_div_den A i j
  apply (div_eq_iff (Nat.cast_ne_zero.mpr A.den_ne_zero)).mp at h
  simpa [mul_comm] using h

theorem cleared_num_natAbs_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (i : Fin m) (j : Fin n) :
    (A.num i j).natAbs ≤ A.den * (A i j).num.natAbs := by
  obtain ⟨k, hk⟩ := Matrix.den_dvd_iff.mp (dvd_refl A.den) i j
  have heq : A.num i j = (k : ℤ) * (A i j).num := by
    have hc : (A.num i j : ℚ) = (((k : ℤ) * (A i j).num : ℤ) : ℚ) := by
      rw [cleared_matrix_entry, hk, Nat.cast_mul]
      calc
        ((A i j).den : ℚ) * k * A i j = (k : ℚ) * ((A i j).den * A i j) := by ring
        _ = (k : ℚ) * (A i j).num := by rw [Rat.den_mul_eq_num]
        _ = (((k : ℤ) * (A i j).num : ℤ) : ℚ) := by simp
    exact_mod_cast hc
  have hk_le : k ≤ A.den := by
    rw [hk]
    exact Nat.le_mul_of_pos_left k (Nat.pos_of_ne_zero (A i j).den_nz)
  rw [heq, Int.natAbs_mul, Int.natAbs_natCast]
  exact Nat.mul_le_mul_right _ hk_le

theorem cleared_num_le_two_pow {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : ℕ)
    (hnum : ∀ i j, (A i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (A i j).den ≤ 2 ^ b) (i : Fin m) (j : Fin n) :
    (A.num i j).natAbs ≤ 2 ^ (b * (m * n) + b) := by
  calc
    (A.num i j).natAbs ≤ A.den * (A i j).num.natAbs := cleared_num_natAbs_le A i j
    _ ≤ 2 ^ (b * (m * n)) * 2 ^ b :=
      Nat.mul_le_mul (matrix_den_le_two_pow A b hden) (hnum i j)
    _ = 2 ^ (b * (m * n) + b) := (pow_add 2 _ _).symm

end KS.W30

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_ArithmeticBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30

open scoped Rat

theorem mul_num_natAbs_le (q r : ℚ) :
    (q * r).num.natAbs ≤ q.num.natAbs * r.num.natAbs := by
  have heq : q * r = (q.num * r.num) /. ((q.den : ℤ) * r.den) := by
    simpa only [Rat.num_divInt_den] using
      (Rat.divInt_mul_divInt q.num r.num :
        q.num /. (q.den : ℤ) * (r.num /. (r.den : ℤ)) =
          (q.num * r.num) /. ((q.den : ℤ) * r.den))
  rw [heq]
  simpa only [Int.natAbs_mul] using
    divInt_num_natAbs_le (q.num * r.num) ((q.den : ℤ) * r.den)
      (mul_ne_zero (Int.natCast_ne_zero.mpr q.den_nz)
        (Int.natCast_ne_zero.mpr r.den_nz))

theorem mul_den_le (q r : ℚ) : (q * r).den ≤ q.den * r.den :=
  Nat.le_of_dvd (Nat.mul_pos q.den_pos r.den_pos) (Rat.mul_den_dvd q r)

theorem add_num_natAbs_le (q r : ℚ) :
    (q + r).num.natAbs ≤ q.num.natAbs * r.den + q.den * r.num.natAbs := by
  rw [Rat.add_num_den]
  apply le_trans (divInt_num_natAbs_le _ _
    (mul_ne_zero (Int.natCast_ne_zero.mpr q.den_nz)
      (Int.natCast_ne_zero.mpr r.den_nz)))
  simpa only [Int.natAbs_mul, Int.natAbs_natCast] using
    Int.natAbs_add_le (q.num * r.den) ((q.den : ℤ) * r.num)

theorem add_den_le (q r : ℚ) : (q + r).den ≤ q.den * r.den :=
  Nat.le_of_dvd (Nat.mul_pos q.den_pos r.den_pos) (Rat.add_den_dvd q r)

theorem mul_parts_le_two_pow (q r : ℚ) (b c : ℕ)
    (hqnum : q.num.natAbs ≤ 2 ^ b) (hqden : q.den ≤ 2 ^ b)
    (hrnum : r.num.natAbs ≤ 2 ^ c) (hrden : r.den ≤ 2 ^ c) :
    (q * r).num.natAbs ≤ 2 ^ (b + c) ∧ (q * r).den ≤ 2 ^ (b + c) := by
  constructor
  · exact (mul_num_natAbs_le q r).trans (by
      simpa only [pow_add] using Nat.mul_le_mul hqnum hrnum)
  · exact (mul_den_le q r).trans (by
      simpa only [pow_add] using Nat.mul_le_mul hqden hrden)

theorem add_parts_le_two_pow (q r : ℚ) (b c : ℕ)
    (hqnum : q.num.natAbs ≤ 2 ^ b) (hqden : q.den ≤ 2 ^ b)
    (hrnum : r.num.natAbs ≤ 2 ^ c) (hrden : r.den ≤ 2 ^ c) :
    (q + r).num.natAbs ≤ 2 ^ (b + c + 1) ∧ (q + r).den ≤ 2 ^ (b + c) := by
  constructor
  · apply (add_num_natAbs_le q r).trans
    have h := Nat.add_le_add (Nat.mul_le_mul hqnum hrden) (Nat.mul_le_mul hqden hrnum)
    simpa only [pow_succ, pow_add, mul_two] using h
  · exact (add_den_le q r).trans (by
      simpa only [pow_add] using Nat.mul_le_mul hqden hrden)

theorem inv_parts_le_two_pow (q : ℚ) (b : ℕ)
    (hqnum : q.num.natAbs ≤ 2 ^ b) (hqden : q.den ≤ 2 ^ b) :
    q⁻¹.num.natAbs ≤ 2 ^ b ∧ q⁻¹.den ≤ 2 ^ b := by
  by_cases hz : q.num = 0
  · simp [Rat.num_inv, Rat.den_inv, hz, Nat.one_le_two_pow]
  · simpa only [Rat.num_inv, Rat.den_inv, hz, ite_false, if_false, Int.natAbs_mul,
      Int.natAbs_sign_of_ne_zero hz, Int.natAbs_natCast, one_mul] using
      And.intro hqden hqnum

theorem div_parts_le_two_pow (q r : ℚ) (b c : ℕ)
    (hqnum : q.num.natAbs ≤ 2 ^ b) (hqden : q.den ≤ 2 ^ b)
    (hrnum : r.num.natAbs ≤ 2 ^ c) (hrden : r.den ≤ 2 ^ c) :
    (q / r).num.natAbs ≤ 2 ^ (b + c) ∧ (q / r).den ≤ 2 ^ (b + c) := by
  have hi := inv_parts_le_two_pow r c hrnum hrden
  simpa only [div_eq_mul_inv] using mul_parts_le_two_pow q r⁻¹ b c hqnum hqden hi.1 hi.2

end KS.W30

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_BinaryEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W01

theorem length_encodePosNum (n : PosNum) :
    (Computability.encodePosNum n).length = n.natSize := by
  induction n <;> simp_all [Computability.encodePosNum, PosNum.natSize]

theorem length_encodeNum (n : Num) :
    (Computability.encodeNum n).length = n.natSize := by
  cases n with
  | zero => rfl
  | pos p => exact length_encodePosNum p

end KS.W01

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_BinaryDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19

def digit (b : Bool) : ℕ := if b then 1 else 0

@[simp] theorem digit_false : digit false = 0 := rfl
@[simp] theorem digit_true : digit true = 1 := rfl

def bitsValue : List Bool → ℕ
  | [] => 0
  | b :: bs => digit b + 2 * bitsValue bs

theorem digit_le_one (b : Bool) : digit b ≤ 1 := by cases b <;> decide

def compareDigit (a b : Bool) : Ordering :=
  if a then (if b then .eq else .gt) else (if b then .lt else .eq)

def compareBits : List Bool → List Bool → Ordering
  | [], [] => .eq
  | [], b :: bs => match compareBits [] bs with
    | .eq => compareDigit false b
    | o => o
  | a :: as, [] => match compareBits as [] with
    | .eq => compareDigit a false
    | o => o
  | a :: as, b :: bs => match compareBits as bs with
    | .eq => compareDigit a b
    | o => o
termination_by xs ys => xs.length + ys.length
decreasing_by all_goals simp_wf <;> omega

def OrderingCorrect (o : Ordering) (a b : ℕ) : Prop :=
  match o with
  | .lt => a < b
  | .eq => a = b
  | .gt => b < a

theorem compareBits_correct (xs ys : List Bool) :
    OrderingCorrect (compareBits xs ys) (bitsValue xs) (bitsValue ys) := by
  induction xs generalizing ys with
  | nil =>
    induction ys with
    | nil => simp [compareBits, OrderingCorrect, bitsValue]
    | cons b bs ih =>
      cases hc : compareBits [] bs <;>
        simp only [hc, OrderingCorrect, bitsValue] at ih <;>
        cases b <;> simp [compareBits, hc, compareDigit, OrderingCorrect, bitsValue, digit] <;> omega
  | cons a as ih =>
    cases ys with
    | nil =>
      have h := ih []
      cases hc : compareBits as [] <;>
        simp only [hc, OrderingCorrect, bitsValue] at h <;>
        cases a <;> simp [compareBits, hc, compareDigit, OrderingCorrect, bitsValue, digit] <;> omega
    | cons b bs =>
      have h := ih bs
      cases hc : compareBits as bs <;>
        simp only [hc, OrderingCorrect] at h <;>
        cases a <;> cases b <;>
        simp [compareBits, hc, compareDigit, OrderingCorrect, bitsValue, digit] <;> omega

theorem compareBits_lt_iff (xs ys : List Bool) :
    compareBits xs ys = .lt ↔ bitsValue xs < bitsValue ys := by
  have h := compareBits_correct xs ys
  cases hc : compareBits xs ys <;> simp [hc, OrderingCorrect] at h ⊢ <;> omega

def differenceDigit (a b borrow : Bool) : Bool := Bool.xor (Bool.xor a b) borrow

def nextBorrow (a b borrow : Bool) : Bool :=
  (!a && (b || borrow)) || (b && borrow)

theorem subtraction_column (a b c : Bool) :
    digit a + 2 * digit (nextBorrow a b c) =
      digit (differenceDigit a b c) + digit b + digit c := by
  cases a <;> cases b <;> cases c <;> decide

def subtractBits : List Bool → List Bool → Bool → List Bool
  | [], [], _ => []
  | [], b :: bs, c => differenceDigit false b c :: subtractBits [] bs (nextBorrow false b c)
  | a :: as, [], c => differenceDigit a false c :: subtractBits as [] (nextBorrow a false c)
  | a :: as, b :: bs, c => differenceDigit a b c :: subtractBits as bs (nextBorrow a b c)
termination_by xs ys _ => xs.length + ys.length
decreasing_by all_goals simp_wf <;> omega

theorem tail_borrow_le (a b c : Bool) (x y : ℕ)
    (h : digit b + 2 * y + digit c ≤ digit a + 2 * x) :
    y + digit (nextBorrow a b c) ≤ x := by
  have he := subtraction_column a b c
  have ho := digit_le_one (differenceDigit a b c)
  omega

theorem subtraction_lift (a b c : Bool) (x y r : ℕ)
    (hr : r + y + digit (nextBorrow a b c) = x) :
    (digit (differenceDigit a b c) + 2 * r) + (digit b + 2 * y) + digit c =
      digit a + 2 * x := by
  have he := subtraction_column a b c
  omega

theorem subtractBits_correct (xs ys : List Bool) (c : Bool)
    (h : bitsValue ys + digit c ≤ bitsValue xs) :
    bitsValue (subtractBits xs ys c) + bitsValue ys + digit c = bitsValue xs := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil =>
      simp only [bitsValue, Nat.zero_add] at h
      simpa [subtractBits, bitsValue] using Nat.eq_zero_of_le_zero h
    | cons b bs ih =>
      have ht := tail_borrow_le false b c 0 (bitsValue bs) (by simpa [bitsValue, digit] using h)
      have hr := ih (nextBorrow false b c) (by simpa [bitsValue] using ht)
      have hh := subtraction_lift false b c 0 (bitsValue bs)
        (bitsValue (subtractBits [] bs (nextBorrow false b c))) (by simpa [bitsValue] using hr)
      simpa [subtractBits, bitsValue, digit] using hh
  | cons a as ih =>
    cases ys with
    | nil =>
      have ht := tail_borrow_le a false c (bitsValue as) 0 (by simpa [bitsValue, digit] using h)
      have hr := ih [] (nextBorrow a false c) (by simpa [bitsValue] using ht)
      have hh := subtraction_lift a false c (bitsValue as) 0
        (bitsValue (subtractBits as [] (nextBorrow a false c))) (by simpa [bitsValue] using hr)
      simpa [subtractBits, bitsValue, digit] using hh
    | cons b bs =>
      have ht := tail_borrow_le a b c (bitsValue as) (bitsValue bs) (by simpa [bitsValue] using h)
      have hr := ih bs (nextBorrow a b c) ht
      simpa only [subtractBits, bitsValue] using
        subtraction_lift a b c (bitsValue as) (bitsValue bs)
          (bitsValue (subtractBits as bs (nextBorrow a b c))) hr

theorem subtractBits_length (xs ys : List Bool) (c : Bool) :
    (subtractBits xs ys c).length = max xs.length ys.length := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => simp [subtractBits]
    | cons b bs ih => simp [subtractBits, ih]
  | cons a as ih =>
    cases ys with
    | nil => simp [subtractBits, ih]
    | cons b bs => simp only [subtractBits, List.length_cons, ih]; omega

def divideBits (divisor : List Bool) : List Bool → List Bool × List Bool
  | [] => ([], [])
  | b :: bs =>
    let qr := divideBits divisor bs
    let trial := b :: qr.2
    if compareBits trial divisor = .lt then
      (false :: qr.1, trial)
    else
      (true :: qr.1, subtractBits trial divisor false)

theorem divideBits_correct (divisor xs : List Bool) (hd : 0 < bitsValue divisor) :
    bitsValue xs = bitsValue divisor * bitsValue (divideBits divisor xs).1 +
      bitsValue (divideBits divisor xs).2 ∧
    bitsValue (divideBits divisor xs).2 < bitsValue divisor := by
  induction xs with
  | nil => simpa [divideBits, bitsValue] using hd
  | cons b bs ih =>
    have hb := digit_le_one b
    by_cases hc : compareBits (b :: (divideBits divisor bs).2) divisor = .lt
    · have hl := (compareBits_lt_iff _ _).mp hc
      simp only [divideBits, hc, ↓reduceIte]
      simp only [bitsValue, digit_false, Nat.zero_add] at hl ⊢
      constructor
      · nlinarith [ih.1]
      · exact hl
    · have hle : bitsValue divisor ≤ bitsValue (b :: (divideBits divisor bs).2) := by
        exact Nat.le_of_not_gt (fun h => hc ((compareBits_lt_iff _ _).mpr h))
      have hs := subtractBits_correct (b :: (divideBits divisor bs).2) divisor false
        (by simpa [digit] using hle)
      simp only [digit_false, Nat.add_zero] at hs
      simp only [divideBits, hc, ↓reduceIte, bitsValue, digit_true]
      simp only [bitsValue] at hs
      constructor
      · nlinarith [ih.1]
      · nlinarith [ih.2]

theorem bitsValue_encodePosNum (n : PosNum) :
    bitsValue (Computability.encodePosNum n) = (n : ℕ) := by
  induction n <;> simp_all [Computability.encodePosNum, bitsValue, digit, PosNum.cast_bit0,
    PosNum.cast_bit1] <;> omega

theorem bitsValue_encodeNum (n : Num) :
    bitsValue (Computability.encodeNum n) = (n : ℕ) := by
  cases n with
  | zero => rfl
  | pos p => exact bitsValue_encodePosNum p

theorem bitsValue_encodeNat (n : ℕ) : bitsValue (Computability.encodeNat n) = n := by
  unfold Computability.encodeNat
  rw [bitsValue_encodeNum, Num.to_of_nat]

def signedBitsValue (negative : Bool) (xs : List Bool) : ℤ :=
  if negative then Int.negSucc (bitsValue xs) else Int.ofNat (bitsValue xs)

def divideSignedBits (negative : Bool) (divisor xs : List Bool) : List Bool × List Bool :=
  let qr := divideBits divisor xs
  if negative then
    (qr.1, subtractBits (subtractBits divisor [true] false) qr.2 false)
  else qr

theorem divideSignedBits_correct (negative : Bool) (divisor xs : List Bool)
    (hd : 0 < bitsValue divisor) :
    signedBitsValue negative xs = (bitsValue divisor : ℤ) *
      signedBitsValue negative (divideSignedBits negative divisor xs).1 +
        (bitsValue (divideSignedBits negative divisor xs).2 : ℤ) ∧
    bitsValue (divideSignedBits negative divisor xs).2 < bitsValue divisor := by
  have hu := divideBits_correct divisor xs hd
  have hc : (bitsValue xs : ℤ) = (bitsValue divisor : ℤ) *
      (bitsValue (divideBits divisor xs).1 : ℤ) +
        (bitsValue (divideBits divisor xs).2 : ℤ) := by exact_mod_cast hu.1
  cases negative
  · simpa [divideSignedBits, signedBitsValue] using And.intro hc hu.2
  · have hp : bitsValue (subtractBits divisor [true] false) + 1 = bitsValue divisor := by
      have hh := subtractBits_correct divisor [true] false (by simp [bitsValue, digit]; omega)
      simpa [bitsValue, digit] using hh
    have hr : bitsValue (divideBits divisor xs).2 ≤ bitsValue (subtractBits divisor [true] false) := by
      omega
    have hs : bitsValue (subtractBits (subtractBits divisor [true] false)
        (divideBits divisor xs).2 false) + bitsValue (divideBits divisor xs).2 =
          bitsValue (subtractBits divisor [true] false) := by
      simpa only [digit_false, Nat.add_zero] using
        subtractBits_correct (subtractBits divisor [true] false) (divideBits divisor xs).2 false
          (by simpa only [digit_false, Nat.add_zero] using hr)
    have hsn : bitsValue (subtractBits (subtractBits divisor [true] false)
        (divideBits divisor xs).2 false) + bitsValue (divideBits divisor xs).2 + 1 =
          bitsValue divisor := by omega
    have hsi : (bitsValue (subtractBits (subtractBits divisor [true] false)
        (divideBits divisor xs).2 false) : ℤ) + (bitsValue (divideBits divisor xs).2 : ℤ) + 1 =
          (bitsValue divisor : ℤ) := by exact_mod_cast hsn
    have he : -((bitsValue xs : ℤ) + 1) = (bitsValue divisor : ℤ) *
        (-((bitsValue (divideBits divisor xs).1 : ℤ) + 1)) +
          (bitsValue (subtractBits (subtractBits divisor [true] false)
            (divideBits divisor xs).2 false) : ℤ) := by nlinarith
    have hl : bitsValue (subtractBits (subtractBits divisor [true] false)
        (divideBits divisor xs).2 false) < bitsValue divisor := by omega
    simpa [divideSignedBits, signedBitsValue, Int.negSucc_eq, Nat.cast_add] using And.intro he hl

theorem divideSignedBits_quotient (negative : Bool) (divisor xs : List Bool)
    (hd : 0 < bitsValue divisor) :
    signedBitsValue negative (divideSignedBits negative divisor xs).1 =
      signedBitsValue negative xs / (bitsValue divisor : ℤ) := by
  have h := divideSignedBits_correct negative divisor xs hd
  have hp : (0 : ℤ) < bitsValue divisor := by exact_mod_cast hd
  have hr : (bitsValue (divideSignedBits negative divisor xs).2 : ℤ) <
      (bitsValue divisor : ℤ) := by exact_mod_cast h.2
  have hz : (0 : ℤ) ≤ bitsValue (divideSignedBits negative divisor xs).2 := Nat.cast_nonneg _
  symm
  apply (Int.ediv_eq_iff_of_pos hp).mpr
  constructor <;> nlinarith [h.1]

def negativeOfInt : ℤ → Bool
  | .ofNat _ => false
  | .negSucc _ => true

end KS.W19

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_BinaryMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W29

def polynomialFuel (coefficient degree inputLength : Nat) : Nat :=
  coefficient * (inputLength + 1) ^ degree

end KS.W29

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_BinaryAdder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W01.BinaryAdder
open KS.W29
open KS.W19 (bitsValue digit)

def sumBit (a b c : Bool) : Bool := Bool.xor (Bool.xor a b) c

def carryBit (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

theorem fullAdder_identity (a b c : Bool) :
    digit (sumBit a b c) + 2 * digit (carryBit a b c) = digit a + digit b + digit c := by
  cases a <;> cases b <;> cases c <;> decide

def carryState (c : Bool) : Fin 2 := if c then 1 else 0

def addBits : Bool → List Bool → List Bool → List Bool
  | c, [], [] => if c then [true] else []
  | c, a :: xs, ys => sumBit a (ys.headD false) c ::
      addBits (carryBit a (ys.headD false) c) xs ys.tail
  | c, [], b :: ys => sumBit false b c :: addBits (carryBit false b c) [] ys
termination_by _ xs ys => xs.length + ys.length
decreasing_by
  all_goals simp_wf
  all_goals omega

theorem addBits_correct (c : Bool) (xs ys : List Bool) :
    bitsValue (addBits c xs ys) = bitsValue xs + bitsValue ys + digit c := by
  induction xs generalizing c ys with
  | nil =>
      induction ys generalizing c with
      | nil => cases c <;> simp [addBits, bitsValue, digit]
      | cons b ys ih =>
          rw [addBits]
          simp only [bitsValue]
          rw [ih]
          have h := fullAdder_identity false b c
          simp only [bitsValue, KS.W19.digit_false] at h ⊢
          omega
  | cons a xs ih =>
      cases ys with
      | nil =>
          rw [addBits]
          simp only [bitsValue, List.headD_nil, List.tail_nil]
          rw [ih]
          have h := fullAdder_identity a false c
          simp only [bitsValue, KS.W19.digit_false] at h ⊢
          omega
      | cons b ys =>
          rw [addBits]
          simp only [bitsValue, List.headD_cons, List.tail_cons]
          rw [ih]
          have h := fullAdder_identity a b c
          omega

theorem addBits_length_le (c : Bool) (xs ys : List Bool) :
    (addBits c xs ys).length ≤ max xs.length ys.length + 1 := by
  induction xs generalizing c ys with
  | nil =>
      induction ys generalizing c with
      | nil => cases c <;> simp [addBits]
      | cons b ys ih =>
          rw [addBits, List.length_cons]
          have h := ih (carryBit false b c)
          simp only [List.length_nil, List.length_cons, Nat.zero_max] at h ⊢
          omega
  | cons a xs ih =>
      cases ys with
      | nil =>
          rw [addBits, List.length_cons]
          have h := ih (carryBit a false c) []
          simp only [List.headD_nil, List.tail_nil, List.length_nil, List.length_cons,
            Nat.max_zero] at h ⊢
          omega
      | cons b ys =>
          rw [addBits, List.length_cons]
          have h := ih (carryBit a b c) ys
          simp only [List.headD_cons, List.tail_cons, List.length_cons] at h ⊢
          omega

end KS.W01.BinaryAdder

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_BinaryAdderCompose
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W01.BinaryAdder
open KS.W29
open KS.W19 (bitsValue digit)

theorem normalized_transition_bound (xs ys : List Bool) :
    (max xs.length ys.length + 1) + ((addBits false xs ys).length + 1) ≤
      2 * (xs.length + ys.length) + 3 := by
  have h := addBits_length_le false xs ys
  omega

end KS.W01.BinaryAdder

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_BinaryNormalize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19

def CanonicalBits : List Bool → Prop
  | [] => True
  | b :: bs => CanonicalBits bs ∧ (bs = [] → b = true)

def trimBits : List Bool → List Bool
  | [] => []
  | b :: bs =>
    let tail := trimBits bs
    if tail = [] ∧ b = false then [] else b :: tail

theorem trimBits_value (xs : List Bool) : bitsValue (trimBits xs) = bitsValue xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    by_cases h : trimBits bs = [] ∧ b = false
    · have hz : bitsValue bs = 0 := by simpa [h.1, bitsValue] using ih.symm
      simp [trimBits, h, bitsValue, hz]
    · simp [trimBits, h, bitsValue, ih]

theorem trimBits_length_le (xs : List Bool) : (trimBits xs).length ≤ xs.length := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    simp only [trimBits]
    split <;> simp_all

theorem trimBits_canonical (xs : List Bool) : CanonicalBits (trimBits xs) := by
  induction xs with
  | nil => trivial
  | cons b bs ih =>
    by_cases h : trimBits bs = [] ∧ b = false
    · simp [trimBits, h, CanonicalBits]
    · simp only [trimBits, h, ↓reduceIte, CanonicalBits]
      refine ⟨ih, ?_⟩
      intro ht
      cases b
      · exact (h ⟨ht, rfl⟩).elim
      · rfl

theorem canonicalBits_value_pos (xs : List Bool) (hc : CanonicalBits xs) (hn : xs ≠ []) :
    0 < bitsValue xs := by
  induction xs with
  | nil => exact (hn rfl).elim
  | cons b bs ih =>
    rcases hc with ⟨ht, hb⟩
    cases bs with
    | nil => simp [hb rfl, bitsValue]
    | cons c cs =>
      have h := ih ht (by simp)
      simp only [bitsValue] at h ⊢
      omega

theorem canonicalBits_injective {xs ys : List Bool}
    (hx : CanonicalBits xs) (hy : CanonicalBits ys)
    (hv : bitsValue xs = bitsValue ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    by_cases hy0 : ys = []
    · exact hy0.symm
    · have hpos := canonicalBits_value_pos ys hy hy0
      simp only [bitsValue] at hv
      omega
  | cons a as ih =>
    cases ys with
    | nil =>
      have hpos := canonicalBits_value_pos (a :: as) hx (by simp)
      simp only [bitsValue] at hv hpos
      omega
    | cons b bs =>
      have hab : a = b := by
        cases a <;> cases b <;> simp_all [bitsValue, digit] <;> omega
      have htail : bitsValue as = bitsValue bs := by
        simp only [bitsValue, hab] at hv
        omega
      have heq := ih hx.1 hy.1 htail
      rw [hab, heq]

theorem canonicalBits_encodePosNum (n : PosNum) : CanonicalBits (Computability.encodePosNum n) := by
  induction n <;>
    simp_all [Computability.encodePosNum, CanonicalBits, Computability.encodePosNum_nonempty]

theorem canonicalBits_encodeNum (n : Num) : CanonicalBits (Computability.encodeNum n) := by
  cases n with
  | zero => trivial
  | pos p => exact canonicalBits_encodePosNum p

theorem canonicalBits_encodeNat (n : ℕ) : CanonicalBits (Computability.encodeNat n) :=
  canonicalBits_encodeNum n

theorem trimBits_eq_encodeNat (xs : List Bool) :
    trimBits xs = Computability.encodeNat (bitsValue xs) := by
  apply canonicalBits_injective (trimBits_canonical xs) (canonicalBits_encodeNat _)
  rw [trimBits_value, bitsValue_encodeNat]

theorem bitsValue_lt_two_pow_length (xs : List Bool) : bitsValue xs < 2 ^ xs.length := by
  induction xs with
  | nil => decide
  | cons b bs ih =>
    have hb := digit_le_one b
    simp only [bitsValue, List.length_cons, pow_succ]
    omega

theorem trimBits_append_false (xs : List Bool) : trimBits (xs ++ [false]) = trimBits xs := by
  induction xs with
  | nil => simp [trimBits]
  | cons b bs ih => simp only [List.cons_append, trimBits, ih]

theorem trimBits_append_true (xs : List Bool) : trimBits (xs ++ [true]) = xs ++ [true] := by
  induction xs with
  | nil => simp [trimBits]
  | cons b bs ih => simp [trimBits, ih]

end KS.W19

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_BinaryGCD
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.BinaryGCD
open KS.W19

lemma remainder_value (ys xs : List Bool) (hy : 0 < bitsValue ys) :
    bitsValue (divideBits ys xs).2 = bitsValue xs % bitsValue ys := by
  obtain ⟨he, hr⟩ := divideBits_correct ys xs hy
  conv_rhs => rw [he]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hr]

lemma trim_eq_nil_iff (xs : List Bool) : trimBits xs = [] ↔ bitsValue xs = 0 := by
  constructor
  · intro h
    have hv := trimBits_value xs
    rw [h] at hv
    simpa [bitsValue] using hv.symm
  · intro h
    apply canonicalBits_injective (trimBits_canonical xs) (by simp [CanonicalBits])
    simpa [bitsValue, trimBits_value] using h

lemma remainder_below_half {b r K : ℕ} (hr : 0 < r) (hrb : r < b) (hb : b < 2 * K) :
    b % r < K := by
  by_cases hsmall : r ≤ K
  · exact lt_of_lt_of_le (Nat.mod_lt b hr) hsmall
  · rw [Nat.mod_eq_sub_mod (Nat.le_of_lt hrb), Nat.mod_eq_of_lt (by omega)]
    omega

def gcdRounds : ℕ → List Bool → List Bool → List Bool
  | 0, xs, _ys => trimBits xs
  | k + 1, xs, ys =>
      let v := trimBits ys
      if v = [] then trimBits xs else
      let r := trimBits (divideBits v xs).2
      if r = [] then v else
      let s := trimBits (divideBits r v).2
      gcdRounds k r s

lemma gcd_two_reductions (a b : ℕ) : Nat.gcd a b = Nat.gcd (a % b) (b % (a % b)) := by
  calc
    Nat.gcd a b = Nat.gcd (a % b) b := by rw [Nat.gcd_comm a b, Nat.gcd_rec b a]
    _ = Nat.gcd (a % b) (b % (a % b)) := by
      rw [Nat.gcd_rec (a % b) b, Nat.gcd_comm]

theorem gcdRounds_correct (k : ℕ) (xs ys : List Bool) (hy : bitsValue ys < 2 ^ k) :
    bitsValue (gcdRounds (k + 1) xs ys) = Nat.gcd (bitsValue xs) (bitsValue ys) := by
  induction k generalizing xs ys with
  | zero =>
      have hz : bitsValue ys = 0 := by simpa using hy
      simp [gcdRounds, (trim_eq_nil_iff ys).mpr hz, trimBits_value, hz]
  | succ k ih =>
      let v := trimBits ys
      have hv : bitsValue v = bitsValue ys := trimBits_value ys
      by_cases hz : v = []
      · have hy0 : bitsValue ys = 0 := (trim_eq_nil_iff ys).mp hz
        simp [gcdRounds, v, hz, trimBits_value, hy0]
      · have hp : 0 < bitsValue v := canonicalBits_value_pos v (trimBits_canonical ys) hz
        let r := trimBits (divideBits v xs).2
        have hr : bitsValue r = bitsValue xs % bitsValue ys := by
          dsimp only [r]
          rw [trimBits_value, remainder_value v xs hp, hv]
        have hrb : bitsValue r < bitsValue ys := by
          rw [hr]
          exact Nat.mod_lt _ (by omega)
        by_cases hrz : r = []
        · have hm : bitsValue xs % bitsValue ys = 0 := by simpa [hrz, bitsValue] using hr.symm
          have hg : Nat.gcd (bitsValue xs) (bitsValue ys) = bitsValue ys := by
            rw [Nat.gcd_comm, Nat.gcd_rec, hm, Nat.gcd_zero_left]
          simp [gcdRounds, v, hz, r, hrz, hv, hg]
        · have hrp : 0 < bitsValue r := canonicalBits_value_pos r (trimBits_canonical _) hrz
          let s := trimBits (divideBits r v).2
          have hs : bitsValue s = bitsValue ys % (bitsValue xs % bitsValue ys) := by
            dsimp only [s]
            rw [trimBits_value, remainder_value r v hrp, hv, hr]
          have hslt : bitsValue s < 2 ^ k := by
            dsimp only [s]
            rw [trimBits_value, remainder_value r v hrp, hv]
            exact remainder_below_half hrp hrb (by simpa [pow_succ, Nat.mul_comm] using hy)
          have hh := ih r s hslt
          rw [hr, hs] at hh
          rw [gcdRounds]
          change bitsValue (if v = [] then trimBits xs else
            if r = [] then v else gcdRounds (k + 1) r s) = _
          simp only [hz, hrz, ite_false, if_false]
          exact hh.trans (gcd_two_reductions _ _).symm

def gcdBits (xs ys : List Bool) : List Bool := gcdRounds (ys.length + 1) xs ys

theorem gcdBits_correct (xs ys : List Bool) :
    bitsValue (gcdBits xs ys) = Nat.gcd (bitsValue xs) (bitsValue ys) :=
  gcdRounds_correct ys.length xs ys (bitsValue_lt_two_pow_length ys)

theorem gcdRounds_canonical (fuel : ℕ) (xs ys : List Bool) :
    CanonicalBits (gcdRounds fuel xs ys) := by
  induction fuel generalizing xs ys with
  | zero => exact trimBits_canonical xs
  | succ fuel ih =>
      simp only [gcdRounds]
      split
      · exact trimBits_canonical xs
      · split
        · exact trimBits_canonical ys
        · exact ih _ _

theorem gcdBits_eq_encodeNat (xs ys : List Bool) :
    gcdBits xs ys = Computability.encodeNat (Nat.gcd (bitsValue xs) (bitsValue ys)) := by
  apply canonicalBits_injective (gcdRounds_canonical _ _ _) (canonicalBits_encodeNat _)
  simpa only [gcdBits, bitsValue_encodeNat] using gcdBits_correct xs ys

end KS.W30.BinaryGCD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_BinaryMultiply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W03.BinaryMultiply

open KS.W19
open KS.W01.BinaryAdder

def shift (xs : List Bool) : List Bool := false :: xs

@[simp] theorem shift_value (xs : List Bool) : bitsValue (shift xs) = 2 * bitsValue xs := by
  simp [shift, bitsValue, digit]

@[simp] theorem shift_length (xs : List Bool) : (shift xs).length = xs.length + 1 := rfl

def multiplyRaw : List Bool → List Bool → List Bool
  | [], _ys => []
  | b :: xs, ys =>
      addBits false (if b then ys else []) (shift (multiplyRaw xs ys))

theorem multiplyRaw_correct (xs ys : List Bool) :
    bitsValue (multiplyRaw xs ys) = bitsValue xs * bitsValue ys := by
  induction xs with
  | nil => simp [multiplyRaw, bitsValue]
  | cons b xs ih =>
    cases b <;> simp [multiplyRaw, addBits_correct, bitsValue, digit, ih] <;> ring

def multiply (xs ys : List Bool) : List Bool := trimBits (multiplyRaw xs ys)

end KS.W03.BinaryMultiply

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_BinaryRationalNormalize
attribute [-simp] _root_.OAI.KS.W03.BinaryMultiply.shift_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.BinaryRational
open KS.W19 KS.W30.BinaryGCD

lemma quotient_value (ys xs : List Bool) (hy : 0 < bitsValue ys) :
    bitsValue (divideBits ys xs).1 = bitsValue xs / bitsValue ys := by
  obtain ⟨he, hr⟩ := divideBits_correct ys xs hy
  symm
  apply Nat.div_eq_of_lt_le <;> nlinarith

def normalizeMagnitude (num den : List Bool) : List Bool × List Bool :=
  if trimBits den = [] then ([], [true]) else
  let g := gcdBits num den
  (trimBits (divideBits g num).1, trimBits (divideBits g den).1)

theorem normalizeMagnitude_correct (num den : List Bool) :
    let q := mkRat (bitsValue num : ℤ) (bitsValue den)
    normalizeMagnitude num den =
      (Computability.encodeNat q.num.natAbs, Computability.encodeNat q.den) := by
  by_cases hz : bitsValue den = 0
  · simp [normalizeMagnitude, (trim_eq_nil_iff den).mpr hz, hz, Computability.encodeNat,
      Computability.encodeNum, Computability.encodePosNum]
  · have hd : 0 < bitsValue den := Nat.pos_of_ne_zero hz
    have hg : 0 < bitsValue (gcdBits num den) := by
      rw [gcdBits_correct]
      exact Nat.gcd_pos_of_pos_right _ hd
    have hn : (mkRat (bitsValue num : ℤ) (bitsValue den)).num.natAbs =
        bitsValue num / Nat.gcd (bitsValue num) (bitsValue den) := by
      simp [Rat.num_mkRat, hz, ← Int.natCast_ediv, Nat.gcd_comm]
    have hd' : (mkRat (bitsValue num : ℤ) (bitsValue den)).den =
        bitsValue den / Nat.gcd (bitsValue num) (bitsValue den) := by
      simp [Rat.den_mkRat, hz, Nat.gcd_comm]
    have htrim : trimBits den ≠ [] := by simpa [trim_eq_nil_iff] using hz
    rw [normalizeMagnitude, ite_eq_right htrim]
    simp only [trimBits_eq_encodeNat, quotient_value _ _ hg, gcdBits_correct, hn, hd']

end KS.W30.BinaryRational

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_BinaryRationalCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.BinaryRational
open KS.W19 KS.W03.BinaryMultiply

structure RatBits where
  negative : Bool
  numerator : List Bool
  denominator : List Bool
  deriving DecidableEq

def RatBits.magnitude (x : RatBits) : ℚ :=
  (bitsValue x.numerator : ℚ) / (bitsValue x.denominator : ℚ)

def RatBits.value (x : RatBits) : ℚ := if x.negative then -x.magnitude else x.magnitude

def normalize (x : RatBits) : RatBits :=
  let p := normalizeMagnitude x.numerator x.denominator
  ⟨if p.1 = [] then false else x.negative, p.1, p.2⟩

lemma normalizeMagnitude_value (num den : List Bool) :
    (bitsValue (normalizeMagnitude num den).1 : ℚ) /
      (bitsValue (normalizeMagnitude num den).2 : ℚ) =
      (bitsValue num : ℚ) / (bitsValue den : ℚ) := by
  let q := mkRat (bitsValue num : ℤ) (bitsValue den)
  have hq : q = (bitsValue num : ℚ) / (bitsValue den : ℚ) := by
    dsimp only [q]
    rw [← Rat.divInt_ofNat, Rat.divInt_eq_div]
    simp
  have hpos : 0 ≤ q := by rw [hq]; exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hnum : (q.num.natAbs : ℚ) = (q.num : ℚ) := by
    have hi : (q.num.natAbs : ℤ) = q.num := by
      rw [Int.natCast_natAbs, abs_of_nonneg (Rat.num_nonneg.mpr hpos)]
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) hi
  rw [normalizeMagnitude_correct]
  simp only [bitsValue_encodeNat]
  change (q.num.natAbs : ℚ) / q.den = _
  rw [hnum, Rat.num_div_den, hq]

@[simp] theorem normalize_value (x : RatBits) : (normalize x).value = x.value := by
  have hu := normalizeMagnitude_value x.numerator x.denominator
  by_cases hz : (normalizeMagnitude x.numerator x.denominator).1 = []
  · have hx : x.magnitude = 0 := by
      unfold RatBits.magnitude
      rw [← hu, hz]
      simp [bitsValue]
    change (bitsValue x.numerator : ℚ) / (bitsValue x.denominator : ℚ) = 0 at hx
    simp [normalize, RatBits.value, RatBits.magnitude, hz, bitsValue, hx]
  · cases hx : x.negative
    · simpa [normalize, RatBits.value, RatBits.magnitude, hz, hx] using hu
    · simpa [normalize, RatBits.value, RatBits.magnitude, hz, hx] using congrArg Neg.neg hu

def encodeMagnitude (q : ℚ) : RatBits :=
  ⟨decide (q.num < 0), Computability.encodeNat q.num.natAbs,
    Computability.encodeNat q.den⟩

def inverseRat (x : RatBits) : RatBits :=
  normalize ⟨x.negative, x.denominator, x.numerator⟩

theorem inverseRat_value (x : RatBits) : (inverseRat x).value = x.value⁻¹ := by
  rw [inverseRat, normalize_value]
  cases hx : x.negative <;> simp [RatBits.value, RatBits.magnitude, hx, inv_div]

end KS.W30.BinaryRational

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_BinaryRationalAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.BinaryRational
open KS.W19 KS.W03.BinaryMultiply KS.W01.BinaryAdder

def signedValue (negative : Bool) (xs : List Bool) : ℤ :=
  if negative then -(bitsValue xs : ℤ) else (bitsValue xs : ℤ)

lemma value_eq_signed_div (x : RatBits) :
    x.value = (signedValue x.negative x.numerator : ℚ) / (bitsValue x.denominator : ℚ) := by
  cases hx : x.negative <;> simp [RatBits.value, RatBits.magnitude, signedValue, hx, neg_div]

end KS.W30.BinaryRational

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_BinaryRationalCanonical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.BinaryRational
open KS.W19

@[simp] theorem encodeMagnitude_value (q : ℚ) : (encodeMagnitude q).value = q := by
  have habs : (q.num.natAbs : ℚ) = |(q.num : ℚ)| := by
    simpa only [Int.cast_natCast, Int.cast_abs] using
      congrArg (fun z : ℤ => (z : ℚ)) (Int.natCast_natAbs q.num)
  by_cases hn : q.num < 0
  · have hn' : (q.num : ℚ) < 0 := by exact_mod_cast hn
    simp [encodeMagnitude, RatBits.value, RatBits.magnitude, bitsValue_encodeNat,
      hn, habs, abs_of_neg hn', neg_div, Rat.num_div_den]
  · have hn' : 0 ≤ (q.num : ℚ) := by exact_mod_cast (show 0 ≤ q.num by omega)
    simp [encodeMagnitude, RatBits.value, RatBits.magnitude, bitsValue_encodeNat,
      hn, habs, abs_of_nonneg hn', Rat.num_div_den]

theorem normalize_eq_encodeMagnitude (x : RatBits) :
    normalize x = encodeMagnitude x.value := by
  let q := mkRat (bitsValue x.numerator : ℤ) (bitsValue x.denominator)
  have hm : x.magnitude = q := by
    dsimp [RatBits.magnitude, q]
    rw [← Rat.divInt_ofNat, Rat.divInt_eq_div]
    simp
  have hq : 0 ≤ q.num := Rat.num_nonneg.mpr (by
    rw [← hm]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hc : normalizeMagnitude x.numerator x.denominator =
      (Computability.encodeNat q.num.natAbs, Computability.encodeNat q.den) :=
    normalizeMagnitude_correct _ _
  by_cases hz : q.num = 0
  · have hq0 : q = 0 := Rat.num_eq_zero.mp hz
    simp [normalize, hc, hq0, encodeMagnitude, RatBits.value, hm, Computability.encodeNat, Computability.encodeNum]
  · have hn : Computability.encodeNat q.num.natAbs ≠ [] := by
      intro he
      have hv := congrArg bitsValue he
      simp only [bitsValue_encodeNat, bitsValue] at hv
      exact hz (Int.natAbs_eq_zero.mp hv)
    have hp : 0 < q.num := by omega
    have hpq : 0 < q := Rat.num_pos.mp hp
    cases hx : x.negative <;>
      simp [normalize, hc, hn, encodeMagnitude, RatBits.value, hx, hm, hpq,
        show ¬q.num < 0 by omega]

@[simp] theorem inverseRat_canonical (q : ℚ) :
    inverseRat (encodeMagnitude q) = encodeMagnitude q⁻¹ := by
  rw [inverseRat, normalize_eq_encodeMagnitude]
  have hv := inverseRat_value (encodeMagnitude q)
  rw [encodeMagnitude_value, inverseRat, normalize_value] at hv
  rw [hv]

end KS.W30.BinaryRational

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_BinarySubtractor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.BinarySubtractor
open KS.W29
open KS.W19 (bitsValue digit differenceDigit nextBorrow subtractBits)

def borrowState (c : Bool) : Fin 2 := if c then 1 else 0

end KS.W19.BinarySubtractor

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_SubtractionBorrow
attribute [-simp] _root_.OAI.KS.W03.BinaryMultiply.shift_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19

def subtractionBorrow : List Bool → List Bool → Bool → Bool
  | [], [], c => c
  | [], b :: bs, c => subtractionBorrow [] bs (nextBorrow false b c)
  | a :: as, [], c => subtractionBorrow as [] (nextBorrow a false c)
  | a :: as, b :: bs, c => subtractionBorrow as bs (nextBorrow a b c)
termination_by xs ys _ => xs.length + ys.length
decreasing_by all_goals simp_wf <;> omega

theorem borrow_column_lift (a b c : Bool) (x y r carry p : Nat)
    (hr : x + carry * p = y + digit (nextBorrow a b c) + r) :
    digit a + 2 * x + carry * (p * 2) =
      digit b + 2 * y + digit c + (digit (differenceDigit a b c) + 2 * r) := by
  have hc := subtraction_column a b c
  nlinarith

theorem subtractionBorrow_identity (xs ys : List Bool) (c : Bool) :
    bitsValue xs + digit (subtractionBorrow xs ys c) * 2 ^ max xs.length ys.length =
      bitsValue ys + digit c + bitsValue (subtractBits xs ys c) := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => simp [subtractionBorrow, subtractBits, bitsValue]
    | cons b bs ih =>
      have ht := ih (nextBorrow false b c)
      have hh := borrow_column_lift false b c 0 (bitsValue bs)
        (bitsValue (subtractBits [] bs (nextBorrow false b c)))
        (digit (subtractionBorrow [] bs (nextBorrow false b c))) (2 ^ bs.length)
        (by simpa only [bitsValue, List.length_nil, Nat.zero_max, Nat.zero_add] using ht)
      simpa [subtractionBorrow, subtractBits, bitsValue, digit_false, pow_succ] using hh
  | cons a as ih =>
    cases ys with
    | nil =>
      have ht := ih [] (nextBorrow a false c)
      have hh := borrow_column_lift a false c (bitsValue as) 0
        (bitsValue (subtractBits as [] (nextBorrow a false c)))
        (digit (subtractionBorrow as [] (nextBorrow a false c))) (2 ^ as.length)
        (by simpa only [bitsValue, List.length_nil, Nat.max_zero, Nat.zero_add] using ht)
      simpa [subtractionBorrow, subtractBits, bitsValue, digit_false, pow_succ] using hh
    | cons b bs =>
      have ht := ih bs (nextBorrow a b c)
      have hh := borrow_column_lift a b c (bitsValue as) (bitsValue bs)
        (bitsValue (subtractBits as bs (nextBorrow a b c)))
        (digit (subtractionBorrow as bs (nextBorrow a b c))) (2 ^ max as.length bs.length) ht
      have hm : max (a :: as).length (b :: bs).length = max as.length bs.length + 1 := by
        simp only [List.length_cons]
        omega
      simpa only [subtractionBorrow, subtractBits, bitsValue, hm, pow_succ] using hh

theorem subtractionBorrow_true_iff (xs ys : List Bool) (c : Bool) :
    subtractionBorrow xs ys c = true ↔ bitsValue xs < bitsValue ys + digit c := by
  have hid := subtractionBorrow_identity xs ys c
  have hr := bitsValue_lt_two_pow_length (subtractBits xs ys c)
  rw [subtractBits_length] at hr
  cases hb : subtractionBorrow xs ys c <;> simp [hb, digit] at hid ⊢ <;> omega

end KS.W19

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_BorrowSubtractor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.BorrowSubtractor
open KS.W29
open KS.W19 (bitsValue digit differenceDigit nextBorrow subtractBits)

def borrowState (c : Bool) : Fin 2 := if c then 1 else 0

end KS.W19.BorrowSubtractor

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_LittleEndianCompare
attribute [-simp] _root_.OAI.KS.W03.BinaryMultiply.shift_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W28.LittleEndianCompare
open KS.W29
open KS.W19 (bitsValue compareBits compareDigit OrderingCorrect)

def encode : Ordering → Fin 3
  | .eq => 0
  | .lt => 1
  | .gt => 2

def decode (s : Fin 3) : Ordering :=
  if s = 0 then .eq else if s = 1 then .lt else .gt

@[simp] theorem decode_encode (o : Ordering) : decode (encode o) = o := by
  cases o <;> rfl

def merge (old high : Ordering) : Ordering :=
  match high with
  | .eq => old
  | o => o

def update (o : Ordering) (a b : Bool) : Ordering := merge o (compareDigit a b)
def result (o : Ordering) : Bool := match o with | .gt => false | _ => true

def scan (o : Ordering) : List Bool → List Bool → Ordering
  | [], [] => o
  | [], b :: ys => scan (update o false b) [] ys
  | a :: xs, [] => scan (update o a false) xs []
  | a :: xs, b :: ys => scan (update o a b) xs ys
termination_by xs ys => xs.length + ys.length
decreasing_by all_goals simp_wf <;> omega

theorem scan_eq (o : Ordering) (xs ys : List Bool) :
    scan o xs ys = merge o (compareBits xs ys) := by
  induction xs generalizing o ys with
  | nil =>
      induction ys generalizing o with
      | nil => simp [scan, compareBits, merge]
      | cons b ys ih =>
          rw [scan, ih]
          cases h : compareBits [] ys <;> cases o <;> cases b <;>
            simp [compareBits, h, update, merge, compareDigit]
  | cons a xs ih =>
      cases ys with
      | nil =>
          rw [scan, ih]
          cases h : compareBits xs [] <;> cases o <;> cases a <;>
            simp [compareBits, h, update, merge, compareDigit]
      | cons b ys =>
          rw [scan, ih]
          cases h : compareBits xs ys <;> cases o <;> cases a <;> cases b <;>
            simp [compareBits, h, update, merge, compareDigit]

theorem result_correct (xs ys : List Bool) :
    result (scan .eq xs ys) = decide (bitsValue xs ≤ bitsValue ys) := by
  rw [scan_eq]
  have hc := KS.W19.compareBits_correct xs ys
  cases h : compareBits xs ys with
  | lt =>
      simp only [h, OrderingCorrect] at hc
      simp [merge, result, Nat.le_of_lt hc]
  | eq =>
      simp only [h, OrderingCorrect] at hc
      simp [merge, result, hc]
  | gt =>
      simp only [h, OrderingCorrect] at hc
      simp [merge, result, Nat.not_le_of_lt hc]

end KS.W28.LittleEndianCompare

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedCompare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W28.FixedCompare

def after {k : ℕ} (ports : Fin 3 ↪ Fin k) (registerMap : Fin k → List Bool)
    (b : Bool) : Fin k → List Bool := fun j =>
  if j = ports 0 then [] else if j = ports 1 then []
  else if j = ports 2 then b :: registerMap j else registerMap j

@[simp] theorem after_left {k : ℕ} (ports : Fin 3 ↪ Fin k)
    (registerMap : Fin k → List Bool) (b : Bool) : after ports registerMap b (ports 0) = [] := by
  simp [after]

@[simp] theorem after_right {k : ℕ} (ports : Fin 3 ↪ Fin k)
    (registerMap : Fin k → List Bool) (b : Bool) : after ports registerMap b (ports 1) = [] := by
  simp [after, ports.injective.eq_iff]

end KS.W28.FixedCompare

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_MagnitudeProgram
attribute [-simp] _root_.OAI.KS.W03.BinaryMultiply.shift_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W01.MagnitudeProgram
open KS.W29
open KS.W01.BinaryAdder

def result (carry : Bool) (xs : List Bool) : List Bool := addBits carry [] xs

def ticks (carry : Bool) (xs : List Bool) : ℕ := xs.length + 1 + ((result carry xs).length + 1)

theorem result_value (carry : Bool) (xs : List Bool) :
    KS.W19.bitsValue (result carry xs) = KS.W19.bitsValue xs + KS.W19.digit carry := by
  simpa [result, KS.W19.bitsValue] using addBits_correct carry [] xs

theorem ticks_le (carry : Bool) (xs : List Bool) : ticks carry xs ≤ 2 * xs.length + 3 := by
  have h := addBits_length_le carry [] xs
  simp only [List.length_nil, Nat.zero_max] at h
  unfold ticks result
  omega

end KS.W01.MagnitudeProgram

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalCompareBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W06.RationalCompare

def signedCrossLE (negativeLeft negativeRight : Bool) (left right : ℕ) : Bool :=
  if negativeLeft then
    if negativeRight then decide (right ≤ left) else true
  else if negativeRight then false else decide (left ≤ right)

def swapFirstTwo : Fin 3 ↪ Fin 3 := ⟨![1,0,2], by decide⟩

end KS.W06.RationalCompare

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_BinaryAccumulator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W03.BinaryAccumulator

open KS.W19 KS.W01.BinaryAdder KS.W03.BinaryMultiply

def nextAccumulator (b : Bool) (operand acc : List Bool) : List Bool :=
  if b then addBits false acc operand else acc

def loop : List Bool → List Bool → List Bool → List Bool
  | [], _operand, acc => acc
  | b :: xs, operand, acc => loop xs (shift operand) (nextAccumulator b operand acc)

theorem loop_value (xs operand acc : List Bool) :
    bitsValue (loop xs operand acc) = bitsValue acc + bitsValue xs * bitsValue operand := by
  induction xs generalizing operand acc with
  | nil => simp [loop, bitsValue]
  | cons b xs ih =>
    rw [loop, ih]
    cases b <;> simp [nextAccumulator, addBits_correct, bitsValue, digit] <;> ring

def width (operand acc : List Bool) : ℕ := max operand.length acc.length

theorem next_width_le (b : Bool) (operand acc : List Bool) :
    width (shift operand) (nextAccumulator b operand acc) ≤ width operand acc + 1 := by
  have ha := addBits_length_le false acc operand
  cases b <;> simp [width, shift_length, nextAccumulator] <;> omega

theorem loop_length_le (xs operand acc : List Bool) :
    (loop xs operand acc).length ≤ width operand acc + xs.length := by
  induction xs generalizing operand acc with
  | nil => simp [loop, width]
  | cons b xs ih =>
    have hn := next_width_le b operand acc
    have hh := ih (shift operand) (nextAccumulator b operand acc)
    rw [loop]
    simp only [List.length_cons]
    omega

def bodyTicks (operand acc : List Bool) : ℕ :=
  (2 * operand.length + 2) + (max acc.length operand.length + 1) +
    ((addBits false acc operand).length + 1) + 1

theorem bodyTicks_le (operand acc : List Bool) :
    bodyTicks operand acc ≤ 4 * width operand acc + 6 := by
  have h := addBits_length_le false acc operand
  unfold bodyTicks width
  omega

def roundTicks (b : Bool) (operand acc : List Bool) : ℕ :=
  if b then bodyTicks operand acc else 0

theorem roundTicks_le (b : Bool) (operand acc : List Bool) :
    roundTicks b operand acc ≤ 4 * width operand acc + 6 := by
  cases b
  · simp [roundTicks]
  · exact bodyTicks_le operand acc

def loopTicks : List Bool → List Bool → List Bool → ℕ
  | [], _operand, _acc => 1
  | b :: xs, operand, acc =>
      1 + roundTicks b operand acc + loopTicks xs (shift operand) (nextAccumulator b operand acc)

theorem loopTicks_le (xs operand acc : List Bool) :
    loopTicks xs operand acc ≤
      8 * (xs.length + 1) * (width operand acc + xs.length + 1) := by
  induction xs generalizing operand acc with
  | nil => simp [loopTicks]; omega
  | cons b xs ih =>
    have hn := next_width_le b operand acc
    have hr := roundTicks_le b operand acc
    have ht := ih (shift operand) (nextAccumulator b operand acc)
    have ht' : loopTicks xs (shift operand) (nextAccumulator b operand acc) ≤
        8 * (xs.length + 1) * (width operand acc + xs.length + 2) := by
      apply ht.trans
      apply Nat.mul_le_mul_left
      omega
    rw [loopTicks]
    simp only [List.length_cons]
    nlinarith

theorem loop_zero_correct (xs operand : List Bool) :
    bitsValue (loop xs operand []) = bitsValue xs * bitsValue operand := by
  simpa [bitsValue] using loop_value xs operand []

theorem loop_zero_length_le (xs operand : List Bool) :
    (loop xs operand []).length ≤ xs.length + operand.length := by
  simpa [width, Nat.add_comm] using loop_length_le xs operand []

theorem loop_zero_ticks_le (xs operand : List Bool) :
    loopTicks xs operand [] ≤ 8 * (xs.length + operand.length + 1) ^ 2 := by
  have h := loopTicks_le xs operand []
  simp only [width, List.length_nil, Nat.max_zero] at h
  have hn : xs.length + 1 ≤ xs.length + operand.length + 1 := by omega
  calc
    _ ≤ 8 * (xs.length + 1) * (operand.length + xs.length + 1) := h
    _ ≤ 8 * (xs.length + operand.length + 1) * (xs.length + operand.length + 1) := by
      rw [Nat.add_comm operand.length xs.length]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 8 hn)
    _ = _ := by ring

end KS.W03.BinaryAccumulator

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_MultiplicationBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W03.MultiplicationBody

open KS.W03.BinaryAccumulator KS.W03.BinaryMultiply

def registers (input xs operand acc copy scratch reverse : List Bool) : Fin 7 → List Bool :=
  ![input, xs, operand, acc, copy, scratch, reverse]

def copyPorts : Fin 3 ↪ Fin 7 := ⟨![2, 4, 5], by decide⟩
def addPorts : Fin 3 ↪ Fin 7 := ⟨![3, 4, 6], by decide⟩
def reversePorts : Fin 3 ↪ Fin 7 := ⟨![0, 3, 6], by decide⟩

end KS.W03.MultiplicationBody

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_MultiplicationLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W03.MultiplicationLoop

open KS.W03.MultiplicationBody KS.W03.BinaryAccumulator KS.W03.BinaryMultiply

def advance : List Bool → List Bool → List Bool
  | [], operand => operand
  | _ :: xs, operand => advance xs (shift operand)

theorem advance_length (xs operand : List Bool) :
    (advance xs operand).length = xs.length + operand.length := by
  induction xs generalizing operand with
  | nil => simp [advance]
  | cons b xs ih => simp [advance, ih, Nat.add_comm, Nat.add_left_comm]

end KS.W03.MultiplicationLoop

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalComparePrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W06.RationalCompare

def replace3 {k : ℕ} (ports : Fin 3 ↪ Fin k) (before : Fin k → List Bool)
    (a b c : List Bool) : Fin k → List Bool := fun j =>
  if j = ports 0 then a else if j = ports 1 then b else if j = ports 2 then c else before j

def signAfter {k : ℕ} (source target : Fin k) (before : Fin k → List Bool)
    (sign : Bool) (tail : List Bool) : Fin k → List Bool := fun j =>
  if j = source then tail else if j = target then sign :: before j else before j

def productTicks (xs ys : List Bool) : ℕ :=
  KS.W03.BinaryAccumulator.loopTicks xs ys [] +
    (2 * (KS.W03.BinaryAccumulator.loop xs ys []).length + 2)

theorem productTicks_le (xs ys : List Bool) :
    productTicks xs ys ≤ 16 * (xs.length + ys.length + 2) ^ 2 := by
  have ht := KS.W03.BinaryAccumulator.loop_zero_ticks_le xs ys
  have hl := KS.W03.BinaryAccumulator.loop_zero_length_le xs ys
  unfold productTicks
  nlinarith [Nat.zero_le ((xs.length + ys.length) * (xs.length + ys.length))]

end KS.W06.RationalCompare

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalCompareParser
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W06.RationalCompare

def fields (input sa na da sb nb db : List Bool) : Fin 13 → List Bool :=
  ![input,sa,na,da,sb,nb,db,[],[],[],[],[],[]]

def leftNumeratorPorts : Fin 3 ↪ Fin 13 := ⟨![0,2,12], by decide⟩
def leftDenominatorPorts : Fin 3 ↪ Fin 13 := ⟨![0,3,12], by decide⟩
def rightNumeratorPorts : Fin 3 ↪ Fin 13 := ⟨![0,5,12], by decide⟩
def rightDenominatorPorts : Fin 3 ↪ Fin 13 := ⟨![0,6,12], by decide⟩

def parseTicks (na da nb db : List Bool) : ℕ :=
  3 * (na.length + da.length + nb.length + db.length) + 10

def negativeBit (z : ℤ) : Bool := decide (z < 0)

end KS.W06.RationalCompare

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalCompareProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W06.RationalCompare

def leftMagnitudePorts : Fin 3 ↪ Fin 13 := ⟨![10,2,11], by decide⟩
def rightMagnitudePorts : Fin 3 ↪ Fin 13 := ⟨![10,5,11], by decide⟩
def leftProductPorts : Fin 7 ↪ Fin 13 := ⟨![9,2,6,7,10,11,12], by decide⟩
def rightProductPorts : Fin 7 ↪ Fin 13 := ⟨![9,5,3,8,10,11,12], by decide⟩
def resultPorts : Fin 3 ↪ Fin 13 := ⟨![7,8,9], by decide⟩

def workFields (sa na da sb nb db left right : List Bool) : Fin 13 → List Bool :=
  ![[],sa,na,da,sb,nb,db,left,right,[],[],[],[]]

def magnitude (s : Bool) (xs : List Bool) : List Bool := KS.W01.MagnitudeProgram.result s xs
def product (xs ys : List Bool) : List Bool :=
  Computability.encodeNat (KS.W19.bitsValue xs * KS.W19.bitsValue ys)

def productsAfter (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) : Fin 13 → List Bool :=
  workFields [sa] [] (KS.W03.MultiplicationLoop.advance nb da) [sb] []
    (KS.W03.MultiplicationLoop.advance na db) (product na db) (product nb da)

def totalTicks (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) : ℕ :=
  let a := magnitude sa na
  let b := magnitude sb nb
  ((parseTicks na da nb db + (2 * na.length + 4) + (2 * nb.length + 4)) +
    (productTicks a db + productTicks b da)) +
    ((product a db).length + (product b da).length + 2)

end KS.W06.RationalCompare

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalCompareCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W06.RationalCompare
open KS.W01

def signedFraction (negative : Bool) (num den : ℕ) : ℚ :=
  (if negative then -(num : ℚ) else num) / den

theorem fraction_le_iff (a b d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    (a : ℚ) / d ≤ (b : ℚ) / e ↔ a * e ≤ b * d := by
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  have he' : (0 : ℚ) < e := by exact_mod_cast he
  rw [div_le_div_iff₀ hd' he']
  norm_cast

theorem signedCrossLE_correct (sa sb : Bool) (a b d e : ℕ)
    (ha : sa = true → 0 < a) (hb : sb = true → 0 < b)
    (hd : 0 < d) (he : 0 < e) :
    signedCrossLE sa sb (a * e) (b * d) =
      decide (signedFraction sa a d ≤ signedFraction sb b e) := by
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  have he' : (0 : ℚ) < e := by exact_mod_cast he
  have ha0 : (0 : ℚ) ≤ (a : ℚ) / d := div_nonneg (Nat.cast_nonneg _) hd'.le
  have hb0 : (0 : ℚ) ≤ (b : ℚ) / e := div_nonneg (Nat.cast_nonneg _) he'.le
  cases sa <;> cases sb
  · simp [signedCrossLE, signedFraction, fraction_le_iff a b d e hd he]
  · have hbpos : (0 : ℚ) < (b : ℚ) / e := div_pos (by exact_mod_cast hb rfl) he'
    have hnot : ¬ (a : ℚ) / d ≤ -((b : ℚ) / e) := by linarith
    simp [signedCrossLE, signedFraction, neg_div, hnot]
  · have hyes : -((a : ℚ) / d) ≤ (b : ℚ) / e := by linarith
    simp [signedCrossLE, signedFraction, neg_div, hyes]
  · simp [signedCrossLE, signedFraction, neg_div, neg_le_neg_iff,
      fraction_le_iff b a e d he hd]

theorem negativeBit_pos (z : ℤ) (h : negativeBit z = true) : 0 < z.natAbs := by
  cases z <;> simp_all [negativeBit]
  omega

theorem signedFraction_num_den (q : ℚ) :
    signedFraction (negativeBit q.num) q.num.natAbs q.den = q := by
  have hn : (if negativeBit q.num then -(q.num.natAbs : ℚ) else (q.num.natAbs : ℚ)) =
      (q.num : ℚ) := by
    cases q.num <;> simp [negativeBit, Int.cast_negSucc]
  unfold signedFraction
  rw [hn]
  exact q.num_div_den

theorem magnitude_length_le (s : Bool) (xs : List Bool) :
    (magnitude s xs).length ≤ xs.length + 1 := by
  simpa [magnitude, KS.W01.MagnitudeProgram.result] using
    KS.W01.BinaryAdder.addBits_length_le s [] xs

end KS.W06.RationalCompare

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_CleanRationalCompare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W04.CleanRationalCompare

variable {k : Nat}

def clearState (port : Fin k) (before : Fin k → List Bool) : Fin k → List Bool :=
  fun j => if j = port then [] else before j

def clearListState : List (Fin k) → (Fin k → List Bool) → (Fin k → List Bool)
  | [], before => before
  | port :: ports, before => clearListState ports (clearState port before)

def clearListTicks : List (Fin k) → (Fin k → List Bool) → Nat
  | [], _ => 1
  | port :: ports, before => (before port).length + 1 + clearListTicks ports (clearState port before)

theorem clearListState_apply (ports : List (Fin k)) (before : Fin k → List Bool) (j : Fin k) :
    clearListState ports before j = if j ∈ ports then [] else before j := by
  induction ports generalizing before with
  | nil => simp [clearListState]
  | cons p ps ih =>
      simp only [clearListState, ih, List.mem_cons]
      by_cases hj : j ∈ ps <;> by_cases hp : j = p <;> simp [clearState, hj, hp]

theorem clearListTicks_le (ports : List (Fin k)) (before : Fin k → List Bool)
    (bound : Nat) (hbound : ∀ j, (before j).length ≤ bound) :
    clearListTicks ports before ≤ ports.length * (bound + 1) + 1 := by
  induction ports generalizing before with
  | nil => simp [clearListTicks]
  | cons p ps ih =>
      have hm : ∀ j, (clearState p before j).length ≤ bound := by
        intro j
        by_cases hj : j = p <;> simp [clearState, hj, hbound j]
      have h := ih (clearState p before) hm
      have hp := hbound p
      simp only [clearListTicks, List.length_cons]
      nlinarith

def scratchPorts : List (Fin 13) := [0,1,2,3,4,5,6,7,8,10,11,12]

def flagState (flag : Bool) : Fin 13 → List Bool := fun j => if j = 9 then [flag] else []

end KS.W04.CleanRationalCompare

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_UnsignedPairSerializer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.UnsignedPairSerializer
open KS.W28

def registers {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (xs ys zs : List Bool) : Fin k → List Bool := fun j =>
  if j = ports 0 then xs else if j = ports 1 then ys else if j = ports 2 then zs else spare j

end KS.W19.UnsignedPairSerializer

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalAddPrimitives
attribute [-simp] _root_.OAI.KS.W03.BinaryMultiply.shift_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W13.RationalAdd

open KS.W19
open KS.W19.UnsignedPairSerializer (registers )

def addResult (xs ys : List Bool) : List Bool :=
  Computability.encodeNat (bitsValue xs + bitsValue ys)

def canonicalAddTicks (xs ys : List Bool) : ℕ :=
  (max xs.length ys.length + 1) + ((KS.W01.BinaryAdder.addBits false xs ys).length + 1)

theorem canonicalAddTicks_le (xs ys : List Bool) :
    canonicalAddTicks xs ys ≤ 2 * (xs.length + ys.length) + 3 := by
  have h := KS.W01.BinaryAdder.addBits_length_le false xs ys
  unfold canonicalAddTicks
  omega

theorem addResult_length_le (xs ys : List Bool) :
    (addResult xs ys).length ≤ max xs.length ys.length + 1 := by
  have hv : bitsValue (KS.W01.BinaryAdder.addBits false xs ys) = bitsValue xs + bitsValue ys := by
    simpa using KS.W01.BinaryAdder.addBits_correct false xs ys
  have ht := trimBits_length_le (KS.W01.BinaryAdder.addBits false xs ys)
  rw [trimBits_eq_encodeNat, hv] at ht
  exact ht.trans (KS.W01.BinaryAdder.addBits_length_le false xs ys)

theorem addResult_canonical (xs ys : List Bool) : CanonicalBits (addResult xs ys) :=
  canonicalBits_encodeNat _

end KS.W13.RationalAdd

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalAddModel
attribute [-simp] _root_.OAI.KS.W30.BinaryRational.encodeMagnitude_value _root_.OAI.KS.W30.BinaryRational.inverseRat_canonical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W13.RationalAdd

open KS.W19 KS.W30.BinaryRational

def signedNumerator (sa : Bool) (xs : List Bool) (sb : Bool) (ys : List Bool) : Bool × List Bool :=
  if sa = sb then (sa, addResult xs ys)
  else if bitsValue xs ≤ bitsValue ys then
    (sb, Computability.encodeNat (bitsValue ys - bitsValue xs))
  else (sa, Computability.encodeNat (bitsValue xs - bitsValue ys))

theorem signedNumerator_value (sa : Bool) (xs : List Bool) (sb : Bool) (ys : List Bool) :
    signedValue (signedNumerator sa xs sb ys).1 (signedNumerator sa xs sb ys).2 =
      signedValue sa xs + signedValue sb ys := by
  by_cases h : bitsValue xs ≤ bitsValue ys
  · cases sa <;> cases sb <;>
      simp [signedNumerator, signedValue, addResult, h, bitsValue_encodeNat] <;> omega
  · cases sa <;> cases sb <;>
      simp [signedNumerator, signedValue, addResult, h, bitsValue_encodeNat] <;> omega

theorem subtractResult_length_le (xs ys : List Bool) (hsub : bitsValue ys ≤ bitsValue xs) :
    (Computability.encodeNat (bitsValue xs - bitsValue ys)).length ≤ max xs.length ys.length := by
  have hv := subtractBits_correct xs ys false (by simpa only [digit_false, Nat.add_zero] using hsub)
  have he : bitsValue (subtractBits xs ys false) = bitsValue xs - bitsValue ys := by
    simp only [digit_false, Nat.add_zero] at hv
    omega
  have h := trimBits_length_le (subtractBits xs ys false)
  rw [trimBits_eq_encodeNat, he, subtractBits_length] at h
  exact h

theorem signedNumerator_length_le (sa : Bool) (xs : List Bool) (sb : Bool) (ys : List Bool) :
    (signedNumerator sa xs sb ys).2.length ≤ max xs.length ys.length + 1 := by
  unfold signedNumerator
  split
  · exact addResult_length_le xs ys
  · split
    · dsimp only [Prod.snd]
      have h := subtractResult_length_le ys xs (by assumption)
      simp only [max_comm] at h
      omega
    · dsimp only [Prod.snd]
      have h := subtractResult_length_le xs ys (by omega)
      omega

theorem signedNumerator_canonical (sa : Bool) (xs : List Bool) (sb : Bool) (ys : List Bool) :
    CanonicalBits (signedNumerator sa xs sb ys).2 := by
  unfold signedNumerator
  split
  · exact addResult_canonical xs ys
  · split <;> exact canonicalBits_encodeNat _

def rawSum (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) : RatBits :=
  let p := signedNumerator sa (KS.W06.RationalCompare.product na db)
    sb (KS.W06.RationalCompare.product nb da)
  ⟨p.1, p.2, KS.W06.RationalCompare.product da db⟩

theorem rawSum_value (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool)
    (hd : bitsValue da ≠ 0) (he : bitsValue db ≠ 0) :
    (rawSum sa na da sb nb db).value =
      (RatBits.mk sa na da).value + (RatBits.mk sb nb db).value := by
  rw [value_eq_signed_div]
  simp only [rawSum, signedNumerator_value, KS.W06.RationalCompare.product, bitsValue_encodeNat]
  have hs (s : Bool) (xs ys : List Bool) :
      signedValue s (Computability.encodeNat (bitsValue xs * bitsValue ys)) =
        signedValue s xs * (bitsValue ys : ℤ) := by
    cases s <;> simp [signedValue, bitsValue_encodeNat, Nat.cast_mul, neg_mul]
  simp only [hs, Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  rw [value_eq_signed_div, value_eq_signed_div]
  simpa only [mul_comm] using
    (div_add_div (signedValue sa na : ℚ) (signedValue sb nb : ℚ)
      (Nat.cast_ne_zero.mpr hd) (Nat.cast_ne_zero.mpr he)).symm

end KS.W13.RationalAdd

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_DivisionMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.DivisionMachine

def trialPorts : Fin 3 ↪ Fin 10 := ⟨![4,6,9], by decide⟩
def divisorPorts : Fin 3 ↪ Fin 10 := ⟨![2,7,9], by decide⟩
def subtractPorts : Fin 3 ↪ Fin 10 := ⟨![6,7,8], by decide⟩
def trimPorts : Fin 3 ↪ Fin 10 := ⟨![0,4,8], by decide⟩

def «stacks» (d pending q r a b c scratch : List Bool) : Fin 10 → List Bool :=
  ![[],[],d,pending,r,q,a,b,c,scratch]

end KS.W19.DivisionMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_GCDMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.GCDMachine
open KS.W19

def remainderPorts : Fin 3 ↪ Fin 10 := ⟨![0,2,8], by decide⟩

def state (a b : List Bool) : Fin 10 → List Bool :=
  DivisionMachine.«stacks» b a.reverse [] [] [] [] [] []

end KS.W30.GCDMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalMagnitudeMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.RationalMagnitudeMachine
open KS.W19

def corePorts : Fin 10 ↪ Fin 13 :=
  ⟨fun i => ⟨i.val, by omega⟩, by intro i j h; exact Fin.ext (congrArg (fun x : Fin 13 => x.val) h)⟩
def numeratorCopyPorts : Fin 3 ↪ Fin 13 := ⟨![10,1,9], by decide⟩
def denominatorCopyPorts : Fin 3 ↪ Fin 13 := ⟨![11,2,9], by decide⟩
def numeratorTrimPorts : Fin 3 ↪ Fin 13 := ⟨![0,10,8], by decide⟩
def denominatorTrimPorts : Fin 3 ↪ Fin 13 := ⟨![0,11,8], by decide⟩

def «stacks» (work : Fin 10 → List Bool) (num den : List Bool) (negative : Bool) :
    Fin 13 → List Bool :=
  ![work 0,work 1,work 2,work 3,work 4,work 5,work 6,work 7,work 8,work 9,num,den,[negative]]
def state (num den : List Bool) (negative : Bool) : Fin 13 → List Bool :=
  «stacks» (fun _ => []) num den negative

end KS.W30.RationalMagnitudeMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalMultiplyProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W15.RationalMultiply
open KS.W06.RationalCompare (workFields product productTicks )

def numeratorPorts : Fin 7 ↪ Fin 13 := ⟨![9,2,5,7,10,11,12], by decide⟩
def denominatorPorts : Fin 7 ↪ Fin 13 := ⟨![9,3,6,8,10,11,12], by decide⟩

def productsAfter (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    Fin 13 → List Bool :=
  ![[],[sa],[],[],[sb],KS.W03.MultiplicationLoop.advance na nb,
    KS.W03.MultiplicationLoop.advance da db,product na nb,product da db,[],[],[],[]]

def xorAfter (before : Fin 13 → List Bool) (sa sb : Bool) : Fin 13 → List Bool :=
  fun j => if j = 1 ∨ j = 4 then [] else if j = 12 then [sa ^^ sb] else before j

def cleanupTicks (na da nb db : List Bool) : Nat :=
  (KS.W03.MultiplicationLoop.advance na nb).length +
    (KS.W03.MultiplicationLoop.advance da db).length +
    2 * (product na nb).length + 2 * (product da db).length + 7

end KS.W15.RationalMultiply

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalAddProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W13.RationalAdd

open KS.W06.RationalCompare (product productTicks)

def corePorts : Fin 13 ↪ Fin 16 :=
  ⟨fun i => ⟨i.val, by omega⟩, by intro i j h; exact Fin.ext (congrArg (fun k : Fin 16 => k.val) h)⟩

def extend (s : Fin 13 → List Bool) (a b c : List Bool) : Fin 16 → List Bool := fun j =>
  if h : j.val < 13 then s ⟨j.val, h⟩ else if j = 13 then a else if j = 14 then b else c

@[simp] theorem extend_core (s : Fin 13 → List Bool) (a b c : List Bool) (i : Fin 13) :
    extend s a b c (corePorts i) = s i := by
  change dite (i.val < 13) (fun h => s ⟨i.val,h⟩) _ = s i
  exact dite_eq_left i.isLt

@[simp] theorem extend_13 (s : Fin 13 → List Bool) (a b c : List Bool) : extend s a b c 13 = a := rfl
@[simp] theorem extend_14 (s : Fin 13 → List Bool) (a b c : List Bool) : extend s a b c 14 = b := rfl
@[simp] theorem extend_15 (s : Fin 13 → List Bool) (a b c : List Bool) : extend s a b c 15 = c := rfl

def inputState (input : List Bool) : Fin 16 → List Bool :=
  extend (KS.W06.RationalCompare.fields input [] [] [] [] [] []) [] [] []

def preparedState (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) : Fin 16 → List Bool :=
  extend (KS.W06.RationalCompare.workFields [sa] na da [sb] nb db [] []) [] [] []

def leftDenCopyPorts : Fin 3 ↪ Fin 16 := ⟨![3,13,9], by decide⟩
def rightDenCopyPorts : Fin 3 ↪ Fin 16 := ⟨![6,14,9], by decide⟩
def denominatorProductPorts : Fin 7 ↪ Fin 16 := ⟨![9,13,14,15,10,11,12], by decide⟩

def savedState (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) : Fin 16 → List Bool :=
  extend (KS.W06.RationalCompare.workFields [sa] na da [sb] nb db [] []) da db []

def productsAfter (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) : Fin 16 → List Bool :=
  extend (KS.W06.RationalCompare.productsAfter sa na da sb nb db) []
    (KS.W03.MultiplicationLoop.advance da db) (product da db)

def productsTicks (na da nb db : List Bool) : ℕ :=
  ((2 * da.length + 2) + (2 * db.length + 2)) +
    (productTicks na db + productTicks nb da) + productTicks da db

def signedState (sa : Bool) (xs : List Bool) (sb : Bool) (ys den : List Bool) : Fin 16 → List Bool :=
  ![[],[sa],[],[],[sb],[],[],xs,ys,[],[],[],[],[],[],den]

def clearProductsTicks (na da nb db : List Bool) : ℕ :=
  (KS.W03.MultiplicationLoop.advance nb da).length + 1 +
    ((KS.W03.MultiplicationLoop.advance na db).length + 1) +
    ((KS.W03.MultiplicationLoop.advance da db).length + 1)

end KS.W13.RationalAdd

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalAddSigned
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W13.RationalAdd
open KS.W06.RationalCompare (signAfter )
open KS.W19.UnsignedPairSerializer (registers)

def readyState (s : Bool) (num den : List Bool) : Fin 16 → List Bool :=
  extend (KS.W30.RationalMagnitudeMachine.state num den s) [] [] []

def numeratorAt (sa sb : Bool) (loc : Fin 16) (num den : List Bool) : Fin 16 → List Bool :=
  fun j => if j = loc then num else signedState sa [] sb [] den j

def addPorts : Fin 3 ↪ Fin 16 := ⟨![7,8,9], by decide⟩
def rightSubtractPorts : Fin 3 ↪ Fin 16 := ⟨![8,7,9], by decide⟩

def arithmeticBudget (xs ys den : List Bool) : ℕ := 16 * (xs.length + ys.length + den.length + 1)

def compareLeftCopyPorts : Fin 3 ↪ Fin 16 := ⟨![7,10,9], by decide⟩
def compareRightCopyPorts : Fin 3 ↪ Fin 16 := ⟨![8,11,9], by decide⟩
def comparePorts : Fin 3 ↪ Fin 16 := ⟨![10,11,12], by decide⟩

def comparedState (sa : Bool) (xs : List Bool) (sb : Bool) (ys den : List Bool) : Fin 16 → List Bool :=
  Function.update (signedState sa xs sb ys den) 12 [decide (KS.W19.bitsValue xs ≤ KS.W19.bitsValue ys)]

def signedBudget (xs ys den : List Bool) : ℕ := 32 * (xs.length + ys.length + den.length + 1)

end KS.W13.RationalAdd

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_DivisionCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.BinaryRational
open KS.W19 KS.W30.BinaryGCD

def normalizeDivisionPair (qr : List Bool × List Bool) : List Bool × List Bool :=
  (trimBits qr.1, trimBits qr.2)

theorem division_values_unique {a d q r : ℕ} (hd : 0 < d)
    (he : a = d * q + r) (hr : r < d) : q = a / d ∧ r = a % d := by
  constructor
  · rw [he, Nat.add_comm (d * q), Nat.add_mul_div_left _ _ hd,
      Nat.div_eq_of_lt hr, Nat.zero_add]
  · rw [he]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hr]

theorem normalizeDivisionPair_eq_divideBits (divisor xs : List Bool)
    (qr : List Bool × List Bool) (hd : 0 < bitsValue divisor)
    (he : bitsValue xs = bitsValue divisor * bitsValue qr.1 + bitsValue qr.2)
    (hr : bitsValue qr.2 < bitsValue divisor) :
    normalizeDivisionPair qr = normalizeDivisionPair (divideBits divisor xs) := by
  obtain ⟨hq, hr'⟩ := division_values_unique hd he hr
  apply Prod.ext
  · apply canonicalBits_injective (trimBits_canonical _) (trimBits_canonical _)
    simpa only [normalizeDivisionPair, trimBits_value, quotient_value _ _ hd] using hq
  · apply canonicalBits_injective (trimBits_canonical _) (trimBits_canonical _)
    simpa only [normalizeDivisionPair, trimBits_value, remainder_value _ _ hd] using hr'

end KS.W30.BinaryRational

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_DivisionLoopModel
attribute [-simp] _root_.OAI.KS.W03.BinaryMultiply.shift_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.DivisionLoop
open KS.W19

def advance (divisor : List Bool) (b : Bool) (q r : List Bool) : List Bool × List Bool :=
  let trial := b :: r
  if subtractionBorrow trial divisor false then (false :: q, trial)
  else (true :: q, trimBits (subtractBits trial divisor false))

theorem advance_correct (divisor : List Bool) (b : Bool) (q r : List Bool)
    (hd : 0 < bitsValue divisor) (hr : bitsValue r < bitsValue divisor) :
    bitsValue divisor * bitsValue (advance divisor b q r).1 +
        bitsValue (advance divisor b q r).2 =
      2 * (bitsValue divisor * bitsValue q + bitsValue r) + digit b ∧
      bitsValue (advance divisor b q r).2 < bitsValue divisor := by
  have hb := digit_le_one b
  by_cases hc : subtractionBorrow (b :: r) divisor false = true
  · have hlt := (subtractionBorrow_true_iff _ _ _).1 hc
    simp only [digit_false, Nat.add_zero] at hlt
    simp only [advance, hc, ↓reduceIte, bitsValue, digit_false, Nat.zero_add]
    constructor
    · ring
    · exact hlt
  · have hle : bitsValue divisor ≤ bitsValue (b :: r) := by
      apply Nat.le_of_not_gt
      intro hlt
      apply hc
      exact (subtractionBorrow_true_iff (b :: r) divisor false).2
        (by simpa only [digit_false, Nat.add_zero] using hlt)
    have hs := subtractBits_correct (b :: r) divisor false (by simpa only [digit_false, Nat.add_zero] using hle)
    simp only [digit_false, Nat.add_zero, bitsValue] at hs
    simp only [advance, hc, Bool.false_eq_true, ↓reduceIte, trimBits_value, bitsValue, digit_true]
    constructor
    · nlinarith
    · apply (Nat.lt_iff_le_pred hd).2
      omega

def process (divisor : List Bool) : List Bool → List Bool → List Bool → List Bool × List Bool
  | [], q, r => (q,r)
  | b :: bs, q, r =>
    let qr := advance divisor b q r
    process divisor bs qr.1 qr.2

theorem bitsValue_append_digit (xs : List Bool) (b : Bool) :
    bitsValue (xs ++ [b]) = bitsValue xs + digit b * 2 ^ xs.length := by
  induction xs with
  | nil => simp [bitsValue]
  | cons a as ih => simp [bitsValue, ih, pow_succ] <;> ring

theorem process_correct (divisor pending q r : List Bool)
    (hd : 0 < bitsValue divisor) (hr : bitsValue r < bitsValue divisor) :
    bitsValue divisor * bitsValue (process divisor pending q r).1 +
        bitsValue (process divisor pending q r).2 =
      (bitsValue divisor * bitsValue q + bitsValue r) * 2 ^ pending.length +
        bitsValue pending.reverse ∧
      bitsValue (process divisor pending q r).2 < bitsValue divisor := by
  induction pending generalizing q r with
  | nil => simpa [process, bitsValue] using hr
  | cons b bs ih =>
    have ha := advance_correct divisor b q r hd hr
    have ht := ih (advance divisor b q r).1 (advance divisor b q r).2 ha.2
    simp only [process]
    constructor
    · rw [ht.1, ha.1]
      simp only [List.length_cons, List.reverse_cons, bitsValue_append_digit, List.length_reverse, pow_succ]
      ring
    · exact ht.2

theorem process_payload_correct (divisor xs : List Bool) (hd : 0 < bitsValue divisor) :
    let qr := process divisor xs.reverse [] []
    bitsValue xs = bitsValue divisor * bitsValue qr.1 + bitsValue qr.2 ∧
      bitsValue qr.2 < bitsValue divisor := by
  have h := process_correct divisor xs.reverse [] [] hd (by simpa only [bitsValue] using hd)
  simp only [bitsValue, Nat.mul_zero, Nat.zero_add, Nat.zero_mul, List.reverse_reverse] at h
  exact ⟨h.1.symm, h.2⟩

theorem advance_quotient_length (divisor : List Bool) (b : Bool) (q r : List Bool) :
    (advance divisor b q r).1.length = q.length + 1 := by
  unfold advance
  dsimp only
  split <;> rfl

theorem advance_remainder_length (divisor : List Bool) (b : Bool) (q r : List Bool) :
    (advance divisor b q r).2.length ≤ max (r.length + 1) divisor.length := by
  unfold advance
  dsimp only
  split
  · simp only [List.length_cons]
    omega
  · exact (trimBits_length_le _).trans (by rw [subtractBits_length]; rfl)

theorem process_quotient_length (d pending q r : List Bool) :
    (process d pending q r).1.length = q.length + pending.length := by
  induction pending generalizing q r with
  | nil => simp [process]
  | cons b bs ih =>
    simp only [process, ih, advance_quotient_length, List.length_cons]
    omega

theorem process_remainder_length (d pending q r : List Bool) :
    (process d pending q r).2.length ≤ max r.length d.length + pending.length := by
  induction pending generalizing q r with
  | nil => simp only [process, List.length_nil, Nat.add_zero]; omega
  | cons b bs ih =>
    have ht := ih (advance d b q r).1 (advance d b q r).2
    have hr := advance_remainder_length d b q r
    simp only [process, List.length_cons]
    omega

end KS.W19.DivisionLoop

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_DivisionLoopBridge
attribute [-simp] _root_.OAI.KS.W03.BinaryMultiply.shift_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.BinaryRational
open KS.W19

theorem divisionLoop_canonical_outputs (divisor xs : List Bool)
    (hd : 0 < bitsValue divisor) :
    normalizeDivisionPair (DivisionLoop.process divisor xs.reverse [] []) =
      normalizeDivisionPair (divideBits divisor xs) := by
  have h := DivisionLoop.process_payload_correct divisor xs hd
  exact normalizeDivisionPair_eq_divideBits divisor xs _ hd h.1 h.2

@[simp] theorem divisionLoop_trim_quotient (divisor xs : List Bool)
    (hd : 0 < bitsValue divisor) :
    trimBits (DivisionLoop.process divisor xs.reverse [] []).1 =
      trimBits (divideBits divisor xs).1 :=
  congrArg Prod.fst (divisionLoop_canonical_outputs divisor xs hd)

@[simp] theorem divisionLoop_trim_remainder (divisor xs : List Bool)
    (hd : 0 < bitsValue divisor) :
    trimBits (DivisionLoop.process divisor xs.reverse [] []).2 =
      trimBits (divideBits divisor xs).2 :=
  congrArg Prod.snd (divisionLoop_canonical_outputs divisor xs hd)

end KS.W30.BinaryRational

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_DivisionBodyTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.DivisionMachine

def bodyFuel (d r : List Bool) : Nat :=
  (2 * r.length + 2) + ((2 * d.length + 2) + ((max r.length d.length + 1) +
    (1 + if subtractionBorrow r d false then max r.length d.length + 1
      else (r.length + 1) + (max r.length d.length + 1))))

def trialResult (d q r : List Bool) : List Bool × List Bool :=
  if subtractionBorrow r d false then (false :: q,r)
  else (true :: q, trimBits (subtractBits r d false))

theorem trialResult_advance (d q r : List Bool) (b : Bool) :
    trialResult d q (b :: r) = DivisionLoop.advance d b q r := rfl

theorem split_exact (bits : List Bool) (a b : Nat) (hb : bits.length = a + b) :
    ∃ first second, bits = first ++ second ∧ first.length = a ∧ second.length = b := by
  refine ⟨bits.take a, bits.drop a, (List.take_append_drop a bits).symm, ?_, ?_⟩
  · simp only [List.length_take, hb]
    omega
  · simp only [List.length_drop, hb]
    omega

theorem bodyFuel_linear (d r : List Bool) : bodyFuel d r ≤ 8 * (r.length + d.length + 1) := by
  unfold bodyFuel
  split <;> omega

end KS.W19.DivisionMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_GCDMachineStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.GCDMachine
open KS.W19

lemma process_quotient_length (d pending q r : List Bool) :
    (DivisionLoop.process d pending q r).1.length = pending.length + q.length := by
  induction pending generalizing q r with
  | nil => simp [DivisionLoop.process]
  | cons b bs ih =>
    rw [DivisionLoop.process, ih, DivisionLoop.advance_quotient_length]
    simp only [List.length_cons]
    omega

lemma process_remainder_length (d pending q r : List Bool) (R : ℕ)
    (hr : r.length + pending.length ≤ R) (hd : d.length + pending.length ≤ R) :
    (DivisionLoop.process d pending q r).2.length ≤ R := by
  induction pending generalizing q r with
  | nil => simpa [DivisionLoop.process] using hr
  | cons b bs ih =>
    rw [DivisionLoop.process]
    apply ih
    · have h := DivisionLoop.advance_remainder_length d b q r
      simp only [List.length_cons] at hr hd
      omega
    · simp only [List.length_cons] at hd
      omega

end KS.W30.GCDMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_GCDMachineRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.GCDMachine
open KS.W19 KS.W30.BinaryGCD

lemma canonical_eq_encode (xs : List Bool) (h : CanonicalBits xs) :
    xs = Computability.encodeNat (bitsValue xs) := by
  apply canonicalBits_injective h (canonicalBits_encodeNat _)
  rw [bitsValue_encodeNat]

end KS.W30.GCDMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_GCDMachinePolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.GCDMachine
open KS.W19

def outputState (g : List Bool) : Fin 10 → List Bool :=
  DivisionMachine.«stacks» [] [] g [] [] [] [] []

end KS.W30.GCDMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalMagnitudeSetup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W30.RationalMagnitudeMachine
open KS.W19

theorem stacks_core (work : Fin 10 → List Bool) (num den : List Bool) (negative : Bool)
    (i : Fin 10) : «stacks» work num den negative (corePorts i)=work i :=by
  fin_cases i <;> rfl

theorem stacks_spare_value (work : Fin 10 → List Bool) (num den : List Bool)
    (negative : Bool) (j : Fin 13) (hj : 10≤j.val) :
    «stacks» work num den negative j=
      (if j=10 then num else if j=11 then den else [negative]) :=by
  have he : j.val=10 ∨ j.val=11 ∨ j.val=12 :=by omega
  rcases he with h | h | h
  · have he : j=10 :=Fin.ext h
    rw [he]
    simp [«stacks»]
  · have he : j=11 :=Fin.ext h
    rw [he]
    simp [«stacks»]
  · have he : j=12 :=Fin.ext h
    rw [he]
    simp [«stacks»]

theorem stacks_spare (before after : Fin 10 → List Bool) (num den : List Bool)
    (negative : Bool) (j : Fin 13) (hj : ∀i,j≠corePorts i) :
    «stacks» after num den negative j=«stacks» before num den negative j :=by
  have hn : 10≤j.val :=by
    by_contra hn
    have h : j.val<10 :=by omega
    exact hj ⟨j.val,h⟩ (Fin.ext rfl)
  rw [stacks_spare_value _ _ _ _ _ hn,stacks_spare_value _ _ _ _ _ hn]

def copiedNumeratorWork (n : List Bool) : Fin 10 → List Bool :=
  ![[],n,[],[],[],[],[],[],[],[]]

def reversedGCDWork (g : List Bool) : Fin 10 → List Bool :=
  DivisionMachine.«stacks» [] [] [] [] [] [] g.reverse []
def divisorWork (g : List Bool) : Fin 10 → List Bool :=
  DivisionMachine.«stacks» g [] [] [] [] [] [] []
def divisorState (g n d : List Bool) (s : Bool) : Fin 13 → List Bool :=
  «stacks» (divisorWork g) n d s

end KS.W30.RationalMagnitudeMachine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalMagnitudeDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.RationalMagnitudeMachine
open KS.W19

def divisionWork (g x : List Bool) : Fin 10 → List Bool :=
  DivisionMachine.«stacks» g x.reverse [] [] [] [] [] []
def quotientWork (g q r : List Bool) : Fin 10 → List Bool :=
  DivisionMachine.«stacks» g [] q r [] [] [] []
def reversedQuotientWork (g q r : List Bool) : Fin 10 → List Bool :=
  DivisionMachine.«stacks» g [] [] r [] [] q.reverse []
def remainderWork (g r : List Bool) : Fin 10 → List Bool :=
  DivisionMachine.«stacks» g [] [] r [] [] [] []

end KS.W30.RationalMagnitudeMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalMagnitudePositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.RationalMagnitudeMachine
open KS.W19 KS.W30.BinaryGCD

theorem positive_output_pair (n d : List Bool) (hd : 0 < bitsValue d) :
    let g := Computability.encodeNat (Nat.gcd (bitsValue n) (bitsValue d))
    KS.W30.BinaryRational.normalizeMagnitude n d =
      (trimBits (DivisionLoop.process g n.reverse [] []).1,
       trimBits (DivisionLoop.process g d.reverse [] []).1) := by
  dsimp only
  have hg : 0 < bitsValue (Computability.encodeNat (Nat.gcd (bitsValue n) (bitsValue d))) := by
    rw [bitsValue_encodeNat]
    exact Nat.gcd_pos_of_pos_right _ hd
  have hd' : trimBits d ≠ [] := by
    intro h
    have hh := (trim_eq_nil_iff d).mp h
    omega
  rw [KS.W30.BinaryRational.normalizeMagnitude, ite_eq_right hd', gcdBits_eq_encodeNat,
    KS.W30.BinaryRational.divisionLoop_trim_quotient _ n hg,
    KS.W30.BinaryRational.divisionLoop_trim_quotient _ d hg]

end KS.W30.RationalMagnitudeMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_WireMagnitude
attribute [-simp] _root_.OAI.KS.W03.BinaryMultiply.shift_value _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_quotient _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_remainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W01.WireMagnitude
open KS.W19

def decrement (xs : List Bool) : List Bool :=
  trimBits (subtractBits xs [true] false)

theorem decrement_encode_succ (n : ℕ) :
    decrement (Computability.encodeNat (n + 1)) = Computability.encodeNat n := by
  have h := subtractBits_correct (Computability.encodeNat (n + 1)) [true] false
    (by simp [bitsValue, digit, bitsValue_encodeNat])
  have hv : bitsValue (subtractBits (Computability.encodeNat (n + 1)) [true] false) = n := by
    simp only [bitsValue_encodeNat, bitsValue, digit_true, digit_false] at h
    omega
  unfold decrement
  rw [trimBits_eq_encodeNat, hv]

theorem decrement_length_le (xs : List Bool) :
    (decrement xs).length ≤ max xs.length 1 := by
  exact (trimBits_length_le _).trans_eq (by simp [subtractBits_length])

def constructorPayload (negative : Bool) (magnitude : List Bool) : List Bool :=
  if negative then decrement magnitude else trimBits magnitude

end KS.W01.WireMagnitude

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_SignedRationalSerializer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W01.SignedRationalSerializer

abbrev Registers := Fin 13 → List Bool

def inputState (num den : List Bool) (sgn : Bool) : Registers :=
  ![[],[],[],[],[],[],[],[],[],[],num,den,[sgn]]
def selectedState (num den : List Bool) (sgn : Bool) : Registers :=
  ![[],[],[],[],[],[],[],[],[sgn],[],num,den,[]]
def oneState (num den : List Bool) : Registers :=
  ![[],[],[],[],[],[],[],[],[true],[true],num,den,[]]
def decrementedState (num den : List Bool) : Registers :=
  ![[],[],[],[],[],[],[],[],[true],WireMagnitude.decrement num,[],den,[]]
def reverseState (wire : List Bool) : Registers :=
  ![[],[],[],[],[],[],[],[],wire.reverse,[],[],[],[]]
def outputState (wire : List Bool) : Registers :=
  ![[],[],[],[],[],[],[],[],[],[],wire,[],[]]

def positivePorts : Fin 3 ↪ Fin 13 := ⟨![10,11,8], by decide⟩
def negativePorts : Fin 3 ↪ Fin 13 := ⟨![9,11,8], by decide⟩
def subtractPorts : Fin 3 ↪ Fin 13 := ⟨![10,9,7], by decide⟩
def reversePorts : Fin 3 ↪ Fin 13 := ⟨![0,10,8], by decide⟩

end KS.W01.SignedRationalSerializer

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalAddProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W13.RationalAdd
open KS.W06.RationalCompare (magnitude product negativeBit )

def preNormalizeTicks (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) : ℕ :=
  let a := magnitude sa na
  let b := magnitude sb nb
  ((KS.W06.RationalCompare.parseTicks na da nb db + (2 * na.length + 4) + (2 * nb.length + 4)) +
    productsTicks a da b db + clearProductsTicks a da b db) +
    signedBudget (product a db) (product b da) (product da db)

def rawInputSum (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    KS.W30.BinaryRational.RatBits := rawSum sa (magnitude sa na) da sb (magnitude sb nb) db

def payloadBound (na da nb db : List Bool) : ℕ := na.length + da.length + nb.length + db.length + 3

def outputState (wire : List Bool) : Fin 16 → List Bool :=
  extend (KS.W01.SignedRationalSerializer.outputState wire) [] [] []

end KS.W13.RationalAdd

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalMultiplyNormalize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W15.RationalMultiply
open KS.W06.RationalCompare (magnitude product productTicks parseTicks negativeBit fields signedFraction)

def rawProduct (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    KS.W30.BinaryRational.RatBits :=
  ⟨sa ^^ sb, product na nb, product da db⟩

theorem rawProduct_value (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    (rawProduct sa na da sb nb db).value =
      signedFraction sa (KS.W19.bitsValue na) (KS.W19.bitsValue da) *
        signedFraction sb (KS.W19.bitsValue nb) (KS.W19.bitsValue db) := by
  cases sa <;> cases sb <;>
    simp [rawProduct, KS.W30.BinaryRational.RatBits.value,
      KS.W30.BinaryRational.RatBits.magnitude, product, KS.W19.bitsValue_encodeNat,
      signedFraction, Nat.cast_mul, div_mul_div_comm, neg_div]

def payloadSize (na da nb db : List Bool) : Nat := na.length + da.length + nb.length + db.length

def normalizeTicks (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) : Nat :=
  let a := magnitude sa na
  let b := magnitude sb nb
  ((parseTicks na da nb db + (2 * na.length + 4) + (2 * nb.length + 4)) +
    (productTicks a b + productTicks da db) + cleanupTicks a da b db) +
      300 * (payloadSize na da nb db + 3) ^ 3

end KS.W15.RationalMultiply

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_WireProgramPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W15.WireProgram

def transferAfter {k : Nat} (source target : Fin k) (before : Fin k → List Bool) :
    Fin k → List Bool :=
  fun j => if j = source then [] else if j = target then before source ++ before target else before j

end KS.W15.WireProgram

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_ComplexScalarNodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W15.ComplexMachine
open KS.W15.WireProgram

abbrev Registers := Fin 28 → List Bool

def corePorts : Fin 16 ↪ Fin 28 :=
  ⟨fun i => ⟨i.val,by omega⟩,by intro i j h; exact Fin.ext (congrArg (fun p : Fin 28 => p.val) h)⟩
def mulPorts : Fin 13 ↪ Fin 28 :=
  ⟨fun i => ⟨i.val,by omega⟩,by intro i j h; exact Fin.ext (congrArg (fun p : Fin 28 => p.val) h)⟩

@[simp] theorem corePorts_apply (i : Fin 16) :
    corePorts i = ⟨i.val, by omega⟩ := rfl

@[simp] theorem mulPorts_apply (i : Fin 13) :
    mulPorts i = ⟨i.val, by omega⟩ := rfl

def CoreEmpty (s : Registers) : Prop := ∀ i : Fin 16, s (corePorts i) = []

theorem coreEmpty_apply (s : Registers) (h : CoreEmpty s) (j : Fin 28) (hj : j.val < 16) :
    s j = [] := by
  have he : corePorts ⟨j.val,hj⟩ = j := Fin.ext rfl
  simpa only [he] using h ⟨j.val,hj⟩

theorem stored_ne_core (a : Fin 28) (ha : 16 ≤ a.val) (i : Fin 16) : a ≠ corePorts i := by
  intro h
  have hv := congrArg Fin.val h
  change a.val = i.val at hv
  have hi := i.isLt
  omega

def pairTicks (x y : List Bool) : Nat := 4 * x.length + 2 * y.length + 6

theorem coreEmpty_update (before : Registers) (hclear : CoreEmpty before)
    (dest : Fin 28) (hd : 16 ≤ dest.val) (wire : List Bool) :
    CoreEmpty (Function.update before dest wire) := by
  intro i
  rw [Function.update_of_ne (stored_ne_core dest hd i).symm]
  exact hclear i

end KS.W15.ComplexMachine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_DivisionInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.DivisionInput

def firstPorts : Fin 3 ↪ Fin 10 := ⟨![0,1,9], by decide⟩
def secondPorts : Fin 3 ↪ Fin 10 := ⟨![0,2,9], by decide⟩

def «stacks» (input xs d pending : List Bool) : Fin 10 → List Bool :=
  ![input,xs,d,pending,[],[],[],[],[],[]]

def inputFuel (xs d : List Bool) : Nat :=
  (3 * xs.length + 2) + ((3 * d.length + 2) + ((xs.length + 1) +
    (xs.length * (8 * (xs.length + 2 * d.length + 2) + 1) + 1)))

end KS.W19.DivisionInput

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_DivisionOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.DivisionOutput
open KS.W19.DivisionMachine («stacks»)

def canonical (xs : List Bool) : List Bool := Computability.encodeNat (bitsValue xs)

theorem canonical_length (xs : List Bool) : (canonical xs).length ≤ xs.length := by
  rw [canonical, ← trimBits_eq_encodeNat]
  exact trimBits_length_le xs

end KS.W19.DivisionOutput

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_EncodedDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.EncodedDivision

def resultPair (xs d : List Bool) : List Bool × List Bool := DivisionLoop.process d xs.reverse [] []

end KS.W19.EncodedDivision

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_FixedBinaryAdder
attribute [-simp] _root_.OAI.KS.W03.BinaryMultiply.shift_value _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_quotient _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_remainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W01.FixedBinaryAdder
open KS.W29

def result (xs ys : List Bool) : List Bool := BinaryAdder.addBits false xs ys

def ticks (xs ys : List Bool) : ℕ := max xs.length ys.length + 1 + ((result xs ys).length + 1)

def output {k : ℕ} (ports : Fin 3 ↪ Fin k) (store : Fin k → List Bool)
    (xs ys : List Bool) : Fin k → List Bool :=
  Function.update (Function.update store (ports 0) []) (ports 1) (result xs ys)

theorem result_value (xs ys : List Bool) :
    KS.W19.bitsValue (result xs ys) = KS.W19.bitsValue xs + KS.W19.bitsValue ys := by
  simpa [result, KS.W19.digit] using BinaryAdder.addBits_correct false xs ys

end KS.W01.FixedBinaryAdder

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SignedFloorModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.SignedFloor

theorem loop_quotient (d xs : List Bool) (hd : 0 < bitsValue d) :
    bitsValue (DivisionLoop.process d xs.reverse [] []).1 = bitsValue xs / bitsValue d := by
  have h := DivisionLoop.process_payload_correct d xs hd
  symm
  apply Nat.div_eq_of_lt_le <;> nlinarith [h.1, h.2]

theorem old_quotient (d xs : List Bool) (hd : 0 < bitsValue d) :
    bitsValue (divideBits d xs).1 = bitsValue xs / bitsValue d := by
  have h := divideBits_correct d xs hd
  symm
  apply Nat.div_eq_of_lt_le <;> nlinarith [h.1, h.2]

end KS.W19.SignedFloor

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SignedFloorMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.SignedFloorMachine

def naturalPorts : Fin 10 ↪ Fin 11 :=
  Fin.castLEEmb (by decide)
def canonPorts : Fin 3 ↪ Fin 11 := ⟨![0,5,8], by decide⟩
def outputPorts : Fin 3 ↪ Fin 11 := ⟨![0,5,10], by decide⟩

def «stacks» (input d q r sign : List Bool) : Fin 11 → List Bool :=
  ![input,[],d,[],r,q,[],[],[],[],sign]

end KS.W19.SignedFloorMachine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_FloorRationalMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W20.FloorRationalMachine
open KS.W19

abbrev Registers := Fin 11 → List Bool

def state (input output : List Bool) : Registers :=
  SignedFloorMachine.«stacks» input [] output [] []

end KS.W20.FloorRationalMachine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_MultiplicationInitialize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W03.MultiplicationInitialize

open KS.W03.MultiplicationBody

def firstPorts : Fin 3 ↪ Fin 7 := ⟨![0, 1, 6], by decide⟩
def secondPorts : Fin 3 ↪ Fin 7 := ⟨![0, 2, 6], by decide⟩

end KS.W03.MultiplicationInitialize

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalReciprocalSwap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W30.RationalReciprocal
open KS.W19

def transferred (before : Fin 13 → List Bool) (source target : Fin 13) : Fin 13 → List Bool :=
  fun j => if j = source then [] else if j = target then before source else before j

def savedState (n d : List Bool) (sgn : Bool) : Fin 13 → List Bool :=
  RationalMagnitudeMachine.«stacks» ![[],[],[],[],[],[],[],[],[],n] [] d sgn
def shiftedState (n d : List Bool) (sgn : Bool) : Fin 13 → List Bool :=
  RationalMagnitudeMachine.«stacks» ![[],[],[],[],[],[],[],[],[],n] d [] sgn

end KS.W30.RationalReciprocal

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalReciprocalCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.RationalReciprocal
open KS.W19
open KS.W30.BinaryRational

def canonicalState (q : ℚ) : Fin 13 → List Bool :=
  RationalMagnitudeMachine.state (Computability.encodeNat q.num.natAbs)
    (Computability.encodeNat q.den) (decide (q.num < 0))

end KS.W30.RationalReciprocal

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_SingleRationalParser
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W06.SingleRationalParser

open KS.W06.RationalCompare

theorem magnitude_result_canonical (carry : Bool) (xs : List Bool)
    (hx : KS.W19.CanonicalBits xs) :
    KS.W19.CanonicalBits (KS.W01.MagnitudeProgram.result carry xs) := by
  induction xs generalizing carry with
  | nil =>
    cases carry <;> simp [KS.W01.MagnitudeProgram.result, KS.W01.BinaryAdder.addBits,
      KS.W19.CanonicalBits]
  | cons b bs ih =>
    rcases hx with ⟨hbs, hlast⟩
    rw [KS.W01.MagnitudeProgram.result, KS.W01.BinaryAdder.addBits]
    refine ⟨ih _ hbs, ?_⟩
    intro hnil
    cases bs with
    | cons d ds => simp [KS.W01.BinaryAdder.addBits] at hnil
    | nil =>
      have hb : b = true := hlast rfl
      subst b
      cases carry <;>
        simp [KS.W01.BinaryAdder.addBits, KS.W01.BinaryAdder.carryBit,
          KS.W01.BinaryAdder.sumBit] at hnil ⊢

def numeratorPorts : Fin 3 ↪ Fin 6 := ⟨![0,3,2], by decide⟩
def denominatorPorts : Fin 3 ↪ Fin 6 := ⟨![0,4,2], by decide⟩
def magnitudePorts : Fin 3 ↪ Fin 6 := ⟨![1,3,2], by decide⟩

def baseState (input num den sign : List Bool) : Fin 6 → List Bool :=
  ![input,[],[],num,den,sign]

def baseTicks (num den : List Bool) : ℕ := 5 * num.length + 3 * den.length + 9

def normalizerPorts : Fin 6 ↪ Fin 13 := ⟨![0,1,2,10,11,12], by decide⟩

def state (tail num den : List Bool) (sign : Bool) : Fin 13 → List Bool :=
  ![tail,[],[],[],[],[],[],[],[],[],num,den,[sign]]

def inputState (input : List Bool) : Fin 13 → List Bool :=
  ![input,[],[],[],[],[],[],[],[],[],[],[],[]]

def canonicalState (q : ℚ) (tail : List Bool := []) : Fin 13 → List Bool :=
  state tail (Computability.encodeNat q.num.natAbs) (Computability.encodeNat q.den)
    (decide (q.num < 0))

end KS.W06.SingleRationalParser

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalReciprocalMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W30.RationalReciprocal

def inputState (wire : List Bool) : Fin 13 → List Bool :=
  KS.W06.SingleRationalParser.inputState wire

def outputState (wire : List Bool) : Fin 13 → List Bool :=
  KS.W01.SignedRationalSerializer.outputState wire

end KS.W30.RationalReciprocal

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalDivisionStages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W30.RationalDivision

def corePorts : Fin 13 ↪ Fin 15 :=
  ⟨fun i => ⟨i.val, by omega⟩, by intro i j h; exact Fin.ext (congrArg (fun j : Fin 15=>j.val) h)⟩
def «stacks» (c : Fin 13 → List Bool) (den num : List Bool) : Fin 15 → List Bool :=
  ![c 0,c 1,c 2,c 3,c 4,c 5,c 6,c 7,c 8,c 9,c 10,c 11,c 12,den,num]

theorem stacks_core (c : Fin 13→List Bool) (den num : List Bool) (i : Fin 13) :
    «stacks» c den num (corePorts i)=c i :=by
  fin_cases i <;> rfl

theorem stacks_spare_value (c : Fin 13→List Bool) (den num : List Bool)
    (j : Fin 15) (hj : 13≤j.val) :
    «stacks» c den num j=(if j=(13 : Fin 15) then den else num) :=by
  have h : j.val=13 ∨ j.val=14 :=by omega
  rcases h with h | h
  · have he : j=(13 : Fin 15) :=Fin.ext h
    rw [he]
    simp [«stacks»]
  · have he : j=(14 : Fin 15) :=Fin.ext h
    rw [he]
    simp [«stacks»]

theorem stacks_spare (before after : Fin 13→List Bool) (den num : List Bool)
    (j : Fin 15) (hj : ∀i,j≠corePorts i) :
    «stacks» after den num j=«stacks» before den num j :=by
  have hb : 13≤j.val :=by
    by_contra h
    have hi : j.val<13 :=by omega
    exact hj ⟨j.val,hi⟩ (Fin.ext rfl)
  rw [stacks_spare_value _ _ _ _ hb,stacks_spare_value _ _ _ _ hb]

def inputState (wire : List Bool) : Fin 15 → List Bool :=
  «stacks» (RationalReciprocal.inputState wire) [] []
def outputState (wire : List Bool) : Fin 15 → List Bool :=
  «stacks» (RationalReciprocal.outputState wire) [] []

def serializerTicks (q : ℚ) : ℕ :=
  16 * ((Computability.encodeNat q.num.natAbs).length + (Computability.encodeNat q.den).length + 1)

end KS.W30.RationalDivision

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedDotModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W12.FixedDot

open scoped BigOperators

def dotValue (ps : List (ℚ × ℚ)) : ℚ := (ps.map (fun p => p.1 * p.2)).sum

end KS.W12.FixedDot

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedDotControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.FixedDot

def registers (source input product accumulator temporary : List Bool) : Fin 19 → List Bool :=
  fun j => if j = 16 then source else if j = 0 then input else if j = 10 then product
    else if j = 17 then accumulator else if j = 18 then temporary else []

def loopTicks (bodyTicks : (ℚ × ℚ) → ℚ → ℕ) : List (ℚ × ℚ) → ℚ → ℕ
  | [], _ => 1
  | p :: ps, a => 1 + bodyTicks p a + loopTicks bodyTicks ps (a + p.1 * p.2)

end KS.W12.FixedDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedDotPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W12.FixedDot

def initialPorts (n : ℕ) (hn : n ≤ 19) : Fin n ↪ Fin 19 where
  toFun i := ⟨i.val, lt_of_lt_of_le i.isLt hn⟩
  inj' := fun _ _ h => Fin.ext (congrArg (fun j : Fin 19 => j.val) h)

def transferAfter (source target : Fin 19) (before : Fin 19 → List Bool) : Fin 19 → List Bool :=
  fun j => if j = source then [] else if j = target then before source ++ before target else before j

end KS.W12.FixedDot

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedDotMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.FixedDot

def pushAfter (b : Bool) (before : Fin 19 → List Bool) : Fin 19 → List Bool :=
  fun j => if j = 17 then b :: before j else before j

def initialStacks (source : List Bool) : Fin 19 → List Bool := registers source [] [] [] []

end KS.W12.FixedDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RowDotRegisters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W12.RowDot

abbrev put (s : Fin 29 → List Bool) (j : Fin 29) (v : List Bool) := Function.update s j v

end KS.W12.RowDot

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RowDotCounter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.RowDot

def incrementPorts : Fin 3 ↪ Fin 29 := ⟨![24, 7, 26], by decide⟩

def incrementTicks (k : ℕ) : ℕ := 1 +
  KS.W13.RationalAdd.canonicalAddTicks (Computability.encodeNat k) [true] +
  (2 * (Computability.encodeNat (k + 1)).length + 2)

end KS.W12.RowDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_DenseRatMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W07

abbrev DenseRatMatrix (n : ℕ) := Vector (Vector ℚ n) n

namespace DenseRatMatrix

def decode {n : ℕ} (M : DenseRatMatrix n) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => (M.get i).get j

def ofMatrix {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) : DenseRatMatrix n :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => M i j))

@[simp] theorem decode_ofMatrix {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) :
    decode (ofMatrix M) = M := by
  funext i j
  simp [decode, ofMatrix, Vector.get]
  rfl

@[simp] theorem ofMatrix_decode {n : ℕ} (M : DenseRatMatrix n) :
    ofMatrix (decode M) = M := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [ofMatrix, decode, Vector.get]
  rfl

end DenseRatMatrix

def decodeRatVector {n : ℕ} (v : Vector ℚ n) : Fin n → ℚ := v.get

@[simp] theorem decodeRatVector_ofFn {n : ℕ} (v : Fin n → ℚ) :
    decodeRatVector (Vector.ofFn v) = v := by
  funext i
  simp [decodeRatVector, Vector.get]
  rfl

end KS.W07

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_DenseMatrixSerialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W08

open KS.W07
open scoped BigOperators

def matrixEntryIndex {n : ℕ} (i j : Fin n) : Fin (n * n) := finProdFinEquiv (i, j)

@[simp] theorem matrixEntryIndex_val {n : ℕ} (i j : Fin n) :
    (matrixEntryIndex i j).val = i.val * n + j.val := by
  simp [matrixEntryIndex, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

theorem matrixEntryIndex_lt {n : ℕ} (i j : Fin n) : i.val * n + j.val < n * n := by
  simpa using (matrixEntryIndex i j).isLt

def denseMatrixCursor {n : ℕ} (i j : Fin n) : List Bool :=
  List.replicate (i.val * n + j.val) true

@[simp] theorem denseMatrixCursor_length {n : ℕ} (i j : Fin n) :
    (denseMatrixCursor i j).length = i.val * n + j.val := by simp [denseMatrixCursor]

end KS.W08

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RowDotModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W12.RowDot
open KS.W07 Matrix
open scoped BigOperators

def indexedVector {n : ℕ} (x : Fin n → ℚ) : List (Fin n × ℚ) := List.ofFn (fun j => (j, x j))

def Consecutive {n : ℕ} (k : ℕ) (xs : List (Fin n × ℚ)) : Prop :=
  xs.map (fun p => p.1.val) = List.range' k xs.length

theorem consecutive_cons {n : ℕ} (k : ℕ) (p : Fin n × ℚ) (xs : List (Fin n × ℚ)) :
    Consecutive k (p :: xs) ↔ p.1.val = k ∧ Consecutive (k + 1) xs := by
  simp [Consecutive, List.range'_succ]

theorem consecutive_indexedVector {n : ℕ} (x : Fin n → ℚ) : Consecutive 0 (indexedVector x) := by
  unfold Consecutive indexedVector
  apply List.ext_getElem
  · simp
  · intro j hj hk
    simp

def state (matrix vector row dim remaining counter reversed : List Bool) : Fin 29 → List Bool :=
  fun j => if j = 19 then matrix else if j = 20 then vector else if j = 21 then row
    else if j = 22 then dim else if j = 23 then remaining else if j = 24 then counter
    else if j = 25 then reversed else []

end KS.W12.RowDot

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_UnaryArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W03.UnaryArithmetic
open KS.W19

def accumulate : List Bool → ℕ → ℕ
  | [], n => n
  | b :: bs, n => accumulate bs (2 * n + digit b)

theorem accumulate_append (xs ys : List Bool) (n : ℕ) :
    accumulate (xs ++ ys) n = accumulate ys (accumulate xs n) := by
  induction xs generalizing n with
  | nil => rfl
  | cons b bs ih => exact ih (2 * n + digit b)

theorem accumulate_reverse (xs : List Bool) :
    accumulate xs.reverse 0 = bitsValue xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    rw [List.reverse_cons, accumulate_append]
    simp only [accumulate, ih, bitsValue]
    omega

def ticks : List Bool → ℕ → ℕ
  | [], _ => 1
  | b :: bs, n => 4 * n + 3 + ticks bs (2 * n + digit b)

theorem ticks_le_linear (xs : List Bool) (n : ℕ) :
    ticks xs n + 4 * n ≤ 4 * accumulate xs n + 3 * xs.length + 1 := by
  induction xs generalizing n with
  | nil => simp only [ticks, accumulate, List.length_nil]; omega
  | cons b bs ih =>
    have h := ih (2 * n + digit b)
    simp only [ticks, accumulate, List.length_cons]
    omega

def totalTicks (xs : List Bool) : ℕ := xs.length + 1 + ticks xs.reverse 0

theorem totalTicks_le_linear (xs : List Bool) :
    totalTicks xs ≤ 4 * bitsValue xs + 4 * xs.length + 2 := by
  have ht := ticks_le_linear xs.reverse 0
  rw [accumulate_reverse, List.length_reverse] at ht
  unfold totalTicks
  omega

end KS.W03.UnaryArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_BinaryToUnaryMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W03.BinaryToUnary
open KS.W29

def doubleState (b : Bool) : Fin 8 := if b then 5 else 2
def secondState (b : Bool) : Fin 8 := if b then 6 else 3
def restoreState (b : Bool) : Fin 8 := if b then 7 else 4

end KS.W03.BinaryToUnary

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_MatrixCursorPreparation
attribute [-simp] _root_.OAI.KS.W03.BinaryMultiply.shift_value _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_quotient _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_remainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W08

def denseMatrixBinaryCursor {n : ℕ} (i j : Fin n) : List Bool :=
  Computability.encodeNat (i.val * n + j.val)

@[simp] theorem denseMatrixBinaryCursor_value {n : ℕ} (i j : Fin n) :
    KS.W19.bitsValue (denseMatrixBinaryCursor i j) = i.val * n + j.val := by
  simp [denseMatrixBinaryCursor, KS.W19.bitsValue_encodeNat]

end KS.W08

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_RationalCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W08

open scoped BigOperators

structure RatCounted (α : Type*) where
  value : α
  ops : ℕ

namespace RatCounted

variable {α β : Type*}

def pure (x : α) : RatCounted α := ⟨x, 0⟩
def bind (x : RatCounted α) (f : α → RatCounted β) : RatCounted β :=
  let y := f x.value
  ⟨y.value, x.ops + y.ops⟩

end RatCounted

end KS.W08

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_StorageCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W08

open KS.W07
open scoped BigOperators

structure AccessCounted (α : Type*) where
  value : α
  reads : ℕ
  writes : ℕ
  copies : ℕ
  ops : ℕ := 0

namespace AccessCounted

variable {α β : Type*}

def pure (x : α) : AccessCounted α := ⟨x, 0, 0, 0, 0⟩

def bind (x : AccessCounted α) (f : α → AccessCounted β) : AccessCounted β :=
  let y := f x.value
  ⟨y.value, x.reads + y.reads, x.writes + y.writes, x.copies + y.copies, x.ops + y.ops⟩

def work (x : AccessCounted α) : ℕ := x.reads + x.writes + x.copies

def add (x y : ℚ) : AccessCounted ℚ := ⟨x + y, 0, 0, 0, 1⟩
def sub (x y : ℚ) : AccessCounted ℚ := ⟨x - y, 0, 0, 0, 1⟩
def mul (x y : ℚ) : AccessCounted ℚ := ⟨x * y, 0, 0, 0, 1⟩
def div (x y : ℚ) : AccessCounted ℚ := ⟨x / y, 0, 0, 0, 1⟩
def neg (x : ℚ) : AccessCounted ℚ := ⟨-x, 0, 0, 0, 1⟩
def inv (x : ℚ) : AccessCounted ℚ := ⟨x⁻¹, 0, 0, 0, 1⟩
def positive (x : ℚ) : AccessCounted Bool := ⟨decide (0 < x), 0, 0, 0, 1⟩

@[simp] theorem add_work (x y : ℚ) : (add x y).work = 0 := rfl
@[simp] theorem sub_work (x y : ℚ) : (sub x y).work = 0 := rfl
@[simp] theorem mul_work (x y : ℚ) : (mul x y).work = 0 := rfl
@[simp] theorem div_work (x y : ℚ) : (div x y).work = 0 := rfl
@[simp] theorem neg_work (x : ℚ) : (neg x).work = 0 := rfl
@[simp] theorem inv_work (x : ℚ) : (inv x).work = 0 := rfl
@[simp] theorem positive_work (x : ℚ) : (positive x).work = 0 := rfl

def erase (x : AccessCounted α) : RatCounted α := ⟨x.value, x.ops⟩

def ofArithmetic (x : RatCounted α) : AccessCounted α := ⟨x.value, 0, 0, 0, x.ops⟩

@[simp] theorem ofArithmetic_value (x : RatCounted α) : (ofArithmetic x).value = x.value := rfl
@[simp] theorem ofArithmetic_ops (x : RatCounted α) : (ofArithmetic x).ops = x.ops := rfl
@[simp] theorem ofArithmetic_work (x : RatCounted α) : (ofArithmetic x).work = 0 := rfl
@[simp] theorem erase_ofArithmetic (x : RatCounted α) : (ofArithmetic x).erase = x := by
  cases x
  rfl
@[simp] theorem erase_pure (x : α) : (pure x).erase = RatCounted.pure x := rfl
@[simp] theorem erase_bind (x : AccessCounted α) (f : α → AccessCounted β) :
    (bind x f).erase = RatCounted.bind x.erase (fun v => (f v).erase) := rfl

@[simp] theorem pure_ops (x : α) : (pure x).ops = 0 := rfl
@[simp] theorem bind_ops (x : AccessCounted α) (f : α → AccessCounted β) :
    (bind x f).ops = x.ops + (f x.value).ops := rfl

@[simp] theorem pure_work (x : α) : (pure x).work = 0 := rfl

@[simp] theorem bind_work (x : AccessCounted α) (f : α → AccessCounted β) :
    (bind x f).work = x.work + (f x.value).work := by simp [bind, work]; omega

def readVector {n : ℕ} (v : Vector ℚ n) (i : Fin n) : AccessCounted ℚ :=
  let saved := Vector.ofFn v.get
  ⟨saved.get i, n + 1, n, 1, 0⟩

@[simp] theorem readVector_value {n : ℕ} (v : Vector ℚ n) (i : Fin n) :
    (readVector v i).value = v.get i := by
  simp [readVector, Vector.get]
  rfl

@[simp] theorem readVector_ops {n : ℕ} (v : Vector ℚ n) (i : Fin n) :
    (readVector v i).ops = 0 := rfl

@[simp] theorem readVector_work {n : ℕ} (v : Vector ℚ n) (i : Fin n) :
    (readVector v i).work = 2 * n + 2 := by simp [readVector, work]; omega

def readMatrix {n : ℕ} (M : DenseRatMatrix n) (i j : Fin n) : AccessCounted ℚ :=
  let saved := DenseRatMatrix.ofMatrix (DenseRatMatrix.decode M)
  ⟨DenseRatMatrix.decode saved i j, 2 * n * n + 2, n * n + n, 1, 0⟩

@[simp] theorem readMatrix_value {n : ℕ} (M : DenseRatMatrix n) (i j : Fin n) :
    (readMatrix M i j).value = DenseRatMatrix.decode M i j := by simp [readMatrix]

@[simp] theorem readMatrix_ops {n : ℕ} (M : DenseRatMatrix n) (i j : Fin n) :
    (readMatrix M i j).ops = 0 := rfl

@[simp] theorem readMatrix_work {n : ℕ} (M : DenseRatMatrix n) (i j : Fin n) :
    (readMatrix M i j).work = 3 * n ^ 2 + n + 3 := by simp [readMatrix, work] <;> ring

end AccessCounted
end KS.W08

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_FramedArraySkip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W11.FramedArray

def «stacks» (input output scratch index : List Bool) : Fin 4 → List Bool :=
  fun j => if j = 0 then input else if j = 1 then output else if j = 2 then scratch else index

end KS.W11.FramedArray

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_FramedArrayRetrieval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W11.FramedArray

def decoderPorts : Fin 3 ↪ Fin 4 := Fin.castLEEmb (by decide)

end KS.W11.FramedArray

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_ReusableArrayLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W04.ReusableArrayLookup

def arrayStacks (source work payload scratch index : List Bool) : Fin 5 → List Bool :=
  fun j => if j = 0 then source else if j = 1 then work else if j = 2 then payload
    else if j = 3 then scratch else index

def lookupPorts : Fin 4 ↪ Fin 5 := ⟨Fin.succ, Fin.succ_injective 4⟩

theorem arrayStacks_copy_update (source index : List Bool) :
    Function.update (arrayStacks source [] [] [] index) (1 : Fin 5) source =
      arrayStacks source source [] [] index := by
  funext j
  fin_cases j <;> rfl

end KS.W04.ReusableArrayLookup

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_MatrixAddressArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W08.MatrixAddress

open KS.W03.MultiplicationBody KS.W03.BinaryAccumulator

def addPorts : Fin 3 ↪ Fin 7 := ⟨![0, 3, 4], by decide⟩

def rawProduct (row dim : List Bool) : List Bool := loop row dim []
def rawAddress (row dim col : List Bool) : List Bool :=
  KS.W01.FixedBinaryAdder.result col (rawProduct row dim)

def ticks (row dim col : List Bool) : ℕ :=
  ((loopTicks row dim [] + (2 * (col.length + (rawProduct row dim).length) + 3)) +
    (2 * (rawAddress row dim col).length + 2)) +
    ((KS.W03.MultiplicationLoop.advance row dim).length + 1)

theorem ticks_le (row dim col : List Bool) :
    ticks row dim col ≤ 32 * (row.length + dim.length + col.length + 1) ^ 2 := by
  have hm := loop_zero_ticks_le row dim
  have hp := loop_zero_length_le row dim
  have ha := KS.W01.BinaryAdder.addBits_length_le false col (rawProduct row dim)
  have hc := KS.W03.MultiplicationLoop.advance_length row dim
  have hmax : max col.length (rawProduct row dim).length ≤
      col.length + (rawProduct row dim).length := by omega
  unfold ticks rawAddress KS.W01.FixedBinaryAdder.result
  change (rawProduct row dim).length ≤ row.length + dim.length at hp
  nlinarith [Nat.le_max_left col.length (rawProduct row dim).length,
    Nat.le_max_right col.length (rawProduct row dim).length,
    hmax,
    Nat.zero_le (row.length * col.length), Nat.zero_le (dim.length * col.length)]

theorem matrix_address_budget {n : ℕ} (i j : Fin n) :
    32 * (Nat.size i.val + Nat.size n + Nat.size j.val + 1) ^ 2 ≤ 512 * (n + 1) ^ 2 := by
  have hi : Nat.size i.val ≤ n := (Nat.size_le.mpr Nat.lt_two_pow_self).trans i.isLt.le
  have hj : Nat.size j.val ≤ n := (Nat.size_le.mpr Nat.lt_two_pow_self).trans j.isLt.le
  have hn : Nat.size n ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have h : Nat.size i.val + Nat.size n + Nat.size j.val + 1 ≤ 4 * (n + 1) := by omega
  have hs := Nat.pow_le_pow_left h 2
  nlinarith

end KS.W08.MatrixAddress

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_MatrixReadProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W08.MatrixRead

open KS.W03.MultiplicationBody

def workspace (source col row dim address : List Bool) : Fin 8 → List Bool :=
  ![col, row, dim, address, [], [], [], source]

def addressPorts : Fin 7 ↪ Fin 8 := Fin.castLEEmb (by decide)
def accessPorts : Fin 5 ↪ Fin 8 := ⟨![7, 3, 0, 1, 2], by decide⟩

end KS.W08.MatrixRead

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RowDotPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.RowDot

def readPorts : Fin 8 ↪ Fin 29 := ⟨![0, 1, 2, 3, 4, 5, 6, 19], by decide⟩

def readBefore (s : Fin 29 → List Bool) (col row dim : List Bool) : Fin 29 → List Bool :=
  put (put (put s 0 col) 1 row) 2 dim

def decodePorts : Fin 3 ↪ Fin 29 := ⟨![23, 27, 26], by decide⟩

def framePorts : Fin 3 ↪ Fin 29 := ⟨![4, 28, 26], by decide⟩

end KS.W12.RowDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RowDotMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.RowDot
open Matrix
def dotPorts : Fin 19 ↪ Fin 29 := Fin.castLEEmb (by decide)

end KS.W12.RowDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_ZeroPaddedRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.RowDot
open Matrix
open KS.W07
open scoped BigOperators

def zeroPadded {n : ℕ} (y : Fin n → ℚ) : Fin (n + 1) → ℚ := Fin.cons 0 y

end KS.W12.RowDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_NegativeDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.RowDot

def divisionPorts : Fin 15 ↪ Fin 29 := Fin.castLEEmb (by decide)

def arithmeticState (saved : Fin 29 → List Bool) (input output : List Bool) : Fin 29 → List Bool :=
  fun j => if j = 0 then input else if j = 10 then output else if j.val < 19 then [] else saved j

def productPorts : Fin 13 ↪ Fin 29 := Fin.castLEEmb (by decide)

end KS.W12.RowDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalSignAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W16.RationalSignAction

def signedRational (eps : Bool) (q : ℚ) : ℚ := if eps then q else -q

def extend (r : Fin 13 → List Bool) (tape : List Bool) : Fin 14 → List Bool :=
  fun j => if h : j.val < 13 then r ⟨j.val,h⟩ else tape

def corePorts : Fin 13 ↪ Fin 14 := Fin.castLEEmb (by decide)
def inputState (wire tape : List Bool) : Fin 14 → List Bool :=
  extend (KS.W06.SingleRationalParser.inputState wire) tape
def operandState (num den : List Bool) (sgn : Bool) (tape : List Bool) : Fin 14 → List Bool :=
  extend (KS.W01.SignedRationalSerializer.inputState num den sgn) tape
def poppedState (num den tape : List Bool) : Fin 14 → List Bool :=
  ![[],[],[],[],[],[],[],[],[],[],num,den,[],tape]
def outputState (wire tape : List Bool) : Fin 14 → List Bool :=
  extend (KS.W01.SignedRationalSerializer.outputState wire) tape

def chooseSign (num : List Bool) (sgn eps : Bool) : Bool :=
  if num = [] then false else if eps then sgn else !sgn

def headSign (heads : Fin 14 → Fin 3) : Bool :=
  if (heads 10).val = 0 then false else
    if (heads 13).val = 2 then (heads 12).val == 2 else !((heads 12).val == 2)

theorem encoded_nat_eq_nil (n : ℕ) : Computability.encodeNat n = [] ↔ n = 0 := by
  constructor
  · intro h
    have hv := congrArg KS.W19.bitsValue h
    simpa only [KS.W19.bitsValue_encodeNat, KS.W19.bitsValue] using hv
  · rintro rfl
    rfl

theorem chooseSign_integer (z : ℤ) (eps : Bool) :
    chooseSign (Computability.encodeNat z.natAbs) (decide (z < 0)) eps =
      decide ((if eps then z else -z) < 0) := by
  by_cases hz : z = 0
  · subst z
    cases eps <;> simp [chooseSign, encoded_nat_eq_nil]
  · have hn : z.natAbs ≠ 0 := by simpa using hz
    by_cases hneg : z < 0
    · cases eps <;> simp [chooseSign, encoded_nat_eq_nil, hn, hneg]
      omega
    · cases eps <;> simp [chooseSign, encoded_nat_eq_nil, hn, hneg]
      omega

@[simp] theorem signedRational_num_abs (eps : Bool) (q : ℚ) :
    (signedRational eps q).num.natAbs = q.num.natAbs := by
  cases eps <;> simp [signedRational]
@[simp] theorem signedRational_den (eps : Bool) (q : ℚ) :
    (signedRational eps q).den = q.den := by
  cases eps <;> simp [signedRational]
theorem chooseSign_rational (q : ℚ) (eps : Bool) :
    chooseSign (Computability.encodeNat q.num.natAbs) (decide (q.num < 0)) eps =
      decide ((signedRational eps q).num < 0) := by
  have h := chooseSign_integer q.num eps
  cases eps <;> simpa [signedRational] using h

theorem extend_on (r : Fin 13 → List Bool) (tape : List Bool) (i : Fin 13) :
    extend r tape (corePorts i) = r i := by
  change dite (i.val < 13) (fun h => r ⟨i.val,h⟩) _ = r i
  exact dite_eq_left i.isLt

theorem extend_off (r : Fin 13 → List Bool) (tape : List Bool) (j : Fin 14)
    (hj : ∀ i, j ≠ corePorts i) : extend r tape j = tape := by
  have hnot : ¬ j.val < 13 := by
    intro h
    exact hj ⟨j.val,h⟩ (Fin.ext rfl)
  simp only [extend, hnot, dite_false]

end KS.W16.RationalSignAction

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalSignClassifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W06.RationalSignClassifier

open KS.W06.RationalCompare
open KS.W04.CleanRationalCompare

def outputCode (q : ℚ) : List Bool :=
  if q < 0 then [false] else if q = 0 then [true] else []

def rawCode (sign : Bool) (num : List Bool) : List Bool :=
  if sign then [false] else if num = [] then [true] else []

def classifiedState (before : Fin 13 → List Bool) (sign : Bool) (num : List Bool) :
    Fin 13 → List Bool := fun j => if j = 9 then rawCode sign num else before j

theorem encodeNat_eq_nil (n : ℕ) : Computability.encodeNat n = [] ↔ n = 0 := by
  constructor
  · intro h
    have hv := congrArg KS.W19.bitsValue h
    simpa only [KS.W19.bitsValue_encodeNat, KS.W19.bitsValue] using hv
  · rintro rfl
    rfl

theorem rawCode_canonical (q : ℚ) :
    rawCode (decide (q.num < 0)) (Computability.encodeNat q.num.natAbs) = outputCode q := by
  have hs : q.num < 0 ↔ q < 0 := by
    simpa only [not_le] using not_congr
      (show 0 ≤ q.num ↔ 0 ≤ q from Rat.num_nonneg)
  have hz : Computability.encodeNat q.num.natAbs = [] ↔ q = 0 := by
    rw [encodeNat_eq_nil, Int.natAbs_eq_zero, Rat.num_eq_zero]
  simp [rawCode, outputCode, hs, hz]

def parsedState (q : ℚ) : Fin 13 → List Bool := SingleRationalParser.canonicalState q

def classifiedCanonical (q : ℚ) : Fin 13 → List Bool :=
  classifiedState (parsedState q) (decide (q.num < 0)) (Computability.encodeNat q.num.natAbs)

def outputState (q : ℚ) : Fin 13 → List Bool := fun j => if j = 9 then outputCode q else []

theorem cleared_classified (q : ℚ) :
    clearListState scratchPorts (classifiedCanonical q) = outputState q := by
  funext j
  rw [clearListState_apply]
  fin_cases j <;> simp [scratchPorts, outputState, classifiedCanonical, classifiedState]
  simpa using rawCode_canonical q

end KS.W06.RationalSignClassifier

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalSubtractProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W13.RationalSubtract

def firstPorts (n : ℕ) (hn : n ≤ 19) : Fin n ↪ Fin 19 :=
  ⟨fun i => ⟨i.val, lt_of_lt_of_le i.isLt hn⟩, fun _ _ h => Fin.ext (congrArg (fun j : Fin 19 => j.val) h)⟩

def extend {n : ℕ} (s : Fin n → List Bool) (spare : Fin 19 → List Bool) : Fin 19 → List Bool :=
  fun j => if h : j.val < n then s ⟨j.val,h⟩ else spare j

def registers (input num den sign tape savedR savedQ temp : List Bool) : Fin 19 → List Bool :=
  ![input,[],[],[],[],[],[],[],[],[],num,den,sign,tape,[],[],savedR,savedQ,temp]

def inputState (wire : List Bool) := registers wire [] [] [] [] [] [] []
def outputState (wire : List Bool) := registers [] wire [] [] [] [] [] []

def serializeTicks (q : ℚ) := 16 * ((Computability.encodeNat q.num.natAbs).length +
  (Computability.encodeNat q.den).length + 1)

end KS.W13.RationalSubtract

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_ComplexScalarCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W15.ComplexMachine
open KS.W15.WireProgram KS.W01

def negativeOneWire : List Bool := [true,true,false,true,true]

end KS.W15.ComplexMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_SparseScalarNodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.SparseScalarNodes
open KS.W15.ComplexMachine

def divPorts : Fin 15 ↪ Fin 28 := Fin.castLEEmb (by decide)

def coefficient (a b : ℚ) : ℚ := -(a+1)/(2*b)

end KS.W19.SparseScalarNodes

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_NaturalPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W23

inductive NaturalPolynomial where
  | constant : ℕ → NaturalPolynomial
  | variable : NaturalPolynomial
  | add : NaturalPolynomial → NaturalPolynomial → NaturalPolynomial
  | mul : NaturalPolynomial → NaturalPolynomial → NaturalPolynomial
  | power : NaturalPolynomial → ℕ → NaturalPolynomial
  deriving Repr

namespace NaturalPolynomial
instance instOfNat (value : ℕ) : OfNat NaturalPolynomial value := ⟨constant value⟩
instance instAdd : Add NaturalPolynomial := ⟨add⟩
instance instMul : Mul NaturalPolynomial := ⟨mul⟩
instance instPowNat : Pow NaturalPolynomial ℕ := ⟨power⟩

def eval : NaturalPolynomial → ℕ → ℕ
  | .constant c, _ => c
  | .variable, x => x
  | .add p q, x => p.eval x + q.eval x
  | .mul p q, x => p.eval x * q.eval x
  | .power p k, x => p.eval x ^ k

def degree : NaturalPolynomial → ℕ
  | .constant _ => 0
  | .variable => 1
  | .add p q => max p.degree q.degree
  | .mul p q => p.degree + q.degree
  | .power p k => p.degree * k

def coefficient (p : NaturalPolynomial) : ℕ := p.eval 1

@[simp] theorem eval_constant (c x : ℕ) : (constant c).eval x = c := rfl
@[simp] theorem eval_variable (x : ℕ) : variable.eval x = x := rfl
@[simp] theorem eval_add (p q : NaturalPolynomial) (x : ℕ) :
    (p + q).eval x = p.eval x + q.eval x := rfl
@[simp] theorem eval_mul (p q : NaturalPolynomial) (x : ℕ) :
    (p * q).eval x = p.eval x * q.eval x := rfl
@[simp] theorem eval_power (p : NaturalPolynomial) (k x : ℕ) :
    (p ^ k).eval x = p.eval x ^ k := rfl
@[simp] theorem eval_numeral (n x : ℕ) : (OfNat.ofNat n : NaturalPolynomial).eval x = n := rfl

theorem eval_le_coefficient_mul_pow (p : NaturalPolynomial) {x M : ℕ}
    (hM : 1 ≤ M) (hx : x ≤ M) : p.eval x ≤ p.coefficient * M ^ p.degree := by
  induction p with
  | constant c => simp [coefficient, eval, degree]
  | «variable» => simpa [coefficient, eval, degree] using hx
  | add p q hp hq =>
      have hp' := hp.trans (Nat.mul_le_mul_left p.coefficient
        (Nat.pow_le_pow_right hM (Nat.le_max_left p.degree q.degree)))
      have hq' := hq.trans (Nat.mul_le_mul_left q.coefficient
        (Nat.pow_le_pow_right hM (Nat.le_max_right p.degree q.degree)))
      simpa [coefficient, eval, degree, Nat.add_mul] using Nat.add_le_add hp' hq'
  | mul p q hp hq =>
      have h := Nat.mul_le_mul hp hq
      simpa [coefficient, eval, degree, pow_add, Nat.mul_assoc, Nat.mul_left_comm,
        Nat.mul_comm] using h
  | power p k hp =>
      have h := Nat.pow_le_pow_left hp k
      simpa [coefficient, eval, degree, mul_pow, pow_mul] using h

theorem eval_le_input_polynomial (p : NaturalPolynomial) (L : ℕ) :
    p.eval L ≤ p.coefficient * (L + 1) ^ p.degree :=
  p.eval_le_coefficient_mul_pow (Nat.succ_le_succ (Nat.zero_le L)) (Nat.le_succ L)

end NaturalPolynomial
end KS.W23

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SparseCoefficientStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.SparseCoefficientStage
open KS.W15.ComplexMachine

def ports : Fin 28 ↪ Fin 35 :=
  ⟨![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,19,20,21,22,24,25,17,23,27,28,26,18], by decide⟩

def cleanupPorts : List (Fin 35) := [19,20,21,22,24,25,27,33]

end KS.W19.SparseCoefficientStage

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_WireAppend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.WireAppend

def moveAfter {k : ℕ} (source target : Fin k) (before : Fin k → List Bool) : Fin k → List Bool :=
  fun j => if j=source then [] else if j=target then (before source).reverse ++ before target else before j

def after {k : ℕ} (source target : Fin k) (before : Fin k → List Bool) : Fin k → List Bool :=
  fun j => if j = source then [] else if j = target then before source ++ before target else before j

end KS.W07.WireAppend

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurReadStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurReadStage

def readPorts : Fin 8 ↪ Fin 32 := ⟨![0,1,2,3,4,5,6,31], by decide⟩

def WorkClear (before : Fin 32 → List Bool) : Prop := ∀ j, j.val < 19 → before j = []

def readPrepared (before : Fin 32 → List Bool) (col row dim : List Bool) : Fin 32 → List Bool :=
  Function.update (Function.update (Function.update before 2 dim) 1 row) 0 col

def rowSource (nonzero : Bool) : Fin 32 := if nonzero then 27 else 29
def colSource (nonzero : Bool) : Fin 32 := if nonzero then 28 else 29

def prepareTicks (before : Fin 32 → List Bool) (row col : Bool) : ℕ :=
  (2*(before 26).length+2) +
    ((2*(before (rowSource row)).length+2) + (2*(before (colSource col)).length+2))

def destination (k : Fin 4) : Fin 32 := ⟨19+k.val, by omega⟩

theorem destination_ne_core (k : Fin 4) (j : Fin 32) (hj : j.val < 19) :
    destination k ≠ j := by
  intro h
  have he := congrArg Fin.val h
  change 19 + k.val = j.val at he
  omega

end KS.W07.SchurReadStage

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_TerminalReadStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.TerminalReadStage
open KS.W07

def ports : Fin 32 ↪ Fin 35 :=
  ⟨![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,30,33,29,27,31], by decide⟩
def sourceRow (diagonal : Bool) : Fin 35 := if diagonal then 30 else 29
def destination (diagonal : Bool) : Fin 35 := if diagonal then 19 else 20
def slot (diagonal : Bool) : Fin 4 := if diagonal then 0 else 1

def WorkClear (s : Fin 35 → List Bool) : Prop := ∀ j, j.val < 19 → s j = []

end KS.W19.TerminalReadStage

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_FramedArrayPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W11.FramedArrayRewrite

def «stacks» (src replacement «prefix» scratch index : List Bool) : Fin 5 → List Bool :=
  fun j => if j = 0 then src else if j = 1 then replacement else if j = 2 then «prefix»
    else if j = 3 then scratch else index

end KS.W11.FramedArrayRewrite

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_ZeroArrayConstructor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W11.ZeroArrayConstructor

def «stacks» (count accum output : List Bool) : Fin 3 → List Bool :=
  fun j => if j = 0 then count else if j = 1 then accum else output

end KS.W11.ZeroArrayConstructor

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_TerminalZeroVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.TerminalZeroVector

def copyPorts : Fin 3 ↪ Fin 35 := ⟨![26,0,16], by decide⟩
def unaryPorts : Fin 3 ↪ Fin 35 := ⟨![0,1,2], by decide⟩
def zeroPorts : Fin 3 ↪ Fin 35 := ⟨![1,0,23], by decide⟩

def ticks (n : ℕ) : ℕ := 28*n + 6*(Computability.encodeNat n).length + 6

end KS.W19.TerminalZeroVector

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_TerminalVectorReplace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.TerminalVectorReplace
open Matrix

def ports : Fin 5 ↪ Fin 35 := ⟨![23,0,1,2,3], by decide⟩

end KS.W19.TerminalVectorReplace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_TerminalWitnessTapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.TerminalVectorReplace

theorem ofFn_set {n : ℕ} (f : Fin n → List Bool) (i : Fin n) (a : List Bool) :
    (List.ofFn f).set i.val a = List.ofFn (Function.update f i a) := by
  apply List.ext_getElem
  · simp
  · intro j hj hk
    have hji : j < n := by simpa using hk
    simp only [List.getElem_set, List.getElem_ofFn]
    by_cases he : i.val = j
    · have hef : (⟨j,hji⟩ : Fin n) = i := Fin.ext he.symm
      simp only [he,↓reduceIte]
      change a = Function.update f i a (⟨j,hji⟩ : Fin n)
      rw [hef,Function.update_self]
    · have hef : (⟨j,hji⟩ : Fin n) ≠ i := by
        intro h
        exact he (congrArg Fin.val h).symm
      simp [he,Function.update_of_ne hef]

def sparseVector {n : ℕ} (j : Fin (n+1)) (c : ℚ) : Fin (n+1) → ℚ :=
  Pi.single 0 c + Pi.single j 1

end KS.W19.TerminalVectorReplace

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_TerminalSparseAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.TerminalSparseAssembly
open KS.W19.TerminalVectorReplace

def unaryPorts : Fin 3 ↪ Fin 35 := ⟨![30,3,1], by decide⟩

def framePorts : Fin 3 ↪ Fin 35 := ⟨![0,28,1], by decide⟩

end KS.W19.TerminalSparseAssembly

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_UniformElimination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

inductive PivotHistory : ℕ → ℕ → Type
  | nil (n : ℕ) : PivotHistory n n
  | push {n N : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
      (rest : PivotHistory (n+1) N) : PivotHistory n N

namespace PivotHistory

def depth : {n N : ℕ} → PivotHistory n N → ℕ
  | _, _, .nil _ => 0
  | _, _, .push _ rest => depth rest + 1

theorem dimension_depth {n N : ℕ} (h : PivotHistory n N) : n + depth h = N := by
  induction h with
  | nil n => simp [depth]
  | @push n N M rest ih => simpa [depth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih

end PivotHistory
end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_SavedPivotPacketMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W08.SavedPivotPacket

def workspace (saved dim row : List Bool) : Fin 5 → List Bool := ![saved, dim, row, [], []]
def dimPorts : Fin 3 ↪ Fin 5 := ⟨![3, 1, 4], by decide⟩
def packetPorts : Fin 3 ↪ Fin 5 := ⟨![1, 2, 4], by decide⟩

def outerPorts : Fin 3 ↪ Fin 5 := ⟨![0, 2, 3], by decide⟩
def innerPorts : Fin 3 ↪ Fin 5 := ⟨![2, 1, 3], by decide⟩

end KS.W08.SavedPivotPacket

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotHistoryMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.FixedPSD

def state (saved parentDim parentTape childDim childTape : List Bool) : Fin 35 → List Bool :=
  fun j => if j = 32 then saved else if j = 26 then parentDim else if j = 31 then parentTape
    else if j = 30 then childDim else if j = 23 then childTape else []

def savedPorts : Fin 5 ↪ Fin 35 := ⟨![32, 26, 31, 33, 34], by decide⟩

end KS.W17.FixedPSD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_StoredWitnessLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.StoredWitnessLift
open KS.W07
open KS.W12.RowDot

def padPorts : Fin 3 ↪ Fin 30 := ⟨![29, 20, 26], by decide⟩
def headPorts : Fin 29 ↪ Fin 30 := Fin.castLEEmb (by decide)
def copyPorts : Fin 3 ↪ Fin 30 := ⟨![29, 17, 26], by decide⟩
def framePorts : Fin 3 ↪ Fin 30 := ⟨![4, 10, 26], by decide⟩

end KS.W12.StoredWitnessLift

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_PivotWitnessMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W07

def witnessPorts : Fin 30 ↪ Fin 35 :=
  ⟨![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,31,20,21,26,29,24,25,22,27,28,23],
    by decide⟩

end KS.W17.FixedPSD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_Pivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Matrix

namespace KS.W07

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

def scalarPivot (a : K) : Matrix Unit Unit K := fun _ _ => a

@[implicit_reducible]
def scalarPivotInvertible {a : K} (ha : a ≠ 0) : Invertible (scalarPivot a) where
  invOf := scalarPivot a⁻¹
  invOf_mul_self := by
    ext i j
    cases i; cases j
    simp [scalarPivot, Matrix.mul_apply, ha]
  mul_invOf_self := by
    ext i j
    cases i; cases j
    simp [scalarPivot, Matrix.mul_apply, ha]

theorem scalarPivot_inv {a : K} (ha : a ≠ 0) :
    (scalarPivot a)⁻¹ = scalarPivot a⁻¹ := by
  let := scalarPivotInvertible ha
  exact (Matrix.invOf_eq_nonsing_inv (scalarPivot a)).symm

end KS.W07

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_DenseElimination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

open Matrix
open KS.W07

theorem map_materialized {n m : ℕ} (o : Option (Vector ℚ n))
    (f : (Fin n → ℚ) → (Fin m → ℚ)) :
    (o.map (fun v => Vector.ofFn (f (decodeRatVector v)))).map decodeRatVector =
      (o.map decodeRatVector).map f := by
  cases o <;> simp

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_NestedSchur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30

theorem nested_schur_invOf {ι κ ρ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype ρ] [DecidableEq ρ]
    (A : Matrix ι ι ℚ) (B : Matrix ι κ ℚ) (C : Matrix κ ι ℚ) (D : Matrix κ κ ℚ)
    (F : Matrix ι ρ ℚ) (G : Matrix κ ρ ℚ)
    (H : Matrix ρ ι ℚ) (I : Matrix ρ κ ℚ) (J : Matrix ρ ρ ℚ)
    [Invertible A] [Invertible (D - C * ⅟A * B)]
    [Invertible (Matrix.fromBlocks A B C D)] :
    J - Matrix.fromCols H I * ⅟(Matrix.fromBlocks A B C D) * Matrix.fromRows F G =
      (J - H * ⅟A * F) -
        (I - H * ⅟A * B) * ⅟(D - C * ⅟A * B) * (G - C * ⅟A * F) := by
  rw [Matrix.invOf_fromBlocks₁₁_eq, Matrix.fromCols_mul_fromBlocks,
    Matrix.fromCols_mul_fromRows]
  generalize ⅟(D - C * ⅟A * B) = R
  generalize ⅟A = P
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  abel

theorem nested_schur {ι κ ρ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype ρ] [DecidableEq ρ]
    (A : Matrix ι ι ℚ) (B : Matrix ι κ ℚ) (C : Matrix κ ι ℚ) (D : Matrix κ κ ℚ)
    (F : Matrix ι ρ ℚ) (G : Matrix κ ρ ℚ)
    (H : Matrix ρ ι ℚ) (I : Matrix ρ κ ℚ) (J : Matrix ρ ρ ℚ)
    (hA : A.det ≠ 0) (hS : (D - C * A⁻¹ * B).det ≠ 0) :
    J - Matrix.fromCols H I * (Matrix.fromBlocks A B C D)⁻¹ * Matrix.fromRows F G =
      (J - H * A⁻¹ * F) -
        (I - H * A⁻¹ * B) * (D - C * A⁻¹ * B)⁻¹ * (G - C * A⁻¹ * F) := by
  let : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hA)
  let : Invertible (D - C * ⅟A * B) := Matrix.invertibleOfIsUnitDet _ (by
    simpa only [Matrix.invOf_eq_nonsing_inv] using (isUnit_iff_ne_zero.mpr hS))
  let : Invertible (Matrix.fromBlocks A B C D) := Matrix.fromBlocks₁₁Invertible A B C D
  simpa only [Matrix.invOf_eq_nonsing_inv] using nested_schur_invOf A B C D F G H I J

end KS.W30

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_DeterminantBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30

open Matrix

theorem factorial_le_two_pow_sq (n : ℕ) : n.factorial ≤ 2 ^ (n * n) := by
  calc
    n.factorial ≤ n ^ n := Nat.factorial_le_pow n
    _ ≤ (2 ^ n) ^ n := Nat.pow_le_pow_left (Nat.le_of_lt n.lt_two_pow_self) n
    _ = 2 ^ (n * n) := (pow_mul 2 n n).symm

theorem abs_det_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (B : ℕ)
    (hA : ∀ i j, |A i j| ≤ (B : ℤ)) :
    |A.det| ≤ (n.factorial : ℤ) * (B : ℤ) ^ n := by
  simpa only [AbsoluteValue.abs_apply, Fintype.card_fin, nsmul_eq_mul] using
    (Matrix.det_le (abv := AbsoluteValue.abs) hA)

theorem natAbs_det_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (B : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ B) :
    A.det.natAbs ≤ n.factorial * B ^ n := by
  have hh : ∀ i j, |A i j| ≤ (B : ℤ) := by
    intro i j
    rw [← Int.natCast_natAbs]
    exact_mod_cast hA i j
  have hd := abs_det_le A B hh
  rw [← Int.natCast_natAbs] at hd
  exact_mod_cast hd

theorem natAbs_det_le_two_pow {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (b : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ b) :
    A.det.natAbs ≤ 2 ^ (n * n + b * n) := by
  calc
    A.det.natAbs ≤ n.factorial * (2 ^ b) ^ n := natAbs_det_le A (2 ^ b) hA
    _ ≤ 2 ^ (n * n) * (2 ^ b) ^ n :=
      Nat.mul_le_mul_right _ (factorial_le_two_pow_sq n)
    _ = 2 ^ (n * n + b * n) := by rw [← pow_mul, ← pow_add]

end KS.W30

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_InverseHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30

def inverseBitBound (n b : ℕ) : ℕ :=
  b * (n * n) + (n * n + (b * (n * n) + b) * n) + 1

end KS.W30

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30

open scoped Rat

theorem schur_scalar_det_ratio {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (B : Matrix ι Unit ℚ) (C : Matrix Unit ι ℚ)
    (D : Matrix Unit Unit ℚ) (hdet : A.det ≠ 0) :
    (D - C * A⁻¹ * B) () () = (Matrix.fromBlocks A B C D).det / A.det := by
  let : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hdet)
  have h := Matrix.det_fromBlocks₁₁ A B C D
  rw [Matrix.invOf_eq_nonsing_inv] at h
  rw [Matrix.det_unique (D - C * A⁻¹ * B)] at h
  apply (eq_div_iff hdet).mpr
  simpa [mul_comm] using h.symm

theorem minor_natAbs_le_two_pow {n k : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (f g : Fin k → Fin n) (b : ℕ) (hM : ∀ i j, (M i j).natAbs ≤ 2 ^ b)
    (hk : k ≤ n) :
    (M.submatrix f g).det.natAbs ≤ 2 ^ (n * n + b * n) := by
  apply le_trans (natAbs_det_le_two_pow (M.submatrix f g) b (fun i j => hM _ _))
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  exact Nat.add_le_add (Nat.mul_le_mul hk hk) (Nat.mul_le_mul_left b hk)

theorem scaled_minor_ratio_parts_size_le {n k l : ℕ}
    (M : Matrix (Fin n) (Fin n) ℤ) (D b d : ℕ) (hD : D ≠ 0) (hDb : D ≤ 2 ^ d)
    (f g : Fin k → Fin n) (u v : Fin l → Fin n)
    (hM : ∀ i j, (M i j).natAbs ≤ 2 ^ b) (hk : k ≤ n) (hl : l ≤ n)
    (hden : (M.submatrix u v).det ≠ 0) :
    let q := (M.submatrix f g).det /. ((D : ℤ) * (M.submatrix u v).det)
    Nat.size q.num.natAbs ≤ d + (n * n + b * n) + 1 ∧
      Nat.size q.den ≤ d + (n * n + b * n) + 1 := by
  let e := n * n + b * n
  have hn := minor_natAbs_le_two_pow M f g b hM hk
  have hd : ((D : ℤ) * (M.submatrix u v).det).natAbs ≤ 2 ^ (d + e) := by
    rw [Int.natAbs_mul, Int.natAbs_natCast, pow_add]
    exact Nat.mul_le_mul hDb (minor_natAbs_le_two_pow M u v b hM hl)
  have hh : ((D : ℤ) * (M.submatrix u v).det) ≠ 0 :=
    mul_ne_zero (Int.natCast_ne_zero.mpr hD) hden
  have hp : 2 ^ (d + e) < 2 ^ (d + e + 1) := by
    exact Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self _)
  have hn' : (M.submatrix f g).det.natAbs < 2 ^ (d + e + 1) := by
    apply lt_of_le_of_lt hn
    exact lt_of_le_of_lt
      (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_left e d)) hp
  exact ⟨divInt_num_size_le _ _ hh _ hn',
    divInt_den_size_le _ _ hh _ (lt_of_le_of_lt hd hp)⟩

theorem cleared_minor_ratio_parts_size_le {n k l : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (b : ℕ)
    (hnum : ∀ i j, (A i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (A i j).den ≤ 2 ^ b)
    (f g : Fin k → Fin n) (u v : Fin l → Fin n) (hk : k ≤ n) (hl : l ≤ n)
    (hdet : (A.num.submatrix u v).det ≠ 0) :
    let q := (A.num.submatrix f g).det /.
      ((A.den : ℤ) * (A.num.submatrix u v).det)
    Nat.size q.num.natAbs ≤ inverseBitBound n b ∧
      Nat.size q.den ≤ inverseBitBound n b := by
  exact scaled_minor_ratio_parts_size_le A.num A.den (b * (n * n) + b) (b * (n * n))
    A.den_ne_zero (matrix_den_le_two_pow A b hden) f g u v
    (fun i j => cleared_num_le_two_pow A b hnum hden i j) hk hl hdet

theorem schur_smul {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℚ) (B : Matrix ι κ ℚ) (C : Matrix κ ι ℚ) (D : Matrix κ κ ℚ)
    (c : ℚ) (hc : c ≠ 0) (hA : A.det ≠ 0) :
    c • D - (c • C) * (c • A)⁻¹ * (c • B) = c • (D - C * A⁻¹ * B) := by
  let : Invertible c := invertibleOfNonzero hc
  rw [Matrix.inv_smul A c (isUnit_iff_ne_zero.mpr hA)]
  simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, invOf_eq_inv, hc, smul_sub]

end KS.W30

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W07

open Matrix

def appendIndexEquiv (k : ℕ) : Fin k ⊕ Unit ≃ Fin (k + 1) where
  toFun := Sum.elim Fin.castSucc (fun _ => Fin.last k)
  invFun := Fin.lastCases (Sum.inr ()) Sum.inl
  left_inv := by
    intro i
    cases i with
    | inl i => simp
    | inr i => cases i; simp
  right_inv := by
    intro i
    induction i using Fin.lastCases <;> simp

noncomputable def selectedSchur {N : ℕ} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (M : Matrix (Fin N) (Fin N) ℚ) (p : ι → Fin N) (r : κ → Fin N) :
    Matrix κ κ ℚ :=
  M.submatrix r r - M.submatrix r p * (M.submatrix p p)⁻¹ * M.submatrix p r

theorem selectedSchur_reindex_selected {N : ℕ} {ι κ ρ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype ρ]
    (M : Matrix (Fin N) (Fin N) ℚ) (p : ι → Fin N) (r : ρ → Fin N)
    (e : κ ≃ ι) :
    selectedSchur M (p ∘ e) r = selectedSchur M p r := by
  change M.submatrix r r -
      (M.submatrix r p).submatrix id e * ((M.submatrix p p).submatrix e e)⁻¹ *
        (M.submatrix p r).submatrix e id = _
  simp only [Matrix.inv_submatrix_equiv, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_id_id, selectedSchur]

theorem selectedSchur_restrict {N k t u : ℕ}
    (M : Matrix (Fin N) (Fin N) ℚ) (p : Fin k → Fin N) (r : Fin t → Fin N)
    (f : Fin u → Fin t) :
    selectedSchur M p (r ∘ f) = (selectedSchur M p r).submatrix f f := by
  ext i j
  simp [selectedSchur, Matrix.mul_apply, Function.comp_def]

theorem originalBorder_reindex {N k : ℕ}
    (M : Matrix (Fin N) (Fin N) ℚ) (p : Fin k → Fin N) (i j : Fin N) :
    (M.submatrix (Fin.snoc p i) (Fin.snoc p j)).submatrix
        (appendIndexEquiv k) (appendIndexEquiv k) =
      Matrix.fromBlocks (M.submatrix p p)
        (fun x _ => M (p x) j : Matrix (Fin k) Unit ℚ)
        (fun _ y => M i (p y) : Matrix Unit (Fin k) ℚ)
        (fun _ _ => M i j : Matrix Unit Unit ℚ) := by
  ext x y
  cases x <;> cases y <;> simp [appendIndexEquiv, Matrix.submatrix] <;> rfl

theorem selectedSchur_entry_minor_ratio {N k t : ℕ}
    (M : Matrix (Fin N) (Fin N) ℚ) (p : Fin k → Fin N) (r : Fin t → Fin N)
    (hp : (M.submatrix p p).det ≠ 0) (i j : Fin t) :
    selectedSchur M p r i j =
      (M.submatrix (Fin.snoc p (r i)) (Fin.snoc p (r j))).det /
        (M.submatrix p p).det := by
  have h := KS.W30.schur_scalar_det_ratio (M.submatrix p p)
    (fun x _ => M (p x) (r j)) (fun _ y => M (r i) (p y))
    (fun _ _ => M (r i) (r j)) hp
  have hd := congrArg Matrix.det (originalBorder_reindex M p (r i) (r j))
  simp only [Matrix.det_submatrix_equiv_self] at hd
  rw [← hd] at h
  exact h

theorem selectedSchur_new_det_ne_zero {N k t : ℕ}
    (M : Matrix (Fin N) (Fin N) ℚ) (p : Fin k → Fin N)
    (r : Fin (t + 1) → Fin N) (hp : (M.submatrix p p).det ≠ 0)
    (ha : selectedSchur M p r 0 0 ≠ 0) :
    (M.submatrix (Fin.snoc p (r 0)) (Fin.snoc p (r 0))).det ≠ 0 := by
  intro hz
  apply ha
  rw [selectedSchur_entry_minor_ratio M p r hp 0 0, hz, zero_div]

end KS.W07

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotHistoryBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07

open Matrix

theorem selectedSchur_smul {N k t : ℕ}
    (M : Matrix (Fin N) (Fin N) ℚ) (p : Fin k → Fin N) (r : Fin t → Fin N)
    (c : ℚ) (hc : c ≠ 0) (hp : (M.submatrix p p).det ≠ 0) :
    selectedSchur (c • M) p r = c • selectedSchur M p r := by
  exact KS.W30.schur_smul (M.submatrix p p) (M.submatrix p r)
    (M.submatrix r p) (M.submatrix r r) c hc hp

theorem original_num_cast {dimension : ℕ} (M : Matrix (Fin dimension) (Fin dimension) ℚ) :
    M.num.map (fun z : ℤ => (z : ℚ)) = (M.den : ℚ) • M := by
  ext i j
  exact KS.W30.cleared_matrix_entry M i j

theorem original_num_selected_det_ne_zero {N k : ℕ}
    (M : Matrix (Fin N) (Fin N) ℚ) (p : Fin k → Fin N)
    (hp : (M.submatrix p p).det ≠ 0) : (M.num.submatrix p p).det ≠ 0 := by
  have heq : (M.num.submatrix p p).map (fun z : ℤ => (z : ℚ)) =
      (M.den : ℚ) • M.submatrix p p := by
    ext i j
    exact KS.W30.cleared_matrix_entry M (p i) (p j)
  have hd : ((M.num.submatrix p p).det : ℚ) =
      (M.den : ℚ) ^ k * (M.submatrix p p).det := by
    rw [Int.cast_det, heq, Matrix.det_smul, Fintype.card_fin]
  have hn : (M.den : ℚ) ^ k * (M.submatrix p p).det ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr M.den_ne_zero)) hp
  intro hz
  apply hn
  rw [← hd, hz, Int.cast_zero]

theorem selectedSchur_entry_cleared_ratio {N k t : ℕ}
    (M : Matrix (Fin N) (Fin N) ℚ) (p : Fin k → Fin N) (r : Fin t → Fin N)
    (hp : (M.submatrix p p).det ≠ 0) (i j : Fin t) :
    selectedSchur M p r i j =
      Rat.divInt (M.num.submatrix (Fin.snoc p (r i)) (Fin.snoc p (r j))).det
        ((M.den : ℤ) * (M.num.submatrix p p).det) := by
  let Z := M.num.map (fun z : ℤ => (z : ℚ))
  have hz : (M.num.submatrix p p).det ≠ 0 := original_num_selected_det_ne_zero M p hp
  have hzp : (Z.submatrix p p).det ≠ 0 := by
    change ((M.num.submatrix p p).map (fun z : ℤ => (z : ℚ))).det ≠ 0
    rw [← Int.cast_det]
    exact_mod_cast hz
  have hs : selectedSchur Z p r = (M.den : ℚ) • selectedSchur M p r := by
    rw [show Z = (M.den : ℚ) • M from original_num_cast M]
    exact selectedSchur_smul M p r _ (Nat.cast_ne_zero.mpr M.den_ne_zero) hp
  have he := congrFun (congrFun hs i) j
  rw [selectedSchur_entry_minor_ratio Z p r hzp i j] at he
  have hd : (Z.submatrix p p).det = ((M.num.submatrix p p).det : ℚ) := by
    exact (Int.cast_det (M.num.submatrix p p)).symm
  have hb : (Z.submatrix (Fin.snoc p (r i)) (Fin.snoc p (r j))).det =
      ((M.num.submatrix (Fin.snoc p (r i)) (Fin.snoc p (r j))).det : ℚ) := by
    exact (Int.cast_det _).symm
  rw [hd, hb] at he
  have hq : ((M.num.submatrix p p).det : ℚ) ≠ 0 := by exact_mod_cast hz
  have hc : (M.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr M.den_ne_zero
  have hcross := (div_eq_iff hq).mp he
  rw [Rat.divInt_eq_div, Int.cast_mul, Int.cast_natCast]
  apply (eq_div_iff (mul_ne_zero hc hq)).mpr
  simpa only [Matrix.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using hcross.symm

end KS.W07

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_CommonDenominatorLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30

def prependLinear {n : ℕ} (c y : Fin n → ℚ) : Fin (n + 1) → ℚ :=
  Fin.cons (∑ i, c i * y i) y

theorem natAbs_sum_le {n : ℕ} (z : Fin n → ℤ) :
    (∑ i, z i).natAbs ≤ ∑ i, (z i).natAbs := by
  have h := Finset.abs_sum_le_sum_abs z Finset.univ
  have hcast : ((∑ i, z i).natAbs : ℤ) ≤ ((∑ i, (z i).natAbs : ℕ) : ℤ) := by
    simpa only [Nat.cast_sum, Int.natCast_natAbs] using h
  exact_mod_cast hcast

theorem prependLinear_common_representation {n : ℕ} (c y : Fin n → ℚ)
    (C D : ℕ) (hC : C ≠ 0) (P Z : Fin n → ℤ)
    (hc : ∀ i, c i = (P i : ℚ) / C) (hy : ∀ i, y i = (Z i : ℚ) / D) :
    let Z' : Fin (n + 1) → ℤ := Fin.cons (∑ i, P i * Z i) (fun i => (C : ℤ) * Z i)
    ∀ i, prependLinear c y i = (Z' i : ℚ) / (D * C : ℕ) := by
  dsimp only
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change (∑ i, c i * y i) = ((∑ i, P i * Z i : ℤ) : ℚ) / (D * C : ℕ)
    simp only [Int.cast_sum]
    rw [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [hc, hy, div_mul_div_comm]
    simp only [Int.cast_mul, Nat.cast_mul, mul_comm (D : ℚ) (C : ℚ), div_eq_mul_inv]
  · change y j = (((C : ℤ) * Z j : ℤ) : ℚ) / (D * C : ℕ)
    rw [hy]
    symm
    simpa only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul,
      mul_comm (D : ℚ) (C : ℚ)] using
      (mul_div_mul_left (Z j : ℚ) (D : ℚ) (Nat.cast_ne_zero.mpr hC : (C : ℚ) ≠ 0))

theorem prependLinear_common_height {n : ℕ} (c y : Fin n → ℚ) (H E : ℕ)
    (hcnum : ∀ i, (c i).num.natAbs ≤ 2 ^ H)
    (hcden : ∀ i, (c i).den ≤ 2 ^ H)
    (D : ℕ) (hD : 0 < D) (hDb : D ≤ 2 ^ E) (Z : Fin n → ℤ)
    (hy : ∀ i, y i = (Z i : ℚ) / D) (hZ : ∀ i, (Z i).natAbs ≤ 2 ^ E) :
    let E' := E + (n + 1) * H + n + 1
    ∃ D' : ℕ, 0 < D' ∧ D' ≤ 2 ^ E' ∧
      ∃ Z' : Fin (n + 1) → ℤ,
        (∀ i, prependLinear c y i = (Z' i : ℚ) / D') ∧
        ∀ i, (Z' i).natAbs ≤ 2 ^ E' := by
  let R : Matrix (Fin 1) (Fin n) ℚ := fun _ i => c i
  let C := R.den
  let P : Fin n → ℤ := fun i => R.num 0 i
  let E' := E + (n + 1) * H + n + 1
  have hC : 0 < C := Nat.pos_of_ne_zero R.den_ne_zero
  have hCb : C ≤ 2 ^ (H * n) := by
    simpa [C] using matrix_den_le_two_pow R H (fun _ i => hcden i)
  have hPb : ∀ i, (P i).natAbs ≤ 2 ^ (H * n + H) := by
    intro i
    simpa [P] using cleared_num_le_two_pow R H
      (fun _ i => hcnum i) (fun _ i => hcden i) 0 i
  have hc : ∀ i, c i = (P i : ℚ) / C := by
    intro i
    exact (Matrix.num_div_den R 0 i).symm
  have hE : E' = E + H * n + H + n + 1 := by dsimp [E'] <;> ring
  have hDen : D * C ≤ 2 ^ E' := by
    calc
      D * C ≤ 2 ^ E * 2 ^ (H * n) := Nat.mul_le_mul hDb hCb
      _ = 2 ^ (E + H * n) := (pow_add 2 _ _).symm
      _ ≤ 2 ^ E' := Nat.pow_le_pow_right (by decide : 0 < 2) (by rw [hE]; omega)
  have hProd : ∀ i, (P i * Z i).natAbs ≤ 2 ^ (H * n + H + E) := by
    intro i
    rw [Int.natAbs_mul, pow_add]
    exact Nat.mul_le_mul (hPb i) (hZ i)
  have hHead : (∑ i, P i * Z i).natAbs ≤ 2 ^ E' := by
    calc
      (∑ i, P i * Z i).natAbs ≤ ∑ i, (P i * Z i).natAbs := natAbs_sum_le _
      _ ≤ ∑ _i : Fin n, 2 ^ (H * n + H + E) := Finset.sum_le_sum (fun i _ => hProd i)
      _ = n * 2 ^ (H * n + H + E) := by simp
      _ ≤ 2 ^ n * 2 ^ (H * n + H + E) :=
        Nat.mul_le_mul_right _ (Nat.le_of_lt n.lt_two_pow_self)
      _ = 2 ^ (n + (H * n + H + E)) := (pow_add 2 _ _).symm
      _ ≤ 2 ^ E' := Nat.pow_le_pow_right (by decide : 0 < 2) (by rw [hE]; omega)
  have hTail : ∀ i, ((C : ℤ) * Z i).natAbs ≤ 2 ^ E' := by
    intro i
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    calc
      C * (Z i).natAbs ≤ 2 ^ (H * n) * 2 ^ E := Nat.mul_le_mul hCb (hZ i)
      _ = 2 ^ (H * n + E) := (pow_add 2 _ _).symm
      _ ≤ 2 ^ E' := Nat.pow_le_pow_right (by decide : 0 < 2) (by rw [hE]; omega)
  refine ⟨D * C, Nat.mul_pos hD hC, hDen,
    Fin.cons (∑ i, P i * Z i) (fun i => (C : ℤ) * Z i), ?_, ?_⟩
  · exact prependLinear_common_representation c y C D (Nat.ne_of_gt hC) P Z hc hy
  · intro i
    exact Fin.cases hHead hTail i

end KS.W30

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_TerminalWitnessBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30

theorem zeroPivot_coefficient_parts_bound (q r : ℚ) (H : ℕ)
    (hqnum : q.num.natAbs ≤ 2 ^ H) (hqden : q.den ≤ 2 ^ H)
    (hrnum : r.num.natAbs ≤ 2 ^ H) (hrden : r.den ≤ 2 ^ H) :
    (-(q + 1) / (2 * r)).num.natAbs ≤ 2 ^ (3 * H + 3) ∧
      (-(q + 1) / (2 * r)).den ≤ 2 ^ (3 * H + 3) := by
  have ha := add_parts_le_two_pow q 1 H 0 hqnum hqden (by norm_num) (by norm_num)
  have han : (-(q + 1)).num.natAbs ≤ 2 ^ (H + 1) := by
    simpa only [Rat.neg_num, Int.natAbs_neg, Nat.add_zero] using ha.1
  have had : (-(q + 1)).den ≤ 2 ^ (H + 1) := by
    rw [Rat.neg_den]
    have had' : (q + 1).den ≤ 2 ^ H := by simpa only [Nat.add_zero] using ha.2
    exact had'.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_succ H))
  have hm := mul_parts_le_two_pow 2 r 1 H (by norm_num) (by norm_num) hrnum hrden
  have hd := div_parts_le_two_pow (-(q + 1)) (2 * r) (H + 1) (1 + H)
    han had hm.1 hm.2
  have hp : 2 ^ (H + 1 + (1 + H)) ≤ 2 ^ (3 * H + 3) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  exact ⟨hd.1.trans hp, hd.2.trans hp⟩

theorem sparse_pair_common_height {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (z : ℚ) (E : ℕ) (hznum : z.num.natAbs ≤ 2 ^ E) (hzden : z.den ≤ 2 ^ E) :
    ∃ D : ℕ, 0 < D ∧ D ≤ 2 ^ E ∧ ∃ Z : Fin n → ℤ,
      (∀ k, (Pi.single i z + Pi.single j 1 : Fin n → ℚ) k = (Z k : ℚ) / D) ∧
      ∀ k, (Z k).natAbs ≤ 2 ^ E := by
  let Z : Fin n → ℤ := Pi.single i z.num + Pi.single j (z.den : ℤ)
  refine ⟨z.den, z.den_pos, hzden, Z, ?_, ?_⟩
  · intro k
    by_cases hki : k = i
    · subst k
      simp [Z, hij, Rat.num_div_den]
    · by_cases hkj : k = j
      · subst k
        simp [Z, Ne.symm hij, z.den_nz]
      · simp [Z, hki, hkj]
  · intro k
    by_cases hki : k = i
    · subst k
      simpa [Z, Pi.single_apply, hij, Ne.symm hij] using hznum
    · by_cases hkj : k = j
      · subst k
        simpa [Z, Pi.single_apply, hij, Ne.symm hij] using hzden
      · simp [Z, hki, hkj]

theorem zeroPivot_pair_common_height {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (q r : ℚ) (H : ℕ)
    (hqnum : q.num.natAbs ≤ 2 ^ H) (hqden : q.den ≤ 2 ^ H)
    (hrnum : r.num.natAbs ≤ 2 ^ H) (hrden : r.den ≤ 2 ^ H) :
    ∃ D : ℕ, 0 < D ∧ D ≤ 2 ^ (3 * H + 3) ∧ ∃ Z : Fin n → ℤ,
      (∀ k, (Pi.single i (-(q + 1) / (2 * r)) + Pi.single j 1 : Fin n → ℚ) k =
        (Z k : ℚ) / D) ∧
      ∀ k, (Z k).natAbs ≤ 2 ^ (3 * H + 3) := by
  have h := zeroPivot_coefficient_parts_bound q r H hqnum hqden hrnum hrden
  exact sparse_pair_common_height i j hij _ _ h.1 h.2

end KS.W30

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_EliminationWitnessHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

open KS.W07

def CommonHeight {n : ℕ} (y : Fin n → ℚ) (E : ℕ) : Prop :=
  ∃ D : ℕ, 0 < D ∧ D ≤ 2 ^ E ∧ ∃ Z : Fin n → ℤ,
    (∀ i, y i = (Z i : ℚ) / D) ∧ ∀ i, (Z i).natAbs ≤ 2 ^ E

theorem CommonHeight.mono {n E F : ℕ} {y : Fin n → ℚ}
    (h : CommonHeight y E) (hEF : E ≤ F) : CommonHeight y F := by
  obtain ⟨D, hD, hDb, Z, hy, hZ⟩ := h
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hEF
  exact ⟨D, hD, hDb.trans hp, Z, hy, fun i => (hZ i).trans hp⟩

theorem CommonHeight.parts_bound {n E : ℕ} {y : Fin n → ℚ}
    (h : CommonHeight y E) (i : Fin n) :
    (y i).num.natAbs ≤ 2 ^ E ∧ (y i).den ≤ 2 ^ E := by
  obtain ⟨D, hD, hDb, Z, hy, hZ⟩ := h
  have hd : (D : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Nat.ne_of_gt hD)
  have he : y i = Rat.divInt (Z i) (D : ℤ) := by
    rw [Rat.divInt_eq_div, Int.cast_natCast]
    exact hy i
  rw [he]
  exact ⟨(KS.W30.divInt_num_natAbs_le _ _ hd).trans (hZ i),
    (KS.W30.divInt_den_le _ _ hd).trans (by simpa using hDb)⟩

theorem commonHeight_single {n : ℕ} (i : Fin n) :
    CommonHeight (Pi.single i (1 : ℚ)) 0 := by
  refine ⟨1, by decide, by simp, Pi.single i 1, ?_, ?_⟩
  · intro j
    by_cases hj : j = i <;> simp [hj]
  · intro j
    by_cases hj : j = i <;> simp [hj]

theorem CommonHeight.cons_zero {n E : ℕ} {y : Fin n → ℚ}
    (h : CommonHeight y E) : CommonHeight (Fin.cons 0 y) E := by
  obtain ⟨D, hD, hDb, Z, hy, hZ⟩ := h
  refine ⟨D, hD, hDb, Fin.cons 0 Z, ?_, ?_⟩
  · intro i
    exact Fin.cases (by simp) (fun j => by simpa using hy j) i
  · intro i
    exact Fin.cases (by simp) (fun j => by simpa using hZ j) i

def witnessHeightBudget (N b t : ℕ) : ℕ :=
  (t + 1) * ((N + 2) * (3 * KS.W30.inverseBitBound N b + 4))

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurCellMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurCellMachine

def workspace (input output x a b c : List Bool) : Fin 23 → List Bool :=
  fun j => if j = 0 then input else if j = 10 then output else if j = 19 then x
    else if j = 20 then a else if j = 21 then b else if j = 22 then c else []

def firstPorts (n : ℕ) (h : n ≤ 23) : Fin n ↪ Fin 23 := Fin.castLEEmb h

def extend {n : ℕ} (s : Fin n → List Bool) (spare : Fin 23 → List Bool) : Fin 23 → List Bool :=
  fun j => if h : j.val < n then s ⟨j.val, h⟩ else spare j

def pairAfter (source target : Fin 23) (before : Fin 23 → List Bool) : Fin 23 → List Bool :=
  WireAppend.after target 0 (WireAppend.after source target before)

end KS.W07.SchurCellMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_SchurCellCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurCellMachine

open KS.W01

def cellBudget (B : ℕ) : ℕ := 4000000 * (16 * B + 40) ^ 3

end KS.W07.SchurCellMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W07.SchurDimension
open SchurReadStage

def predecessorPorts : Fin 3 ↪ Fin 32 := ⟨![0,1,2], by decide⟩

def predecessorTicks (n : ℕ) : ℕ := (2*(Computability.encodeNat (n+1)).length+2) +
  (1 + (2*(max (Computability.encodeNat (n+1)).length 1+1) +
    (2*(Computability.encodeNat n).length+2)))

def counterPort (column : Bool) : Fin 32 := if column then 25 else 24

def unaryPorts (column : Bool) : Fin 3 ↪ Fin 32 :=
  ⟨![0,counterPort column,1], by cases column <;> decide⟩

@[simp] theorem unaryPorts_apply (column : Bool) (i : Fin 3) :
    unaryPorts column i = ![0,counterPort column,1] i := rfl

end KS.W07.SchurDimension

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurOperands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W07.SchurOperands
open SchurReadStage

def operands (s : Fin 32 → List Bool) (x a b c : List Bool) : Fin 32 → List Bool :=
  Function.update (Function.update (Function.update (Function.update s 19 x) 20 a) 21 b) 22 c

theorem workClear_update (s : Fin 32 → List Bool) (hs : WorkClear s)
    (k : Fin 4) (wire : List Bool) : WorkClear (Function.update s (destination k) wire) := by
  intro j hj
  have hne : j ≠ destination k := by intro h; have he := congrArg Fin.val h; simp [destination] at he; omega
  rw [Function.update_of_ne hne]
  exact hs j hj

def scalarPorts : Fin 23 ↪ Fin 32 := Fin.castLEEmb (by decide)

end KS.W07.SchurOperands

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurEntryMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurEntryMachine

def framePorts : Fin 3 ↪ Fin 32 := ⟨![0,10,1], by decide⟩

end KS.W07.SchurEntryMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurTableMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurTableMachine

def columnIncrementPorts : Fin 3 ↪ Fin 32 := ⟨![0,28,1], by decide⟩
def rowIncrementPorts : Fin 3 ↪ Fin 32 := ⟨![0,27,1], by decide⟩

end KS.W07.SchurTableMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurColumnLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurLoopState

def columnBudget (n B : ℕ) : ℕ := 4096*(n+2)^2*(B+1) +
  SchurCellMachine.cellBudget B + 200*(n+B+3)

end KS.W07.SchurLoopState

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurRowLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurLoopState

def rowTicks (n B i : ℕ) : ℕ := (4*n+6*(Computability.encodeNat n).length+4) +
  (1 + ((n*(columnBudget n B+1)+1) +
    (((Computability.encodeNat (n+1)).length+1) +
      (2*(Computability.encodeNat (i+1)).length+6))))

def rowBudget (n B : ℕ) : ℕ := n*(columnBudget n B+1)+20*(n+2)

end KS.W07.SchurLoopState

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurTableCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurTableMachine
open SchurLoopState

def initializeTicks (n : ℕ) : ℕ := SchurDimension.predecessorTicks n +
  ((4*n+6*(Computability.encodeNat n).length+4)+1)

def totalTicks (n B : ℕ) : ℕ := 30*(n+2) +
  ((n*(rowBudget n B+1)+1) + (n+5+3*(n*n*(32*B+39))))

end KS.W07.SchurTableMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_PivotDescentMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W07

def schurPorts : Fin 32 ↪ Fin 35 := Fin.castLEEmb (by decide)

end KS.W17.FixedPSD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_ControllerReachable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W07

def originalMatrixTapeBound (N b : ℕ) : ℕ := N*N*(8*KS.W30.inverseBitBound N b+15)
def originalWitnessTapeBound (N b : ℕ) : ℕ := N*(8*witnessHeightBudget N b N+15)
def originalFrameBound (N b : ℕ) : ℕ := 4*N+2*originalMatrixTapeBound N b+3

end KS.W17.FixedPSD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_ControllerReplayBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W07

def originalReplayInputBound (N b : ℕ) : ℕ :=
  originalMatrixTapeBound N b+N+originalWitnessTapeBound N b

def originalReplayStepBound (N b : ℕ) : ℕ :=
  10000000000000000000000000000*(originalReplayInputBound N b+1)^8+
    10*(originalReplayInputBound N b+1)+20

end KS.W17.FixedPSD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotRowClassify
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.PivotRowClassify
open KS.W07
open KS.W07.SchurReadStage

def classifierPorts : Fin 13 ↪ Fin 32 := Fin.castLEEmb (by decide)

end KS.W17.PivotRowClassify

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotRowBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.PivotRowBody
open KS.W07
open KS.W07.SchurReadStage

def incrementPorts : Fin 3 ↪ Fin 32 := ⟨![0,28,1], by decide⟩

def after (before : Fin 32 → List Bool) (q : ℚ) (idx : ℕ) : Fin 32 → List Bool :=
  if q = 0 then Function.update before 28 (Computability.encodeNat (idx+1))
  else Function.update before 24 [true]

end KS.W17.PivotRowBody

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotRowLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W17.PivotRowLoop
open KS.W07

structure Outcome where
  index : ℕ
  remaining : ℕ
  found : Bool

end KS.W17.PivotRowLoop

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotRowInitialize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.PivotRowLoop
open KS.W07

def initializeTicks (n : ℕ) : ℕ :=
  SchurDimension.predecessorTicks n + (4*n+6*(Computability.encodeNat n).length+4) +
    ((Computability.encodeNat n).length+1) + 1

end KS.W17.PivotRowLoop

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotRowFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W17.PivotRowLoop
open KS.W07

def finishTicks (idx k : ℕ) : ℕ := 2*(Computability.encodeNat idx).length+k+10

end KS.W17.PivotRowLoop

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotRowCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.PivotRowLoop
open KS.W07

def foundIndex (o : Outcome) : Option ℕ := if o.found then some o.index else none

theorem successor_finRange (n : ℕ) :
    (List.finRange n).map (fun j => j.succ.val) = List.range' 1 n := by
  calc
    _ = ((List.finRange n).map Fin.val).map (fun j => j+1) := by
      simp only [List.map_map,Function.comp_def,Fin.val_succ]
    _ = (List.range n).map (fun j => j+1) := by rw [List.map_coe_finRange_eq_range]
    _ = List.range' 1 n := by rw [List.range_eq_range',← List.range'_succ_left]

end KS.W17.PivotRowLoop

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotDecisionPorts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W07

def withSaved (saved : List Bool) (small : Fin 32 → List Bool) : Fin 35 → List Bool :=
  fun j => if h : j.val < 32 then small ⟨j.val,h⟩ else if j=32 then saved else []

end KS.W17.FixedPSD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotScannerBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W23.PivotScannerBounds
open KS.W01 KS.W07 KS.W17

theorem classifier_code_length (q : ℚ) : (W06.RationalSignClassifier.outputCode q).length ≤ 1 := by
  by_cases hn : q < 0
  · simp [W06.RationalSignClassifier.outputCode, hn]
  · by_cases hz : q = 0 <;> simp [W06.RationalSignClassifier.outputCode, hn, hz]

end KS.W23.PivotScannerBounds

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_ControllerTerminalBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W07

def originalTerminalBound (N b : ℕ) : ℕ :=
  100000000*(originalMatrixTapeBound N b+1)^4+
  1000000000000000000*(originalMatrixTapeBound N b+1)^3+
  100*(originalMatrixTapeBound N b+1)+originalMatrixTapeBound N b+N+10+
  (N+1)*originalReplayStepBound N b

end KS.W17.FixedPSD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurInputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurTableMachine
open scoped BigOperators

theorem totalTicks_mono {n N B C : ℕ} (hn : n≤N) (hB : B≤C) :
    totalTicks n B ≤ totalTicks N C := by
  unfold totalTicks SchurLoopState.rowBudget SchurLoopState.columnBudget SchurCellMachine.cellBudget
  gcongr

def inputLengthBudget (L : ℕ) : ℕ := totalTicks L L

end KS.W07.SchurTableMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_SchurPolynomialBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurTableMachine

theorem inputLengthBudget_le_monomial (L : ℕ) :
    inputLengthBudget L ≤ KS.W29.polynomialFuel 2000000000000 5 L := by
  unfold inputLengthBudget totalTicks SchurLoopState.rowBudget SchurLoopState.columnBudget
    SchurCellMachine.cellBudget KS.W29.polynomialFuel
  ring_nf
  omega

end KS.W07.SchurTableMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_PivotDescentBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W23.PivotDescentBounds
open KS.W01 KS.W07 KS.W17.FixedPSD

def descentCoefficient : ℕ := 3000000000000

def payloadBudget (L : ℕ) : ℕ := descentCoefficient*(L+1)^5

end KS.W23.PivotDescentBounds

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotReachableBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W23.PivotReachableBounds
open KS.W07 KS.W17 KS.W17.FixedPSD

def stepCoefficient : ℕ := PivotDescentBounds.descentCoefficient+100000000+2

def stepBudget (L : ℕ) : ℕ := stepCoefficient*(L+1)^5

theorem stepBudget_mono {L K : ℕ} (h : L ≤ K) : stepBudget L ≤ stepBudget K :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 5)

end KS.W23.PivotReachableBounds

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_ControllerRuntime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W07

def originalControllerStepBound (N b : ℕ) : ℕ :=
  KS.W23.PivotReachableBounds.stepBudget (originalMatrixTapeBound N b)+
    originalTerminalBound N b+N*originalFrameBound N b+1

def originalControllerBound (N b : ℕ) : ℕ := (N+1)*originalControllerStepBound N b

end KS.W17.FixedPSD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PSDControllerPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W23.PSDControllerPolynomial
open KS.W07 KS.W17 KS.W17.FixedPSD

def X : NaturalPolynomial := .variable
def inverseP : NaturalPolynomial :=
  X*(X*X)+(X*X+(X*(X*X)+X)*X)+1
def matrixP : NaturalPolynomial := X*X*(8*inverseP+15)
def witnessHeightP : NaturalPolynomial := (X+1)*((X+2)*(3*inverseP+4))
def witnessP : NaturalPolynomial := X*(8*witnessHeightP+15)
def frameP : NaturalPolynomial := 4*X+2*matrixP+3
def replayInputP : NaturalPolynomial := matrixP+X+witnessP
def replayP : NaturalPolynomial :=
  10000000000000000000000000000*(replayInputP+1)^8+10*(replayInputP+1)+20
def terminalP : NaturalPolynomial :=
  100000000*(matrixP+1)^4+1000000000000000000*(matrixP+1)^3+
    100*(matrixP+1)+matrixP+X+10+(X+1)*replayP
def stepP : NaturalPolynomial :=
  NaturalPolynomial.constant PivotReachableBounds.stepCoefficient*(matrixP+1)^5

def controllerPolynomial : NaturalPolynomial :=
  (X+1)*(stepP+terminalP+X*frameP+1)

def coefficient : ℕ := controllerPolynomial.coefficient

theorem expression_eval (L : ℕ) : controllerPolynomial.eval L = originalControllerBound L L := rfl

theorem expression_degree : controllerPolynomial.degree = 58 := by decide

theorem originalControllerBound_mono_dim {N K : ℕ} (b : ℕ) (h : N ≤ K) :
    originalControllerBound N b ≤ originalControllerBound K b := by
  unfold originalControllerBound originalControllerStepBound originalTerminalBound
    originalFrameBound originalReplayStepBound originalReplayInputBound
    originalWitnessTapeBound originalMatrixTapeBound witnessHeightBudget
    KS.W30.inverseBitBound PivotReachableBounds.stepBudget
  gcongr

theorem originalControllerBound_le_monomial {N L : ℕ} (h : N ≤ L) :
    originalControllerBound N L ≤ coefficient*(L+1)^58 := by
  calc
    originalControllerBound N L ≤ originalControllerBound L L := originalControllerBound_mono_dim L h
    _ = controllerPolynomial.eval L := (expression_eval L).symm
    _ ≤ controllerPolynomial.coefficient*(L+1)^controllerPolynomial.degree :=
      controllerPolynomial.eval_le_input_polynomial L
    _ = coefficient*(L+1)^58 := by rw [expression_degree]; rfl

end KS.W23.PSDControllerPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_DenseFieldCounter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.DenseFieldCounter

def unary (n : ℕ) : List Bool := List.replicate n true

end CurrentKS.DenseFieldCounter

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_ExpressionPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W13.ExpressionMachine

def registers (source values input output left sign : List Bool) : Fin 24 → List Bool :=
  fun j => if j=20 then source else if j=21 then values else if j=0 then input
    else if j=10 then output else if j=23 then left else if j=13 then sign else []

def firstPorts (n : ℕ) (hn : n ≤ 24) : Fin n ↪ Fin 24 :=
  ⟨fun i => ⟨i.val,lt_of_lt_of_le i.isLt hn⟩,fun _ _ h => Fin.ext (congrArg (fun j : Fin 24 => j.val) h)⟩

inductive BinaryOp where | add | sub | mul | div deriving DecidableEq

def BinaryOp.eval : BinaryOp → ℚ → ℚ → ℚ
  | .add,q,r => q+r
  | .sub,q,r => q-r
  | .mul,q,r => q*r
  | .div,q,r => q/r

end KS.W13.ExpressionMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_FramedMapRoutine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.FramedMapRoutine

variable {α : Type*}
  {cost : α → ℕ}

abbrev source (n : ℕ) : Fin (n+5) := ⟨n+1,by omega⟩
abbrev accumulator (n : ℕ) : Fin (n+5) := ⟨n+2,by omega⟩
abbrev work (n : ℕ) : Fin (n+5) := ⟨n+3,by omega⟩
abbrev scratch (n : ℕ) : Fin (n+5) := ⟨n+4,by omega⟩

def ports (n : ℕ) : Fin (n+1) ↪ Fin (n+5) := ⟨Fin.castAdd 4,Fin.castAdd_injective _ _⟩
def decodePorts (n : ℕ) : Fin 3 ↪ Fin (n+5) :=
  ⟨![source n,0,work n],by intro i j h;fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]⟩
def framePorts (n : ℕ) : Fin 3 ↪ Fin (n+5) :=
  ⟨![work n,0,scratch n],by intro i j h;fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]⟩

lemma decodePorts_0 (n : ℕ) : decodePorts n 0 = source n := rfl
lemma decodePorts_1 (n : ℕ) : decodePorts n 1 = 0 := rfl
lemma decodePorts_2 (n : ℕ) : decodePorts n 2 = work n := rfl
lemma framePorts_0 (n : ℕ) : framePorts n 0 = work n := rfl
lemma framePorts_1 (n : ℕ) : framePorts n 1 = 0 := rfl
lemma framePorts_2 (n : ℕ) : framePorts n 2 = scratch n := rfl

end CurrentKS.FramedMapRoutine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ScalarRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization

variable {α β : Type*}

lemma fold_add_zero (xs : List ℚ) : xs.foldl (fun a b => a+b) 0=xs.sum := by
  have h : ∀ z : ℚ,xs.foldl (fun a b => a+b) z=z+xs.sum := by
    induction xs with
    | nil => intro z;simp
    | cons x xs ih => intro z;simp [ih,add_assoc]
  simpa using h 0

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ArrayRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization

variable {α γ : Type*}

lemma fold_natAdd (n k z : ℕ) : (fun a : ℕ×ℕ => (a.1,a.1+a.2))^[n] (k,z)=(k,n*k+z) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply',ih];simp [Nat.add_mul,Nat.add_comm,Nat.add_left_comm]

lemma iterate_ratSucc (n : ℕ) (q : ℚ) : (fun x : ℚ => x+1)^[n] q=q+n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply',ih];push_cast <;> ring

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_VectorRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open Matrix

variable {α β γ : Type*}

def chooseFold (pred : α → Bool) (f : α → β) (xs : List α) (a : β) : β :=
  xs.foldr (fun value result => if pred value then f value else result) a

lemma chooseFold_find (pred : α → Bool) (f : α → β) (xs : List α) (a : β) :
    chooseFold pred f xs a = (xs.find? pred).elim a f := by
  induction xs with
  | nil => rfl
  | cons value values inductionHypothesis =>
    simp only [chooseFold,List.foldr_cons,List.find?_cons]
    cases predicateValue : pred value <;> simp_all [chooseFold]

def zipDefault (f : α×β → γ) (a : α) (b : β) (p : List α×List β) : List γ :=
  (List.range p.1.length).map (fun i => f (p.1.getD i a,p.2.getD i b))

lemma getD_ofFn {n : ℕ} (f : Fin n → α) (i : Fin n) (a : α) :
    (List.ofFn f).getD i.val a=f i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

lemma range_map_fin {n : ℕ} (f : ℕ → α) :
    (List.range n).map f=List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp at hi
    simp

lemma zipDefault_ofFn {n : ℕ} (f : α×β → γ) (a : α) (b : β)
    (x : Fin n → α) (y : Fin n → β) :
    zipDefault f a b (List.ofFn x,List.ofFn y)=List.ofFn (fun i => f (x i,y i)) := by
  unfold zipDefault
  rw [List.length_ofFn,range_map_fin]
  apply congrArg List.ofFn
  funext i
  rw [getD_ofFn,getD_ofFn]

def dotValue (p : List ℚ×List ℚ) : ℚ := (zipDefault (fun q : ℚ×ℚ => q.1*q.2) 0 0 p).sum

lemma vectorAdd_ofFn {n : ℕ} (x y : Fin n → ℚ) :
    zipDefault (fun p : ℚ×ℚ => p.1+p.2) 0 0 (List.ofFn x,List.ofFn y)=List.ofFn (x+y) :=
  zipDefault_ofFn _ _ _ _ _

lemma dot_ofFn {n : ℕ} (x y : Fin n → ℚ) : dotValue (List.ofFn x,List.ofFn y)=dotProduct x y := by
  unfold dotValue
  rw [zipDefault_ofFn,List.sum_ofFn]
  rfl

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_FaceArrayRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization

lemma range_finRange (n : ℕ) : List.range n=(List.finRange n).map Fin.val := by simp
def extendEntryData (p : (List ℕ×(List ℚ×List ℚ))×ℕ) : ℚ :=
  ((List.range p.1.1.length).find? (fun j => p.1.1.getD j 0==p.2)).elim
    (p.1.2.1.getD p.2 0) (fun j => p.1.2.2.getD j 0)

def extendData (p : List ℕ×(List ℚ×List ℚ)) : List ℚ :=
  (List.range p.2.1.length).map (fun i => extendEntryData (p,i))

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_StoredPSDRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open Matrix

lemma fold_append_flatten {α : Type*} (xs : List (List α)) (acc : List α) :
    xs.foldl (fun a b => a++b) acc=acc++xs.flatten := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp [ih,List.append_assoc]

abbrev MatrixObject := Σ n : ℕ,Matrix (Fin n) (Fin n) ℚ

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_EndpointRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
def updateData (p : List ℚ×(ℕ×ℚ)) : List ℚ :=
  (List.range p.1.length).map (fun j => if j=p.2.1 then p.2.2 else p.1.getD j 0)
lemma update_data {n : ℕ} (x : Fin n → ℚ) (i : Fin n) (t : ℚ) :
    updateData (List.ofFn x,(i.val,t))=List.ofFn (Function.update x i t) := by
  rw [updateData,List.length_ofFn,range_map_fin]
  congr 1
  funext j
  rw [getD_ofFn]
  by_cases h : j=i
  · subst j;simp
  · have hv : j.val≠i.val := fun hh => h (Fin.ext hh)
    simp [h,hv,Function.update]

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_RootRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
def rootStep (pow : ℕ) (p : ℚ×(ℚ×ℚ)) : ℚ×(ℚ×ℚ) :=
  let mid := (p.2.1+p.2.2)/2
  (p.1,if mid^pow≤p.1 then (mid,p.2.2) else (p.2.1,mid))

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_RoundedStepRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open Matrix

abbrev StepParameters := ℚ×ℚ
abbrev UpdateData := StepParameters×(List ℚ×List ℚ)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_PencilCompileRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open Matrix
open scoped BigOperators

def basisData (p : ℕ×ℕ) : List ℚ := (List.range p.1).map (fun j => if p.2=j then 1 else 0)
lemma basis_data {n : ℕ} (i : Fin n) : basisData (n,i.val)=List.ofFn (Pi.single i (1:ℚ)) := by
  rw [basisData,range_map_fin]
  apply congrArg List.ofFn
  funext j
  simp [Pi.single_apply,Fin.ext_iff,eq_comm]

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_FaceQueryRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization

structure FaceParams where
  d : ℕ
  N : ℕ
  coords : Fin N → Fin d×Fin d → ℚ
  base : Fin N → ℚ
  nu : ℚ
  lam : ℚ

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_SelectionRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization

variable {α β : Type*}

def betterData (p : (α×ℚ)×(α×ℚ)) : α×ℚ :=
  if p.2.2 < p.1.2 then p.2 else p.1

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_FaceChoiceRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
lemma vectorSub_data {n : ℕ} (x y : Fin n → ℚ) :
    zipDefault (fun p : ℚ×ℚ => p.1-p.2) 0 0 (List.ofFn x,List.ofFn y)=List.ofFn (x-y) :=
  zipDefault_ofFn _ _ _ _ _

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_OriginalFieldsRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open scoped BigOperators

def recordEntryData (imag : Bool) (p : ((ℕ×List ℚ)×ℕ)×ℕ) : ℚ :=
  p.1.1.2.getD (2*(p.1.2*p.1.1.1+p.2)+(if imag then 1 else 0)) 0

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_VarianceRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open scoped BigOperators

structure MatrixGrid where
  n : ℕ
  M : Matrix (Fin n) (Fin n) ℚ
  den : ℕ

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_OriginalSignRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open scoped BigOperators

def recordTraceData (p : ℕ×List ℚ) : ℚ :=
  ((List.range p.1).map (fun i => recordEntryData false ((p,i),i))).sum

def nonzeroIndicesData (xs : List ℚ) : List ℕ :=
  (List.range xs.length).filter (fun i => decide (xs.getD i 0≠0))

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Duality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uJ uV uI2 uI3 uV2 uW uJ2 uV3 uE2 uT uJ3 uH uI4

section

namespace StrongThinTree.ShortcutDual
noncomputable section
open Matrix Finset Filter Topology
open scoped Classical MatrixOrder Matrix.Norms.L2Operator
variable {V : Type uV3} {E : Type uE2} {T : Type uT} {J : Type uJ3} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype T] [Fintype J]

omit [DecidableEq V] in
lemma outer_posSemidef (v : V → ℝ) : (vecMulVec v v).PosSemidef := by
  simpa using posSemidef_vecMulVec_self_star v

end
end StrongThinTree.ShortcutDual

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_ShortcutDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace StrongThinTree.MultiGraph
noncomputable section
open Matrix Finset
open scoped Classical MatrixOrder Matrix.Norms.L2Operator
variable {n m h : ℕ} (G : MultiGraph n m)

abbrev point (v : Fin n) : Fin n → ℝ := Pi.single v 1

def incidence (e : Fin m) : Fin n → ℝ := point (G.left e) - point (G.right e)

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_GraphMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree
variable {V : Type uV} [Fintype V] [DecidableEq V]

namespace MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)
def laplacian (F : Finset (Fin m)) : Matrix (Fin n) (Fin n) ℝ := ∑e ∈ F, vecMulVec (G.incidence e) (G.incidence e)
lemma laplacian_psd (F : Finset (Fin m)) : (G.laplacian F).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro e _
  simpa only [star_trivial] using posSemidef_vecMulVec_self_star (G.incidence e)

end MultiGraph
end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_UnaryArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unary arithmetic. -/

section

namespace CurrentKS.Realization
open KS.W23

lemma pred_iterate (n k : ℕ) : Nat.pred^[k] n = n-k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,Nat.pred_eq_sub_one]; omega

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_ExtractionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Filter
open scoped Topology
namespace StrongThinTree

def errorU (r : ℕ) : ℝ := (r:ℝ)^(-1/16:ℝ)

end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Normalization_Descent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization descent. -/

section

namespace AlgorithmicThinTrees.Normalization
open Matrix Finset StrongThinTree
open scoped MatrixOrder

section Covariance
variable {E I : Type*} [normalizationFintypeE : Fintype E]
  [normalizationDecidableEqE : DecidableEq E] [normalizationFintypeI : Fintype I]
  [normalizationDecidableEqI : DecidableEq I]

def covariance {K : Type*} [Field K] (v : E → I → K) (a : E → K) : Matrix I I K :=
  ∑e, a e • vecMulVec (v e) (v e)

end Covariance

end AlgorithmicThinTrees.Normalization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Normalization_Algorithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization algorithm. -/

section

namespace AlgorithmicThinTrees.Normalization
open Matrix Finset StrongThinTree
open scoped MatrixOrder
variable {m d : ℕ}

def weights (s : Fin m → ℚ) : Fin m → ℚ := fun e => (s e)^2

def decrement (t : ℚ) : ℚ := 1-t^2
def threshold (q : ℕ) (t : ℚ) : ℚ := 1/q+4*decrement t

def testMatrix (q : ℕ) (t : ℚ) (v : Fin m → Fin d → ℚ)
    (s : Fin m → ℚ) (e : Fin m) : Matrix (Fin d) (Fin d) ℚ :=
  threshold q t • covariance v (weights s)-(s e)^2 • vecMulVec (v e) (v e)

def multiplier (r : ℕ) : ℚ := 1-1/(16*(r:ℚ)^2)
def normalizationLength (m r : ℕ) : ℕ := (2*m+1)*256*r^4

end AlgorithmicThinTrees.Normalization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Normalization_Realization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization realization. -/

section


namespace CurrentKS.Realization
open KS.W23

variable {β : Type*}

lemma find_map_flagged {α β : Type*} (xs : List α) (p : α → Bool)
    (f : α → β) (b : β) :
    (((xs.map fun a => (p a,f a)).find? Prod.fst).elim b Prod.snd)=
      (xs.find? p).elim b f := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons,List.find?_cons]
    cases h : p a <;> simp_all
end CurrentKS.Realization

namespace AlgorithmicThinTrees.Normalization.Stack
open CurrentKS CurrentKS.Realization KS.W23
open Matrix

structure Params where
  d : ℕ
  m : ℕ
  q : ℕ
  t : ℚ
  v : Fin m → Fin d → ℚ

structure State where
  params : Params
  scales : Fin params.m → ℚ

abbrev Column := Σ s : State, Fin s.params.m

def fixedStepParams (a : Params×ℕ) : Params :=
  ⟨a.1.d,a.1.m,a.1.q,multiplier a.2,a.1.v⟩

end AlgorithmicThinTrees.Normalization.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_UnaryRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unary root. -/

section

namespace CurrentKS.Realization
open KS.W23

def unaryRootStep (d : ℕ) (a : ℕ×ℕ) : ℕ×ℕ :=
  (a.1,if (a.2+1)^d ≤ a.1 then a.2+1 else a.2)

lemma unaryRootStep_iterate_bound (d k : ℕ) (a : ℕ×ℕ) :
    ((unaryRootStep d)^[k] a).1=a.1 ∧ ((unaryRootStep d)^[k] a).2≤a.2+k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    dsimp only [unaryRootStep]
    constructor
    · exact ih.1
    · split <;> omega

lemma unaryRootStep_iterate_zero (d : ℕ) (hd : d≠0) (r k : ℕ) :
    ((unaryRootStep d)^[k] (r,0)).2=min k (Nat.nthRoot d r) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    dsimp only [unaryRootStep]
    simp only [(unaryRootStep_iterate_bound d k (r,0)).1,ih]
    simp only [←Nat.le_nthRoot_iff hd]
    split <;> omega

lemma unaryRoot_le (d r : ℕ) (hd : d≠0) : Nat.nthRoot d r ≤ r :=
  (Nat.le_self_pow hd _).trans (Nat.pow_nthRoot_le (Or.inl hd))

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_MatrixBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric matrix bound. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m d : ℕ}

def difference (u v : Fin n) : Fin n → ℝ := point u-point v

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_CenteredMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered matrices. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m : ℕ}

def ones (n : ℕ) : Fin n → ℝ := fun _ => 1

def constantProjection (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (n : ℝ)⁻¹ • vecMulVec (ones n) (ones n)

def centering (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := 1-constantProjection n

lemma constantProjection_psd : (constantProjection n).PosSemidef := by
  apply Matrix.PosSemidef.smul _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  simpa only [star_trivial] using posSemidef_vecMulVec_self_star (ones n)

lemma constantProjection_symmetric : (constantProjection n)ᵀ=constantProjection n :=
  isHermitian_iff_isSymm.mp constantProjection_psd.isHermitian

lemma centering_symmetric : (centering n)ᵀ=centering n := by
  simp only [centering,transpose_sub,transpose_one,constantProjection_symmetric]

def centered (D : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  centering n*D*centering n

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_ConeRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric cone representation. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder Matrix.Norms.Elementwise Topology
open Filter

section TraceDual
variable {n : ℕ}

abbrev DistinctTriple (n : ℕ) :=
  {ijk : Fin n × Fin n × Fin n // ijk.1 ≠ ijk.2.1 ∧ ijk.2.1 ≠ ijk.2.2 ∧ ijk.1 ≠ ijk.2.2}

def triangleMatrix (u v w : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  vecMulVec (difference u v) (difference u v)+
  vecMulVec (difference v w) (difference v w)-
  vecMulVec (difference u w) (difference u w)

def triangleGenerator (ijk : DistinctTriple n) : Matrix (Fin n) (Fin n) ℝ :=
  triangleMatrix ijk.1.1 ijk.1.2.1 ijk.1.2.2

lemma triangleMatrix_hermitian (u v w : Fin n) : (triangleMatrix u v w).IsHermitian :=
  ((ShortcutDual.outer_posSemidef _).isHermitian.add
    (ShortcutDual.outer_posSemidef _).isHermitian).sub (ShortcutDual.outer_posSemidef _).isHermitian

end TraceDual

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Encoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation encoding. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder Matrix.Norms.Elementwise

variable {n m : ℕ}

def responseMatrix (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  centered ((1/2 : ℝ) • (A+Aᵀ))

lemma responseMatrix_hermitian (A : Matrix (Fin n) (Fin n) ℝ) :
    (responseMatrix A).IsHermitian := by
  apply isHermitian_iff_isSymm.mpr
  simp only [responseMatrix,centered,IsSymm,transpose_mul,transpose_smul,transpose_add,
    transpose_transpose,centering_symmetric]
  rw [add_comm Aᵀ A,mul_assoc]

abbrev StepFree (n m : ℕ) :=
  Matrix (Fin n) (Fin n) ℝ × (DistinctTriple n → ℝ) × (Fin m → ℝ) × (Fin m → ℝ)

namespace StepFree

def matrix (x : StepFree n m) : Matrix (Fin n) (Fin n) ℝ := responseMatrix x.1
def multiplier (x : StepFree n m) : DistinctTriple n → ℝ := x.2.1
def y (x : StepFree n m) : Fin m → ℝ := x.2.2.1
def z (x : StepFree n m) : Fin m → ℝ := x.2.2.2

end StepFree

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Feasibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation feasibility. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Finset Matrix StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder Matrix.Norms.Elementwise

variable {n m : ℕ}

def continuationBaseline (m : ℕ) : ℝ := 1/((m:ℝ)+1)

def continuationStep (m : ℕ) : ℝ := continuationBaseline m/32

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_SpectralSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral size. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m : ℕ}

def graphSize (n m : ℕ) : ℝ := n+m+2

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Flow_RootedRelaxation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rooted relaxation. -/

section

namespace AlgorithmicThinTrees.Orientations
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical
variable {n m : ℕ}

structure FlowPoint (n m : ℕ) where
  x : Fin m → ℝ
  a : Fin n → Fin m → ℝ
  b : Fin n → Fin m → ℝ

end
end AlgorithmicThinTrees.Orientations
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation coordinates. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Orientations

abbrev Triple (n : ℕ) := Fin n × (Fin n × Fin n)
abbrev Var (n m : ℕ) :=
  (Fin n × Fin n) ⊕ (Triple n ⊕ ((Fin 3 × Fin m) ⊕ (Fin 2 × (Fin n × Fin m))))

def dimension (n m : ℕ) := n*n+(n*(n*n)+(3*m+2*(n*m)))

def index (n m : ℕ) : Var n m ≃ Fin (dimension n m) :=
  let et : Triple n ≃ Fin (n*(n*n)) :=
    ((Equiv.refl (Fin n)).prodCongr finProdFinEquiv).trans finProdFinEquiv
  let ef : (Fin 2 × (Fin n × Fin m)) ≃ Fin (2*(n*m)) :=
    ((Equiv.refl (Fin 2)).prodCongr finProdFinEquiv).trans finProdFinEquiv
  let ee := (finProdFinEquiv.sumCongr ef).trans finSumFinEquiv
  (finProdFinEquiv.sumCongr ((et.sumCongr ee).trans finSumFinEquiv)).trans finSumFinEquiv

variable {n m : ℕ}

def matIndex (i j : Fin n) : Fin (dimension n m) := index n m (.inl (i,j))
def mulIndex (ijk : Triple n) : Fin (dimension n m) := index n m (.inr (.inl ijk))
def edgeIndex (p : Fin 3) (e : Fin m) : Fin (dimension n m) := index n m (.inr (.inr (.inl (p,e))))
def flowIndex (p : Fin 2) (r : Fin n) (e : Fin m) : Fin (dimension n m) :=
  index n m (.inr (.inr (.inr (p,(r,e)))))

def rawMatrix {R : Type*} (v : Fin (dimension n m) → R) : Matrix (Fin n) (Fin n) R :=
  fun i j => v (matIndex i j)
def multiplier {R : Type*} (v : Fin (dimension n m) → R) : DistinctTriple n → R :=
  fun ijk => v (mulIndex ijk.val)
def y {R : Type*} (v : Fin (dimension n m) → R) : Fin m → R :=fun e => v (edgeIndex 0 e)
def z {R : Type*} (v : Fin (dimension n m) → R) : Fin m → R :=fun e => v (edgeIndex 1 e)
def flowX {R : Type*} (v : Fin (dimension n m) → R) : Fin m → R :=fun e => v (edgeIndex 2 e)
def flowA {R : Type*} (v : Fin (dimension n m) → R) : Fin n → Fin m → R :=fun r e => v (flowIndex 0 r e)
def flowB {R : Type*} (v : Fin (dimension n m) → R) : Fin n → Fin m → R :=fun r e => v (flowIndex 1 r e)

def step (v : Fin (dimension n m) → ℝ) : StepFree n m :=
  (rawMatrix v,multiplier v,y v,z v)
def flow (v : Fin (dimension n m) → ℝ) : FlowPoint n m :=
  ⟨flowX v,flowA v,flowB v⟩

noncomputable def encode (c : StepFree n m) (F : FlowPoint n m) : Fin (dimension n m) → ℝ :=
  fun k => match (index n m).symm k with
  | .inl (i,j) => c.1 i j
  | .inr (.inl ijk) =>
      if h : ijk.1 ≠ ijk.2.1 ∧ ijk.2.1 ≠ ijk.2.2 ∧ ijk.1 ≠ ijk.2.2 then c.multiplier ⟨ijk,h⟩ else 0
  | .inr (.inr (.inl (p,e))) => if p=0 then c.y e else if p=1 then c.z e else F.x e
  | .inr (.inr (.inr (p,(r,e)))) => if p=0 then F.a r e else F.b r e

@[simp] lemma encode_mat (c : StepFree n m) (F : FlowPoint n m) (i j : Fin n) :
    encode c F (matIndex i j)=c.1 i j := by simp [encode,matIndex]
@[simp] lemma encode_mul (c : StepFree n m) (F : FlowPoint n m) (ijk : DistinctTriple n) :
    encode c F (mulIndex ijk.val)=c.multiplier ijk := by simp [encode,mulIndex,ijk.property]
@[simp] lemma encode_y (c : StepFree n m) (F : FlowPoint n m) (e : Fin m) :
    encode c F (edgeIndex 0 e)=c.y e := by simp [encode,edgeIndex]
@[simp] lemma encode_z (c : StepFree n m) (F : FlowPoint n m) (e : Fin m) :
    encode c F (edgeIndex 1 e)=c.z e := by simp [encode,edgeIndex]

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_AffinePencil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Affine pencil. -/

section

namespace AlgorithmicThinTrees.RationalForms
open Matrix Finset
open scoped BigOperators

abbrev Affine (d : ℕ) := ℚ × (Fin d → ℚ)

namespace Affine
variable {d : ℕ}

def cst (q : ℚ) : Affine d := (q,0)
def coord (i : Fin d) : Affine d := (0,Pi.single i 1)

noncomputable def real (z : Fin d → ℝ) (a : Affine d) : ℝ :=
  (a.1:ℝ)+∑i, (a.2 i:ℝ)*z i

@[simp] lemma real_cst (z : Fin d → ℝ) (q : ℚ) : real z (cst q)=(q:ℝ) := by
  simp [real,cst]
@[simp] lemma real_coord (z : Fin d → ℝ) (i : Fin d) : real z (coord i)=z i := by
  simp [real,coord,Pi.single_apply,apply_ite,ite_mul]
@[simp] lemma real_zero (z : Fin d → ℝ) : real z (0 : Affine d)=0 := by
  simp [real]
@[simp] lemma real_add (z : Fin d → ℝ) (a b : Affine d) : real z (a+b)=real z a+real z b := by
  simp [real,add_mul,sum_add_distrib]
  ring
@[simp] lemma real_sub (z : Fin d → ℝ) (a b : Affine d) : real z (a-b)=real z a-real z b := by
  simp [real,sub_mul,sum_sub_distrib]
  ring
@[simp] lemma real_smul (z : Fin d → ℝ) (q : ℚ) (a : Affine d) :
    real z (q • a)=(q:ℝ)*real z a := by
  simp [real,mul_add,mul_assoc,mul_sum]
@[simp] lemma real_sum {I : Type*} (s : Finset I) (f : I → Affine d) (z : Fin d → ℝ) :
    real z (∑i ∈ s,f i)=∑i ∈ s,real z (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi,ih]

lemma ext_real {a b : Affine d} (h : ∀z : Fin d → ℝ,real z a=real z b) : a=b := by
  have hc : a.1=b.1 := by
    have hh := h 0
    simp only [real,Pi.zero_apply,mul_zero,sum_const_zero,add_zero] at hh
    exact_mod_cast hh
  apply Prod.ext hc
  funext i
  have hh := h (Pi.single i 1)
  simp only [real,hc,Pi.single_apply,mul_ite,mul_one,mul_zero,sum_ite_eq',mem_univ,
    ite_true, if_true,add_right_inj] at hh
  exact_mod_cast hh

end Affine

lemma symmetric_of_real {I : Type*} {d : ℕ} (A : Matrix I I (Affine d))
    (h : ∀z, (A.map (Affine.real z)).IsSymm) : A.IsSymm :=
  IsSymm.ext fun i j => Affine.ext_real (fun z => (h z).apply i j)

end AlgorithmicThinTrees.RationalForms
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Pencil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation pencil. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Orientations RationalForms
open scoped BigOperators
variable {n m : ℕ}

abbrev Form (n m : ℕ) := Affine (dimension n m)

def qdiff (i j : Fin n) : Fin n → ℚ := Pi.single i 1-Pi.single j 1

def qtriangle (ijk : DistinctTriple n) : Matrix (Fin n) (Fin n) ℚ :=
  vecMulVec (qdiff ijk.1.1 ijk.1.2.1) (qdiff ijk.1.1 ijk.1.2.1)+
  vecMulVec (qdiff ijk.1.2.1 ijk.1.2.2) (qdiff ijk.1.2.1 ijk.1.2.2)-
  vecMulVec (qdiff ijk.1.1 ijk.1.2.2) (qdiff ijk.1.1 ijk.1.2.2)

def qproject (n : ℕ) : Matrix (Fin n) (Fin n) ℚ := (1 : Matrix (Fin n) (Fin n) ℚ)-Matrix.of (fun (_ _ : Fin n) => (n:ℚ)⁻¹)

lemma cast_qdiff (i j k : Fin n) : (qdiff i j k : ℝ)=difference i j k := by
  simp only [qdiff, difference, point, Pi.sub_apply, Pi.single_apply, Rat.cast_sub]
  split_ifs <;> norm_num
lemma cast_qtriangle (ijk : DistinctTriple n) (i j : Fin n) :
    (qtriangle ijk i j : ℝ)=triangleGenerator ijk i j := by
  simp [qtriangle,triangleGenerator,triangleMatrix,Matrix.sub_apply,vecMulVec,cast_qdiff]
lemma cast_qproject (i j : Fin n) : (qproject n i j : ℝ)=centering n i j := by
  change (((1 : Matrix (Fin n) (Fin n) ℚ) i j-(n:ℚ)⁻¹ : ℚ) : ℝ)=_
  simp only [centering,constantProjection,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
    vecMulVec,Matrix.of_apply,ones,mul_one,Rat.cast_sub,Rat.cast_inv,Rat.cast_natCast,
    Matrix.one_apply]
  split_ifs <;> norm_num

def matrixForm (i j : Fin n) : Form n m :=
  ∑b, ∑a, (qproject n i a*qproject n b j/2) •
    (Affine.coord (matIndex a b)+Affine.coord (matIndex b a))

lemma real_matrixForm (v : Fin (dimension n m) → ℝ) (i j : Fin n) :
    Affine.real v (matrixForm i j)=(step v).matrix i j := by
  simp only [matrixForm,Affine.real_sum,Affine.real_smul,Affine.real_add,Affine.real_coord,
    Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,cast_qproject]
  simp only [step,StepFree.matrix,responseMatrix,centered,Matrix.mul_apply,
    Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply,rawMatrix,smul_eq_mul,sum_mul]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro a _
  ring

abbrev MatBlock (m : ℕ) := Fin 2 ⊕ Fin m

abbrev ScalarBlock (n m : ℕ) :=
  Triple n ⊕ ((Fin 7 × Fin m) ⊕ ((Fin 3 × (Fin n × Fin m)) ⊕ ((Fin n × Fin n) ⊕ Fin 1)))

def order (n m : ℕ) := n*(2+m)+(n*(n*n)+(7*m+(3*(n*m)+(n*n+1))))

def rowIndex (n m : ℕ) : ((Fin n × MatBlock m) ⊕ ScalarBlock n m) ≃ Fin (order n m) :=
  let et : Triple n ≃ Fin (n*(n*n)) :=
    ((Equiv.refl (Fin n)).prodCongr finProdFinEquiv).trans finProdFinEquiv
  let ef : (Fin 3 × (Fin n × Fin m)) ≃ Fin (3*(n*m)) :=
    ((Equiv.refl (Fin 3)).prodCongr finProdFinEquiv).trans finProdFinEquiv
  let eu := (finProdFinEquiv.sumCongr (Equiv.refl (Fin 1))).trans finSumFinEquiv
  let ee := (finProdFinEquiv.sumCongr ((ef.sumCongr eu).trans finSumFinEquiv)).trans finSumFinEquiv
  let em := ((Equiv.refl (Fin n)).prodCongr finSumFinEquiv).trans finProdFinEquiv
  (em.sumCongr ((et.sumCongr ee).trans finSumFinEquiv)).trans finSumFinEquiv

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Search
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation search. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Orientations
open scoped BigOperators
variable {n m : ℕ}

def sizeQ (n m : ℕ) : ℚ := n+m+2
def baselineQ (m : ℕ) : ℚ := 1/(m+1)
def stepQ (m : ℕ) : ℚ := baselineQ m/32
def radiusQ (n m : ℕ) : ℚ := (sizeQ n m)^(-50:ℤ)
def errorQ (n m : ℕ) : ℚ := (sizeQ n m)^(-10:ℤ)

@[simp] lemma cast_sizeQ (n m : ℕ) : (sizeQ n m:ℝ)=graphSize n m := by
  simp [sizeQ,graphSize]
@[simp] lemma cast_baselineQ (m : ℕ) : (baselineQ m:ℝ)=continuationBaseline m := by
  simp [baselineQ,continuationBaseline]
@[simp] lemma cast_stepQ (m : ℕ) : (stepQ m:ℝ)=continuationStep m := by
  simp [stepQ,continuationStep]
@[simp] lemma cast_radiusQ (n m : ℕ) : (radiusQ n m:ℝ)=(graphSize n m)^(-50:ℤ) := by
  simp [radiusQ]

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Iteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation iteration. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped MatrixOrder
variable {n m : ℕ}

def target (m r : ℕ) (Q g : ℚ) : ℚ := Q-g*r*stepQ m-2*stepQ m

def qresponse (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  qproject n*((1/2:ℚ) • (A+Aᵀ))*qproject n

structure State (n m : ℕ) where
  scale : ℚ
  quality : ℚ
  matrix : Matrix (Fin n) (Fin n) ℚ
  capacity : Fin m → ℚ

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Schedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation schedule. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped MatrixOrder
variable {n m : ℕ}

def gain (r : ℕ) : ℚ := 1/(Nat.nthRoot 8 r:ℚ)

def blocks (r : ℕ) : ℕ := Nat.nthRoot 16 r

def blockLength (m : ℕ) : ℕ := 32*(m+1)

def scheduleLength (m r : ℕ) : ℕ := blockLength m*blocks r

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_BlockAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Block assembly. -/

section

namespace CurrentKS.Realization
open Matrix KS.W23

variable {n k l : ℕ}

def blockRowEquiv {U S : Type*} (eb : U ≃ Fin k) (es : S ≃ Fin l) :
    ((Fin n × U) ⊕ S) ≃ Fin (n*k+l) :=
  ((((Equiv.refl (Fin n)).prodCongr eb).trans finProdFinEquiv).sumCongr es).trans finSumFinEquiv

@[simp] lemma blockRowEquiv_left {U S : Type*} (eb : U ≃ Fin k) (es : S ≃ Fin l)
    (i : Fin n) (b : U) : (blockRowEquiv eb es (.inl (i,b))).val=(eb b).val+k*i.val := rfl
@[simp] lemma blockRowEquiv_right {U S : Type*} (eb : U ≃ Fin k) (es : S ≃ Fin l)
    (s : S) : (blockRowEquiv (n:=n) eb es (.inr s)).val=n*k+(es s).val := rfl

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_FiniteFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite families. -/

section

namespace CurrentKS.Realization
open KS.W23

variable {α β : Type*}
variable {I J : α → Type*} {n m : α → ℕ}

def sumEquiv (e : (a : α) → I a ≃ Fin (n a)) (e' : (a : α) → J a ≃ Fin (m a))
    (a : α) : I a ⊕ J a ≃ Fin (n a+m a) :=
  ((e a).sumCongr (e' a)).trans finSumFinEquiv

def sumLeft (_e : (a : α) → I a ≃ Fin (n a)) (_e' : (a : α) → J a ≃ Fin (m a))
    (p : {p : Σ a,I a ⊕ J a // p.2.isLeft=true}) : Σ a,I a :=
  ⟨p.val.1,p.val.2.getLeft p.property⟩
def sumRight (_e : (a : α) → I a ≃ Fin (n a)) (_e' : (a : α) → J a ≃ Fin (m a))
    (p : {p : Σ a,I a ⊕ J a // ¬p.2.isLeft=true}) : Σ a,J a :=
  ⟨p.val.1,p.val.2.getRight (by have hp := p.property; cases h : p.val.2 <;> simp_all)⟩

lemma sumRight_index (e : (a : α) → I a ≃ Fin (n a)) (e' : (a : α) → J a ≃ Fin (m a))
    (p : {p : Σ a,I a ⊕ J a // ¬p.2.isLeft=true}) :
    (sumEquiv e e' p.val.1 p.val.2).val-n p.val.1=
      (e' (sumRight e e' p).1 (sumRight e e' p).2).val := by
  rcases p with ⟨⟨a,i|j⟩,h⟩
  · simp at h
  · change n a+(e' a j).val-n a=(e' a j).val
    omega

def prodEquiv (e : (a : α) → I a ≃ Fin (n a)) (e' : (a : α) → J a ≃ Fin (m a))
    (a : α) : I a × J a ≃ Fin (n a*m a) :=
  ((e a).prodCongr (e' a)).trans finProdFinEquiv

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_RationalAffineEval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational affine eval. -/

section


namespace AlgorithmicThinTrees.RationalForms
open Matrix Finset
open scoped BigOperators
namespace Affine
variable {d : ℕ}
def rat (v : Fin d → ℚ) (a : Affine d) : ℚ := a.1+∑i,a.2 i*v i
@[simp] lemma rat_cst (v : Fin d → ℚ) (q : ℚ) : rat v (cst q)=q := by simp [rat,cst]
@[simp] lemma rat_coord (v : Fin d → ℚ) (i : Fin d) : rat v (coord i)=v i := by
  simp [rat,coord,Pi.single_apply,ite_mul]
@[simp] lemma rat_zero (v : Fin d → ℚ) : rat v (0 : Affine d)=0 := by simp [rat]
@[simp] lemma rat_add (v : Fin d → ℚ) (a b : Affine d) : rat v (a+b)=rat v a+rat v b := by
  simp [rat,add_mul,sum_add_distrib] <;> ring
@[simp] lemma rat_sub (v : Fin d → ℚ) (a b : Affine d) : rat v (a-b)=rat v a-rat v b := by
  simp [rat,sub_mul,sum_sub_distrib] <;> ring
@[simp] lemma rat_smul (v : Fin d → ℚ) (q : ℚ) (a : Affine d) : rat v (q • a)=q*rat v a := by
  simp [rat,mul_add,mul_assoc,mul_sum]
@[simp] lemma rat_sum {I : Type*} (s : Finset I) (f : I → Affine d) (v : Fin d → ℚ) :
    rat v (∑i ∈ s,f i)=∑i ∈ s,rat v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi,ih]
end Affine
end AlgorithmicThinTrees.RationalForms
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_MatrixConstraintRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix constraint realization. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open CurrentKS.Realization KS.W23 Matrix StrongThinTree RationalForms
open scoped BigOperators

namespace Stack

def triangleAt {n : ℕ} (t : Triple n) : Matrix (Fin n) (Fin n) ℚ :=
  vecMulVec (qdiff t.1 t.2.1) (qdiff t.1 t.2.1)+
    vecMulVec (qdiff t.2.1 t.2.2) (qdiff t.2.1 t.2.2)-
    vecMulVec (qdiff t.1 t.2.2) (qdiff t.1 t.2.2)

end Stack
end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_Realization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Signing realization. -/

section

namespace AlgorithmicThinTrees.Signing.Stack
open CurrentKS.Realization KS.W23 Matrix

structure Frame where
  d : ℕ
  m : ℕ
  v : Fin m → Fin d → ℚ

structure FormFrame where
  form : MatrixObject
  m : ℕ
  v : Fin m → Fin form.1 → ℚ

structure FramePair where
  a : ℕ
  b : ℕ
  m : ℕ
  u : Fin m → Fin a → ℚ
  v : Fin m → Fin b → ℚ

def FramePair.left (a : FramePair) : Frame := ⟨a.a,a.m,a.u⟩
def FramePair.right (a : FramePair) : Frame := ⟨a.b,a.m,a.v⟩

structure FormPair where
  a : MatrixObject
  b : MatrixObject
  m : ℕ
  u : Fin m → Fin a.1 → ℚ
  v : Fin m → Fin b.1 → ℚ

def FormPair.left (p : FormPair) : FormFrame := ⟨p.a,p.m,p.u⟩
def FormPair.right (p : FormPair) : FormFrame := ⟨p.b,p.m,p.v⟩

end AlgorithmicThinTrees.Signing.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_GraphicHalf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Graphic half. -/

section

namespace AlgorithmicThinTrees.GraphicHalf
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open MetricTests MetricTests.RationalStep Normalization
open scoped MatrixOrder
variable {n d m : ℕ}

def positiveForm (X : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  X+Matrix.of (fun _ _ => (n:ℚ)⁻¹)

end AlgorithmicThinTrees.GraphicHalf
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_ShortcutExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Shortcut extraction. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped MatrixOrder
variable {n m : ℕ}

def State.active (a : State n m) : Finset (Fin m) := univ.filter (fun e => 0 < a.capacity e)

def State.packingTarget (a : State n m) : ℕ := ⌊a.quality-1⌋₊

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_HalfNumeric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Half numeric. -/

section

namespace AlgorithmicThinTrees.GraphicHalf
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open MetricTests MetricTests.RationalStep Normalization Filter Topology
open scoped MatrixOrder

noncomputable def varianceBound (r : ℕ) : ℝ := 5*(r:ℝ)^(-1/4:ℝ)
noncomputable def halfError (r : ℕ) : ℝ := 20*Real.sqrt (2*varianceBound r)

structure Numeric (r : ℕ) : Prop where
  rlarge : 4 ≤ r
  small : errorU r ≤ 1/128
  inverse : 4/(r:ℝ) ≤ errorU r
  loss : halfError r ≤ errorU r

end AlgorithmicThinTrees.GraphicHalf
end

end OAI
end


