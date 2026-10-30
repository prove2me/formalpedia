-- Prove2me | Definitions.Def_OAIQ081S075
-- name    : OAIQ081S075
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:56:29.874701+00:00
-- url     : https://prove2.me/theorems/93928319-2307-4103-ae54-1385b1319db2
-- title:
--   Definitions bundle OAIQ081S075 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 118 declarations of OpenAI's Lean: 90 definitions and 28 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.value`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.MetadataBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.nativePositions`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Staging.actionCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Staging.actionResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Staging.cost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Staging.result`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.headEntry`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.paddedConstraint`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.Bounded`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.termTotal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.termValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Scan.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.executionContext`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.records`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.rowBytes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.rowRecord`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramInitialize.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native.callbackBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native.polynomialBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.advance`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.Cache.Totals`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.Cache.Values`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.FactoredEncodes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.FactoredTotalEncodes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.preparedRecords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.preparedTriples`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.triple`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.tripleRecord`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.tripleWords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.unsignedCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutUniversal.constraints`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutUniversal.headOwner`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutUniversal.jointOwner`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.bump`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.chooseMarked`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.dispatch`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.fetch`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.foreignBranch` and 50 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LayoutProgramArrays`, `SubexponentialSAT_SqrtLog_LayoutProgramEntries`, `SubexponentialSAT_SqrtLog_LayoutProgramNumeratorRun`, `SubexponentialSAT_SqrtLog_LayoutProgramPadded`, `SubexponentialSAT_SqrtLog_LayoutProgramScalar`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarStep`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameInput`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceBankState`, `SubexponentialSAT_SqrtLog_LayoutProgramStaging`, `SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupScan`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramContext`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramInitialize`, `SubexponentialSAT_SqrtLog_LayoutSourceValuesProgram`, `SubexponentialSAT_SqrtLog_LayoutSourceValuesProgramLoop`, `SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram`, `SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgramInterface`, `SubexponentialSAT_SqrtLog_LayoutUniversal`, `SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramBranches`, `SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramChoose`, `SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramFetch`, `SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramRun`, `SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramTest`, `SubexponentialSAT_SqrtLog_LeafNodeCacheProgram`, `SubexponentialSAT_SqrtLog_LeafNodeSamplesProgram`, `SubexponentialSAT_SqrtLog_LeafProgramHash`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramBinary`, `SubexponentialSAT_SqrtLog_LeafStatisticsSemantics`, `SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsFactor`, `SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsNeutral`, `SubexponentialSAT_SqrtLog_PolynomialExecutorProgramExtract`, `SubexponentialSAT_SqrtLog_PolynomialExecutorProgramFlatten`, `SubexponentialSAT_SubexpDenseLiteralPadding`, `SubexponentialSAT_SubexpDenseOperandIO`, `SubexponentialSAT_SubexpEvaluationProgram`, `SubexponentialSAT_SubexpKernelControl`, `SubexponentialSAT_SubexpNodeIndexProgram`, `SubexponentialSAT_SubexpRowInterpolation`, `SubexponentialSAT_SubexpRowPostfixInterpreter`, `SubexponentialSAT_SubexpRowPostfixServices`, `SubexponentialSAT_Subexp_CandidateScoreProgram`, `SubexponentialSAT_Subexp_DimensionProgram`, `SubexponentialSAT_Subexp_MismatchPlanProgram`, `SubexponentialSAT_Subexp_PackingLeftovers`, `SubexponentialSAT_Subexp_UniversalRowFactorLoop`, `SubexponentialSAT_Subexp_UniversalRowFactors`, `SubexponentialSAT_Subexp_UniversalRowGuard`, `SubexponentialSAT_Subexp_UniversalRowMismatchTypes`, `SubexponentialSAT_Subexp_UniversalRowProgram`, `SubexponentialSAT_Subexp_UniversalRowTermFraming`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S047`, `OAIQ081S048`, `OAIQ081S050`, `OAIQ081S051`, `OAIQ081S052`, `OAIQ081S053`, `OAIQ081S054`, `OAIQ081S055`, `OAIQ081S056`, `OAIQ081S057` and `OAIQ081S058` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S089`, `OAIQ081S090`, `OAIQ081S091`, `OAIQ081S092`, `OAIQ081S093`, `OAIQ081S098` and `OAIQ081S099`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.scalarProgram_runsIn_total`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.factoredEncodes_sum`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.factoredTotalEncodes_sum`, `OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding.program_runsIn` and `OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixServices.program_runsIn`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.eventually_raw_scope_guards`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_measured_guards`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.accumulate_eval_total`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.multiply_eval_total`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.scalarProgram_runsIn_total`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.factoredEncodes_sum`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.factoredTotalEncodes_sum`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.statistics_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBounds.measured_polylog`, `OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding.program_runsIn` and `OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixServices.program_runsIn`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S047
import Definitions.Def_OAIQ081S048
import Definitions.Def_OAIQ081S050
import Definitions.Def_OAIQ081S051
import Definitions.Def_OAIQ081S052
import Definitions.Def_OAIQ081S053
import Definitions.Def_OAIQ081S054
import Definitions.Def_OAIQ081S055
import Definitions.Def_OAIQ081S056
import Definitions.Def_OAIQ081S057
import Definitions.Def_OAIQ081S058

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramArrays
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical access to the two-array integer matrix ABI. Every array entry is a
runtime-width binary word; its signed value is positive minus negative. The
fixed program below preserves both arrays, the index and width. It does not
assume a unit-cost array lookup or add an integer primitive to the machine. -/

namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.ArrayUpdateLifted

@[simp] theorem readSignedStacks_negative (p n : List Bool)
    (stk : Stacks (Fin 11)) : readSignedStacks p n stk 6 = n ++ stk 6 := by
  simp [readSignedStacks]

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRowInterpolation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit mismatch interpolation for the multi-color layout

Section 3.3 of `subexponential-sat.txt`. All inverse data are supplied as
units. The polynomials are finite sums and products, not chosen witnesses.
Their scalar evaluation functions are executable from the supplied ring
operations and units; the semantic polynomial definitions use mathlib's
noncomputable polynomial representation.
-/

namespace SubexponentialSAT.SubexpRowInterpolation

open scoped BigOperators

variable {E I V C : Type*} [CommRing E] [DecidableEq I]

variable {node : I → E}

theorem basis_natDegree_le (u : NodeUnits node) (s : Finset I) {i : I} (hi : i ∈ s) :
    (basis u s i).natDegree ≤ s.card := by
  have hprod : (∏ j ∈ s.erase i, basisDivisor u i j).natDegree ≤ (s.erase i).card := by
    calc
      _ ≤ ∑ j ∈ s.erase i, (basisDivisor u i j).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ _j ∈ s.erase i, 1 :=
        Finset.sum_le_sum (fun j _hj => basisDivisor_natDegree_le u i j)
      _ = (s.erase i).card := by simp
  calc
    (basis u s i).natDegree ≤ 1 + (s.erase i).card := by
      apply Polynomial.natDegree_mul_le_of_le
      · exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
      · exact hprod
    _ = s.card := by rw [Nat.add_comm, Finset.card_erase_add_one hi]

theorem correctionPolynomial_natDegree_le (u : NodeUnits node) (s : Finset I) (d : I → E) :
    (correctionPolynomial u s d).natDegree ≤ s.card := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact (Polynomial.natDegree_C_mul_le _ _).trans (basis_natDegree_le u s hi)

variable [DecidableEq V]

theorem columnCorrection_natDegree_le (Y : Finset V) (A : V → Finset I)
    (u : NodeUnits node) (d : V → I → E) {R : ℕ}
    (hcard : ∀ y ∈ Y, (A y).card ≤ R) (y : V) :
    (columnCorrection Y A u d y).natDegree ≤ R := by
  by_cases hy : y ∈ Y
  · simp only [columnCorrection, ite_eq_left hy]
    exact (correctionPolynomial_natDegree_le u (A y) (d y)).trans (hcard y hy)
  · simp [columnCorrection, hy]

section Mismatches

variable [Fintype I] [Fintype V] [DecidableEq C]

theorem mismatchCorrection_natDegree_le (head : V → I → C) (σ : I → C) (R : ℕ)
    (u : NodeUnits node) (d : V → I → E) (y : V) :
    (mismatchCorrection head σ R u d y).natDegree ≤ R := by
  apply columnCorrection_natDegree_le
  intro z hz
  exact (mem_correctionColumns head σ R z).mp hz

end Mismatches

/-! ## Executable finite expression codes

The following constructors produce polynomial expression data using only
finite `List.ofFn` traversals. Their denotations are the proved polynomials
above. This supplies a concrete path representation in addition to the
executable scalar evaluator.
-/

end SubexponentialSAT.SubexpRowInterpolation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutUniversal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual universal incidence-copy block over a commutative coefficient
ring in which the power-of-two denominator is a unit. -/

namespace SubexponentialSAT.SqrtLog.LayoutUniversal

open scoped BigOperators
open Matrix
open SubexponentialSAT.MulticolorTypes
open LayoutPullback LayoutExactBuckets LayoutScaledMatrices

variable {r Q : ℕ} {O : Type*} [CommRing O]

def jointOwner (t : Fin Q) (g : Fin r) : Joint t g (0 : Fin 1) → Head t g :=
  fun j => ⟨j.val, j.property.1⟩

def headOwner (t : Fin Q) (g : Fin r) : Head t g → U r Q := Subtype.val

theorem headOwner_injective (t : Fin Q) (g : Fin r) :
    Function.Injective (headOwner t g) := Subtype.val_injective

noncomputable def constraints (A R : ℕ) (t : Fin Q) (g : Fin r) :
    Joint t g (0 : Fin 1) → Head t g → ℤ :=
  pulledConstraints (jointOwner t g)
    (clearedDefect (LayoutNumerator.denominator R)
      (LayoutNumerator.joint (0 : Fin 1) t g A R))

end SubexponentialSAT.SqrtLog.LayoutUniversal

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_DimensionProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed generator for all unary dimensions from zero through a runtime bound

The input bound is a unary stack, and the output is a framed list of unary
payloads. The program has no bound-dependent control labels.
-/

namespace SubexponentialSAT.Subexp.DimensionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.TupleProgram

theorem readCounter_eval (a : State 5 5) :
    Eval readCounter 1 a (readCounterState a) := .base (.atom _ _)

end SubexponentialSAT.Subexp.DimensionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CandidateScoreProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control candidate scoring

Score records are accumulated as reversed serialized bytes and reversed once
at the end, so output score order agrees with the input candidate order.
-/

namespace SubexponentialSAT.Subexp.CandidateScoreProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev finish : Cmd 16 36 :=
  .seq (TupleProgram.pushConst 35 0 false) (.call (StackRoutines.transferProgram 35 32 0 1))

end SubexponentialSAT.Subexp.CandidateScoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntries
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Executable scalar specifications in the physical side/joint list order.
These definitions do not assert a primitive runtime bound: their exact
identification lets the separately traced scan/arithmetic producer feed the
semantic layout without an arbitrary finite-type ordering oracle. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.MulticolorTypes
open LayoutPullback LayoutExactBuckets LayoutScaledMatrices

variable {r Q : ℕ}

def headEntry (A R : ℕ) (t : Fin Q) (g : Fin r)
    (u : Joint t g (0 : Fin 1)) (y : LayoutUniversal.Head t g) : ℤ :=
  if y.val ∈ joint t g (0 : Fin 1) then
    (if u.val = y.val then (2 : ℤ) ^ (R-1) else 0) -
      LayoutCoefficientAlgorithm.scalarEntry (0 : Fin 1) t A R u.val y.val
  else 0

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete arithmetic adapters for the cached layout scalar loop.
The working signed pair occupies 0/1, the next operand 2/3, the record queue
15, and the saved sum 16/17. All arithmetic is an actual compiled bit program.
-/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

@[simp] theorem one_value : pairValue one = 1 := rfl

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A single cached scalar term: three parsed operands, three real signed
multiplications, and one real signed addition. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

def termValue (x : Triple) : ℤ :=
  pairValue x.1*pairValue x.2.1*pairValue x.2.2

def Bounded (B : ℕ) (xs : List Triple) : Prop :=
  ∀ x ∈ xs, pairLength x.1 ≤ B ∧ pairLength x.2.1 ≤ B ∧ pairLength x.2.2 ≤ B

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! Polynomial source-step bounds for the concrete cached scalar arithmetic.
The stream has three actual binary signed operands per summand, not a stream
of precomputed products or an assumed arithmetic callback. -/

/-! Exact unsigned component totals for the same concrete scalar program.
The extra invariant controls cancellation without changing any instruction. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

@[simp] theorem one_total : wordTotal one = 1 := rfl

def termTotal (x : Triple) : ℕ := wordTotal x.1 * wordTotal x.2.1 * wordTotal x.2.2

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


-- LayoutTriplePreparationProgramLookup.lean

/-! List-level cache representation for the preserving physical array scan. -/

/-! One real triple-production iteration: two scans, three serializers and
paid cleanup. Only a parity bit is kept outside the subroutine registers. -/

/-! A fixed, paid iteration producing the three real scalar operands. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

/-- The scalar consumer uses this same three-word order definitionally. -/
def tripleWords (xs : List Triple) : List WordPair :=
  xs.flatMap fun x => [x.1,x.2.1,x.2.2]

def triple (c : Cache) (sign : Bool) (h k : ℕ) : Triple :=
  (signedPair sign (c.Hword h).1 (c.Hword h).2,c.power,c.Bword k)

def tripleRecord (t : Triple) : List Bool :=
  wordRecord t.1 ++ wordRecord t.2.1 ++ wordRecord t.2.2

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramLoop.lean

/-! The native unary loop produces all triples in increasing binomial index. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

def preparedTriples (c : Cache) : Bool → ℕ → ℕ → List Triple
  | _,0,_ => []
  | sign,n+1,k => triple c sign n k :: preparedTriples c (!sign) n (k+1)

def preparedRecords (c : Cache) (sign : Bool) (n k : ℕ) : List Bool :=
  (preparedTriples c sign n k).flatMap tripleRecord

@[simp] theorem preparedTriples_length (c : Cache) (s : Bool) (n k : ℕ) :
    (preparedTriples c s n k).length = n := by
  induction n generalizing s k with
  | zero => rfl
  | succ n ih => simp [preparedTriples,ih]

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramFinish.lean

/-! Initial unary copy/parity and final stream reversal are native paid calls. -/

/-! Complete cache-to-triple primitive program with all scans and copies paid. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgramInterface
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

-- LayoutTriplePreparationProgramAlgebra.lean

/-! The factored triple stream uses the positive H cache directly. The outer
parity and both powers in a scalar summand are combined before serialization. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

open scoped BigOperators
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar
open SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm
open SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence

def FactoredEncodes (A R d h : ℕ) (xs : List Triple) : Prop :=
  xs.length = R-d ∧ ∀ k : Fin xs.length,
    pairValue (xs.get k).1 = (-1 : ℤ)^(A+k.val)*(H A (R-1-d-k.val) : ℤ) ∧
    pairValue (xs.get k).2.1 = (2 : ℤ)^(R-1) ∧
    pairValue (xs.get k).2.2 = (h.choose k.val : ℤ)

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramSemantics.lean

/-! The actual generated stream has the exact coefficient sum and nonnegative
mass required by the scalar machine, despite the factored cache representation. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open scoped BigOperators
open RowSelectionProgram LayoutProgramScalar LayoutCoefficientRecurrence

def Cache.Values (c : Cache) (A R h : ℕ) : Prop :=
  (∀ i < R, pairValue (c.Hword i) = (H A i : ℤ)) ∧
  pairValue c.power = (2 : ℤ)^(R-1) ∧
  (∀ k < R, pairValue (c.Bword k) = (h.choose k : ℤ))

def Cache.Totals (c : Cache) (A R h : ℕ) : Prop :=
  (∀ i < R, wordTotal (c.Hword i) = H A i) ∧
  wordTotal c.power = 2^(R-1) ∧
  (∀ k < R, wordTotal (c.Bword k) = h.choose k)

def FactoredTotalEncodes (A R d h : ℕ) (xs : List LayoutProgramScalar.Triple) : Prop :=
  xs.length = R-d ∧ ∀ k : Fin xs.length,
    termTotal (xs.get k) = H A (R-1-d-k.val)*2^(R-1)*h.choose k.val

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramInterface.lean

/-! One consumer-facing contract for native triple preparation. -/

namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open RowSelectionProgram LayoutProgramScalar LayoutCoefficientRecurrence
open SubexponentialSAT.BinaryArithmetic

/-- Cache representation supplied by the native unsigned cache builders. -/
def unsignedCache (Hwords Bwords : List (List Bool)) (width : List Bool)
    (power : WordPair) (R : ℕ) : Cache :=
  ⟨Hwords,List.replicate R (List.replicate width.length false),
    Bwords,List.replicate R (List.replicate width.length false),width,power⟩

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramNumeratorRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.Numerator

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open UniversalEntry RowSelectionProgram
open MatrixScanProgram MatrixEntryEvaluation MatrixEntryKernel MatrixExtendedEntryProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q : ℕ}

def value (A R : ℕ) (t : Fin Q) (u y : UniversalType r Q 1) : ℤ :=
  if anchorValid (0 : Fin 1) t u y then
    LayoutCoefficientAlgorithm.scalarEntry (0 : Fin 1) t A R u y else 0

end SubexponentialSAT.SqrtLog.LayoutProgram.Numerator

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramPadded
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A computable integer row for every incidence position. Inactive covered
positions and non-head uncovered positions are zero. Active rows are precisely
the raw block constraints, with repetitions and zero padding permitted. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking

variable {r Q : ℕ} {I O : Type*}
variable [Fintype I] [DecidableEq I] [CommRing O]

def paddedConstraint (P : PackingData I (UniversalType r Q 1))
    (A R : ℕ) (t : Fin Q) (g : Fin r) : I → IncidenceHead P t g → ℤ :=
  fun v w => paddedEntry P A R t g v w.val

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramStaging
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A finite sequence of genuine copy, clear and constant-bit instructions.
The functional result is only a trace specification; execution uses the
fixed primitive instruction tables. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Staging

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

variable {r s : ℕ}

def actionResult (v pr : Fin r) : Action s → State r s → State r s
  | .copy src dst,a => ⟨readRegs a.regs v pr none,StackRoutines.copyStacks src dst a.stacks⟩
  | .clear dst,a => ⟨readRegs a.regs v pr none,StackRoutines.clearStacks dst a.stacks⟩
  | .push dst b,a => TupleProgram.pushedState dst v b a

def actionCost : Action s → State r s → ℕ
  | .copy src _,a => 7*(a.stacks src).length+5
  | .clear dst,a => 2*(a.stacks dst).length+3
  | .push _ _,_ => 2

def result (v pr : Fin r) : List (Action s) → State r s → State r s
  | [],a => a
  | op::ops,a => result v pr ops (actionResult v pr op a)

def cost (v pr : Fin r) : List (Action s) → State r s → ℕ
  | [],_ => 0
  | op::ops,a => actionCost op a+cost v pr ops (actionResult v pr op a)

end SubexponentialSAT.SqrtLog.LayoutProgram.Staging

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingLeftovers
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual leftover packing pass

The immutable covered table is searched for every original vertex. A found
vertex is skipped. A missing vertex is appended to reversed storage and both
lookup tables, with actual unary rank/address increments.
-/
namespace SubexponentialSAT.Subexp.PackingLeftovers

open BitProgram StructuredCalls MatrixProgramSupport

def data (regs : Fin 8 → Bool)
    (work query covered source payload rank address storage metadata addresses vertex : List Bool) : Data :=
  ⟨regs, ![work,[],query,[],[],[],covered,source,payload,[],rank,address,storage,metadata,addresses,vertex,[],[]]⟩

def state (regs : Fin 8 → Bool)
    (covered source rank address storage metadata addresses : List Bool) : Data :=
  data regs [] [] covered source [] rank address storage metadata addresses []

theorem data_stacks (regs : Fin 8 → Bool)
    (work query covered source payload rank address storage metadata addresses vertex : List Bool)
    (i : Fin 18) :
    (data regs work query covered source payload rank address storage metadata addresses vertex).stacks i =
      if i=0 then work else if i=2 then query else if i=6 then covered
      else if i=7 then source else if i=8 then payload else if i=10 then rank
      else if i=11 then address else if i=12 then storage else if i=13 then metadata
      else if i=14 then addresses else if i=15 then vertex else [] := by
  fin_cases i <;> rfl

theorem resetParser_eval (d : Data) :
    Eval resetParser 3 d ⟨parserRegs d.regs false true false,d.stacks⟩ := by
  exact (Eval.base (.atom (.set 5 false) d)).seq
    ((Eval.base (.atom (.set 6 true) _)).seq (Eval.base (.atom (.set 7 false) _)))

def configured (regs : Fin 8 → Bool) (records : Records) (source payload : List Bool)
    (s : Snapshot) (vertex : List Bool) : Data :=
  data regs [] [] (SelectorProgram.rawRecords records) source payload (unary s.rank) (unary s.address)
    s.storage s.metadata s.addresses vertex

theorem parser_state (regs : Fin 8 → Bool) (records : Records) (s : Snapshot)
    (source payload vertex newSource newPayload : List Bool) (tag present found : Bool) :
    RecordPrograms.state ports (configured regs records source payload s vertex)
      tag present found newSource newPayload =
    configured (parserRegs regs tag present found) records newSource newPayload s vertex := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> simp [configured,data,ports]

end SubexponentialSAT.Subexp.PackingLeftovers

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpKernelControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed controller constructing the separated postfix source

The input contains literal payloads and the three nested lists of blocks,
color groups, and terms.  The controller only parses frames, copies bits,
and emits postfix tags.  It has no arithmetic callback and never builds a
Cartesian product of the inner lists.  Three unary stacks hold the pending
right-fold operators, so the emitted source has exactly the association of
`SubexpAlgorithm.momentExpression`.
-/

namespace SubexponentialSAT.SubexpKernelControl

open BitProgram StructuredCalls

/-! ## Fixed source-constructor control -/

local infixr:60 " ;; " => Cmd.seq

abbrev unframe : Cmd 3 8 :=
  .call (ProgramLinking.liftProgram ParserProgram.unframeProgram registerMap (pairMap 0 4))

/-- The fixed body consumes exactly one unframed payload, then the next marker
is read. The same control table handles every list length. -/
abbrev scanLoop (body : Cmd 3 8) : Cmd 3 8 := .while 0 (unframe ;; body ;; popTag)

abbrev scan (body : Cmd 3 8) : Cmd 3 8 := popTag ;; scanLoop body

/-! ## Concrete machine states and elementary traces -/

/-! The following induction rule accounts for actual executions of the fixed
payload body. Its premises will be proved for `termBody`, `groupBody`, and
`blockBody`; the exported whole-controller statement has no callback argument. -/

/-! ## Forward-output service boundary -/

end SubexponentialSAT.SubexpKernelControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowGuard
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Count the actual mismatch-index records and compare their count with R. -/

namespace SubexponentialSAT.Subexp.UniversalRowGuard

open BitProgram StructuredCalls StackRoutines

abbrev command : Cmd 8 32 :=
  .seq (.call (copyProgram 28 17 15 (0 : Fin 8) 1))
    (.seq count (.seq (TupleProgram.pushConst 11 0 false)
      (.seq (.call (copyProgram 13 11 15 (0 : Fin 8) 1)) compareClean)))

end SubexponentialSAT.Subexp.UniversalRowGuard

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical source construction for universal interpolation rows

The input holds raw coefficient payloads, node inverses, and negative nodes.
It does not contain polynomial instructions. Fixed nested scans emit the
Lagrange products and correction sum as postfix source in canonical list order.
The surrounding row-data producer supplies the selected mismatch positions;
its matrix, cache, and type-mask construction is tracked separately.
-/

namespace SubexponentialSAT.Subexp.UniversalRowProgram

open BitProgram StructuredCalls
open SubexpKernelControl (Word pushWord operator popTag unframe emitFramedLiteral emitOperator countOne drain scan )

abbrev emitX : Cmd 3 8 :=
  .call (ProgramLinking.liftProgram SubexpHornerProgram.Literal.program id literalPorts)

local infixr:60 " ;; " => Cmd.seq

abbrev factorBody : Cmd 3 8 :=
  emitFramedLiteral ;; emitX ;; emitFramedLiteral ;; emitOperator false ;; emitOperator true ;; countOne 6

end SubexponentialSAT.Subexp.UniversalRowProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowFactors
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed array reads and framing for one interpolation factor. -/

namespace SubexponentialSAT.Subexp.UniversalRowFactors

open BitProgram StructuredCalls
open UniversalRowGather (Word)

/-- Prepend one complete factor record from its two raw scalar payloads.
The output is a record-list accumulator; its existing suffix is preserved. -/
abbrev emitFactor : Cmd 8 32 :=
  .seq (MatrixProgramSupport.emitFrame 12 22 23 (by decide))
    (.seq (MatrixProgramSupport.emitFrame 1 22 23 (by decide))
      (.seq (MatrixProgramSupport.emitFrame 22 21 23 (by decide))
        (TupleProgram.pushConst 21 0 true)))

end SubexponentialSAT.Subexp.UniversalRowFactors

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowFactorLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual diagonal exclusion and factor-record production for a row. -/

namespace SubexponentialSAT.Subexp.UniversalRowFactorLoop

open BitProgram StructuredCalls StackRoutines
open UniversalRowGather (Word)

abbrev selected : Cmd 8 32 :=
  .seq UniversalRowFactors.readFactor UniversalRowFactors.emitFactor

end SubexponentialSAT.Subexp.UniversalRowFactorLoop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowTermFraming
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical framing of a gathered correction term and the final row. -/

namespace SubexponentialSAT.Subexp.UniversalRowTermFraming

open BitProgram StructuredCalls

abbrev term : Cmd 8 32 :=
  .seq (MatrixProgramSupport.emitFrame 20 21 23 (by decide))
    (.seq (MatrixProgramSupport.emitFrame 19 21 23 (by decide))
      (.seq (MatrixProgramSupport.emitFrame 21 31 23 (by decide))
        (TupleProgram.pushConst 31 0 true)))

abbrev row : Cmd 8 32 := MatrixProgramSupport.emitFrame 18 31 23 (by decide)

end SubexponentialSAT.Subexp.UniversalRowTermFraming

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceValuesProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed control that constructs an ordered scalar table. The callback is an
actual finite command with a measured execution contract. Runtime unary node
indices and counters do not change the command. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open _root_.OAI.Algorithms.SubexponentialSAT.SubexpPolynomialServiceControl (transfer )

attribute [local simp] Fin.coe_ofNat_eq_mod

def advance : Code := Subexp.TupleProgram.pushConst 37 0 true

end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MismatchPlanProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical mismatch-position selection

The input consists of two packed arrays, a runtime row width, and a framed
list of numeric positions. Each callback reads the two rows with the actual
persistent array reader, compares their bytes, and emits exactly the unequal
positions. The arrays and their order are preserved.
-/

namespace SubexponentialSAT.Subexp.MismatchPlanProgram

open BitProgram StructuredCalls StackRoutines

def equalityInner := compiled CollisionStreamProgram.sealCommand (1 : Fin 13) 11
abbrev equality : Cmd 8 16 :=
  .call (ProgramLinking.liftProgram equalityInner equalityRegs equalityStacks)

end SubexponentialSAT.Subexp.MismatchPlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowMismatchTypes
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Read the two relevant words from the complete types, generate their
mismatch positions, and restore the temporary extracted words. -/

namespace SubexponentialSAT.Subexp.UniversalRowMismatchTypes

open BitProgram StructuredCalls StackRoutines MulticolorTypes

abbrev extract : Cmd 10 49 := .call (ProgramLinking.liftProgram
  MatrixInputProgram.program inputRegs inputStacks)

end SubexponentialSAT.Subexp.UniversalRowMismatchTypes

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual scalar producer's numerator input already contains precisely
all low type-extractor inputs. No second pre-expanded input is assumed. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

def nativePositions {r Q : ℕ} (u y : UniversalType r Q 1) : List ℕ :=
  MismatchPlanProgram.selectedPositions y.head (u.slot 0)

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Cache and workspace invariants for the actual metadata dispatch. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

def MetadataBound (m : GlobalBasisMetadata.Metadata) (S : ℕ) : Prop :=
  m.block.length ≤ S ∧ m.typeCode.length ≤ S ∧ m.rank.length ≤ S

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNodeIndexProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical lookup of the current field node

The fixed program copies the framed node table, parses its records in order,
compares their actual bits with the current node, and counts rejected records.
Its only visible stack change is the unary first matching index at port 116.
The source table at 125 and query at 78 are preserved.
-/

namespace SubexponentialSAT.SubexpNodeIndexProgram

open BitProgram StructuredCalls SubexpScanPrimitives

namespace Internal

abbrev callback : Cmd 5 7 :=
  .seq (.call (StackRoutines.reverseProgram 3 4 5 (0 : Fin 5) 1))
    (.seq (copy 0 4) (.seq compare (.seq (clear 3) (.seq (clear 4) finish))))

abbrev command : Cmd 5 7 := .seq (copy 1 2)
  (.seq (RecordPrograms.iterate ports callback) (clear 2))

end Internal

end SubexponentialSAT.SubexpNodeIndexProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

namespace Scan

def command : Code := liftCommand SubexpNodeIndexProgram.Internal.command 0 6 register stack

end Scan
end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpEvaluationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete evaluation-result extraction

The extractor removes the singleton operand-list framing, parses the result
payload into a reversed scratch stack, and transfers it to physical stack 15.
It clears the operand/depth/scratch stacks and preserves every other stack.
-/

namespace SubexponentialSAT.SubexpEvaluationProgram

open BitProgram
open SubexpPostfixControl

open SubexpPostfixGlobal

/-! ## Entry from arbitrary caller registers -/

abbrev resetProgram : Program 16 128 17 :=
  StructuredProgram.compiled (resetList (List.finRange 16)) 26 15

end SubexponentialSAT.SubexpEvaluationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpDenseOperandIO
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed finite framing operations at the physical postfix operand port.
These routines preserve the code/depth stacks and all surrounding data. -/

namespace SubexponentialSAT.SubexpDenseOperandIO

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev parseProgram : Program 16 128 7 :=
  ProgramLinking.liftProgram ParserProgram.frameProgram parseRegs parseStacks

abbrev takeOperand (dst : Fin 128) : Cmd 16 128 :=
  .seq (.base (.atom (.pop 27 0 1)))
    (.seq (.call parseProgram) (.call (StackRoutines.transferProgram 29 dst 0 1)))

abbrev writeProgram : Program 16 128 17 :=
  ProgramLinking.liftProgram SubexpNormalizeProgram.emitRecordProgram writeRegs writeStacks

end SubexponentialSAT.SubexpDenseOperandIO

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpDenseLiteralPadding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Padding arbitrary literal payloads for the dense interpreter

The existing five-label padding table already truncates long inputs. This
module proves that behavior without a length precondition, then connects the
table to the actual framed operand stack. The cached dense zero array supplies
the requested bit width; no dimension is baked into the program control.
-/

namespace SubexponentialSAT.SubexpDenseLiteralPadding

open BitProgram StructuredCalls ModularArithmetic ModularPrograms
open SubexpConvolutionControl (Store Code )

def take : Code := liftSmall (SubexpDenseOperandIO.takeOperand 21)

def write : Code := liftSmall (.call SubexpDenseOperandIO.writeProgram)

local infixr:60 " ;; " => Cmd.seq

def command : Code := take ;; SubexpConvolutionControl.copy 242 99 ;; pad ;;
  SubexpConvolutionControl.clear 21 ;; write

def reset : Code :=
  .call (ProgramLinking.liftProgram SubexpEvaluationProgram.resetProgram id smallPorts)

def program := compiled (command ;; reset) 27 27

end SubexponentialSAT.SubexpDenseLiteralPadding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete finite controllers for source fiber sums and ambient source-row
serialization. Parameters are actual finite programs with paid contracts. -/

/-! A runtime owner-fiber fold of actual serialized polynomial sources. -/

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

def rowRecord (bits : List Bool) : List Bool := true::Encoding.frame bits

def rowBytes (value : ℕ → List Bool) (j n : ℕ) : List Bool :=
  ((List.range' j n).map (fun i => rowRecord (value i))).flatten

@[simp] theorem rowBytes_zero (value : ℕ → List Bool) (j : ℕ) : rowBytes value j 0=[] := by
  simp [rowBytes]

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

/-! Paid bank relocation and register reset for the native polynomial source
executor. The parameter is a finite BitProgram; the integration selects the
checked polynomial executor, never a polynomial-value instruction. -/

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod
variable {Witness : Type*}

def records (encode : Witness → List Bool) (ws : List Witness) : List Bool :=
  ws.flatMap (fun w => rowRecord (encode w))

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

/-! The bytes produced by the runtime fold are the compiler output of the
same finite sum expression, including the empty-owner zero polynomial. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRowPostfixServices
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Framed arithmetic calls for source-row postfix expressions

The physical interpreter keeps its operand list on stack 27. These fixed
commands read two framed operands, call a dense polynomial service on
240/241, and frame its result from 244. All temporary stacks are restored;
the caller's remaining operands and every other stack are preserved.
-/

namespace SubexponentialSAT.SubexpRowPostfixServices

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpConvolutionControl (Code Store Data copy clear )
open SubexpDenseLiteralPadding (take write reset )

local infixr:60 " ;; " => Cmd.seq

/-- Move a runtime word in its original orientation, using the shared copy
scratch stack 120. The source and destination are fixed program ports. -/
def move (src dst : Fin 256) : Code := copy src dst ;; clear src

def prepare : Code := take ;; move 21 241 ;; take ;; move 21 240

def finish : Code := clear 240 ;; clear 241 ;;
  SubexpPolynomialServiceControl.transfer 244 29 ;; write

/-- The supplied arithmetic command is installed as actual finite code. -/
def command (arithmetic : Code) : Code := prepare ;; arithmetic ;; finish ;; reset

def program (arithmetic : Code) := compiled (command arithmetic) 27 27

end SubexponentialSAT.SubexpRowPostfixServices

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRowPostfixInterpreter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The source-row postfix interpreter on the fixed 256-stack workspace.
Only port names change; the checked dispatcher and all service transitions
are retained. Parameters such as R and the field remain encoded data. -/

namespace SubexponentialSAT.SubexpRowPostfixInterpreter

open BitProgram
open SubexpPostfixControl (serializeCode )
open SubexpPostfixInterpreter (cfg)
open SubexpPostfixGlobal (reindexCfg )

def physicalCfg {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin 252 → List Bool) : Cfg 16 256 l :=
  reindexCfg ports (cfg (r := 13) (s := 252) pc v p op code depth operands context)

@[simp] theorem physicalCfg_code {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin 252 → List Bool) :
    (physicalCfg pc v p op code depth operands context).stacks 26 = code := by
  simp [physicalCfg, reindexCfg, cfg]
  rfl

@[simp] theorem physicalCfg_depth {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin 252 → List Bool) :
    (physicalCfg pc v p op code depth operands context).stacks 28 = depth := by
  simp [physicalCfg, reindexCfg, cfg]
  rfl

@[simp] theorem physicalCfg_operands {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin 252 → List Bool) :
    (physicalCfg pc v p op code depth operands context).stacks 27 = operands := by
  simp [physicalCfg, reindexCfg, cfg]
  rfl

@[simp] theorem physicalCfg_scratch {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin 252 → List Bool) :
    (physicalCfg pc v p op code depth operands context).stacks 29 = [] := by
  simp [physicalCfg, reindexCfg, cfg]
  rfl

@[simp] theorem physicalCfg_context {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin 252 → List Bool) (i : Fin 252) :
    (physicalCfg pc v p op code depth operands context).stacks
      (ports (Fin.natAdd 4 i)) = context i := by
  simp [physicalCfg, reindexCfg, cfg]

/-- The input arithmetic table already uses shared physical ports. -/
abbrev localService {l : ℕ} (p : Program 16 256 l) : Program 16 256 l :=
  ProgramLinking.liftProgram p id ports.symm

abbrev globalProgram {a b c : ℕ} (add : Program 16 256 a) (mul : Program 16 256 b)
    (loader : Program 16 256 c) : Program 16 256 (37 + (2 + (a + (b + c)))) :=
  ProgramLinking.liftProgram
    (SubexpProjectedInterpreter.program (r := 13) (s := 252)
      (localService add) (localService mul) (localService loader)) id ports

@[simp] theorem globalProgram_input {a b c : ℕ} (add : Program 16 256 a)
    (mul : Program 16 256 b) (loader : Program 16 256 c) :
    (globalProgram add mul loader).inputStack = 26 := by
  simp [ SubexpProjectedInterpreter.program,
    SubexpPostfixInterpreter.stack]

@[simp] theorem globalProgram_output {a b c : ℕ} (add : Program 16 256 a)
    (mul : Program 16 256 b) (loader : Program 16 256 c) :
    (globalProgram add mul loader).outputStack = 27 := by
  simp [ SubexpProjectedInterpreter.program,
    SubexpPostfixInterpreter.stack]


end SubexponentialSAT.SubexpRowPostfixInterpreter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramContext
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact extraction of the native executor context from the source worker.
The four dispatcher ports are excluded from this context. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpRowPostfixInterpreter (ports physicalCfg )
attribute [local simp] Fin.coe_ofNat_eq_mod

def executionContext (s : Store) : Fin 252 → List Bool :=
  fun i => s (executorPorts (ports (Fin.natAdd 4 i)))

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramInitialize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed, width-generic initialization for the source-row executor. All
zero-array construction and copies are paid; only four output stacks change. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramInitialize
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram

def command : Code :=
  .seq (copy 210 243)
    (.seq (SubexpPolynomialConstructor.construct 104 104 242)
      (.seq (copy 242 192) (copy 210 193)))

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramInitialize

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceValuesProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! The scalar callback calls the actual integer numerator program, then the
actual binary-to-ring scaler. Its integer result is never supplied as input. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open MulticolorTypes IntegerRingLiftProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram (WordPair pairValue pairLength)
open scoped BigOperators
attribute [local simp] Fin.coe_ofNat_eq_mod

namespace Native

def callbackBudget (num bits t d : ℕ) : ℕ :=
  num + 1 + _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.polynomialBudget bits t d + 2*bits + 6

end Native
end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram


/-! Closed correction-table construction from type metadata and integer/ring
caches. No correction-scalar table is supplied to the program or theorem. -/


/-! Uniform polynomial accounting and per-index observation of generated
correction tables. All parameters describe actual bytes and runtime counts. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open MulticolorTypes IntegerRingLiftProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram (WordPair pairValue pairLength)
open scoped BigOperators

/-- An explicit polynomial upper bound on the complete constructed table. -/
def polynomialBudget (r Q A R W P t d : ℕ) : ℕ :=
  Q * (callbackBudget (Q * numeratorAllowance r Q A R W P) (integerBits R W P) t d +
    6*(d*SubexpLiftRing.baseWidth 3 t)+16)+14

end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramHash
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Sparse clause-circuit evaluation for one hash row

The input is a list of supplied nonzero coefficients and width-k clause lists.
The evaluator visits those lists directly; it never builds a truth table on the
union of the clause scopes. Counters include measured variable lookup and ring
callbacks. Their primitive realization is a separate obligation, not inferred
from these counters. `Algebra` also admits canonical truncated operations, whose
decoder need not be a homomorphism into the untruncated polynomial ring.
-/

namespace SubexponentialSAT.SqrtLog.LeafProgram

open SubexponentialSAT.SubexpSymbolicCost

variable {V C A : Type*}

section PolynomialSemantics

variable {R : Type*} [CommRing R]

noncomputable def rowPolynomial (decode : C → R) (terms : SparseRow V C) : MvPolynomial V R :=
  (terms.map fun term => MvPolynomial.C (decode term.1) * clausePolynomial term.2).sum

end PolynomialSemantics
end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramFetch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The selected payload is fetched by scanning the actual source record list. -/
namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def fetch (marked : Bool) : Code := .call
  (ProgramLinking.liftProgram HashInputProgram.Source.fetchProgram fetchRegs (fetchPorts marked))

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramTest
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

/-- The extra cell changes the comparison from f < h to f ≤ h. -/
def bump (extra : Bool) : Code :=
  .seq (Subexp.TupleProgram.pushConst 9 0 true)
    (if extra then Subexp.TupleProgram.pushConst 9 0 true else .base .skip)

def test (extra : Bool) : Code := .seq (copy 6 8) (.seq (copy 3 9) (.seq (bump extra) lessClean))

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramBranches
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def hashBranch : Code := .seq (fetch false) (mark true false)
def markedBranch : Code := .seq (clear 6)
  (.seq (copy 4 6) (.seq (fetch true) (mark false true)))

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramChoose
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def chooseMarked : Code := .ite 7 markedBranch neutralBranch
def foreignBranch : Code := .seq (test true) (.ite 3 chooseMarked neutralBranch)
def dispatch : Code := .seq (test false) (.ite 3 hashBranch foreignBranch)

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native dispatcher: reverse the incoming ID, classify it, and scan
only the selected source. No selected payload is supplied as an input. -/
namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def command : Code := .seq prepare dispatch
def program := compiled command 2 15

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafNodeCacheProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical staging of node-local cached ring words. The ambient source tapes
and ring masters are copied, never consumed. The two raw-one caches are built
by the checked sparse-constant program, rather than supplied semantically. -/
namespace SubexponentialSAT.SqrtLog.LeafNodeCacheProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

def rawOne (f : Fin 768 → List Bool) :=
  Encoding.frame (HashCircuitProgram.Constant.key (f 128).length) ++ Encoding.frame (f 207)


end SubexponentialSAT.SqrtLog.LeafNodeCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafNodeSamplesProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed indexed traversal of the actual framed node table. The installed
worker is a real command; its measured, frame-preserving execution remains an
explicit producer obligation. Neither the index nor a jet is semantic advice. -/
namespace SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

def state (regs : Fin 40 → Bool) (s : Store) : Data := ⟨regs,tapes s⟩

end SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramBinary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native unary-to-binary conversion for each statistics output. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Binary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
def program := compiled command 0 1

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Binary

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsNeutral
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact statistics for the neutral completion of the residual factor family. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open scoped BigOperators
open HighIncidence

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [DecidableEq E] in
theorem neutral_degree_eq (scope : E → Finset V) (v : V) :
    Incidence.degree (neutralScope scope) v = max 1 (Incidence.degree scope v) := by
  classical
  rw [Incidence.degree_eq_sum, Fintype.sum_sum_type]
  have hsplit :
      ((∑ e : E, if v ∈ neutralScope scope (Sum.inl e) then 1 else 0) +
        ∑ w : uncovered scope, if v ∈ neutralScope scope (Sum.inr w) then 1 else 0) =
      ((∑ e : E, if v ∈ scope e then 1 else 0) +
        ∑ w : uncovered scope, if v = w.val then 1 else 0) := by
    apply congrArg₂ (· + ·)
    · exact Finset.sum_congr rfl (fun e _ => by rfl)
    · exact Finset.sum_congr rfl (fun w _ => by
        change (if v ∈ ({w.val} : Finset V) then 1 else 0) = _
        simp only [Finset.mem_singleton])
  rw [hsplit]
  rw [← Incidence.degree_eq_sum]
  by_cases hv : Incidence.degree scope v = 0
  · let u : uncovered scope := ⟨v, by simp [uncovered, hv]⟩
    have hs : (∑ w : uncovered scope, if v = w.val then 1 else 0 : ℕ) = 1 := by
      rw [Finset.sum_eq_single u]
      · simp [u]
      · intro w _ hwu
        have hne : v ≠ w.val := by
          intro h
          apply hwu
          exact Subtype.ext h.symm
        simp [hne]
      · simp
    rw [hv, hs]
    decide
  · have hs : (∑ w : uncovered scope, if v = w.val then 1 else 0 : ℕ) = 0 := by
      apply Finset.sum_eq_zero
      intro w _
      have hne : v ≠ w.val := by
        intro h
        apply hv
        have hw : Incidence.degree scope w.val = 0 := by
          exact (Finset.mem_filter.mp w.property).2
        simpa [h] using hw
      simp [hne]
    rw [hs, Nat.add_zero, max_eq_right (Nat.one_le_iff_ne_zero.mpr hv)]

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The runtime scan equals the statistics of the actual residual scope family,
with precisely one neutral singleton for each unused free coordinate. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open scoped BigOperators
open LeafStatisticsProgram HighIncidence

def residualScope (scopes : List (List ℕ)) (mask : List Bool) :
    Fin scopes.length → Finset (Free mask) :=
  remainingScope (highMask mask) (Subexp.IncidencePlanSpec.pattern mask.length scopes).scope

def completedScope (scopes : List (List ℕ)) (mask : List Bool) :=
  neutralScope (residualScope scopes mask)

theorem pattern_degree (scopes : List (List ℕ)) (n : ℕ) (v : Fin n) :
    Incidence.degree (Subexp.IncidencePlanSpec.pattern n scopes).scope v = degree scopes v.val := by
  calc
    _ = Fintype.card (SlotAssignment.Incident (Subexp.IncidencePlanSpec.pattern n scopes) v) := by
      simp only [SlotAssignment.card_incident, Incidence.degree, Incidence.incident]
    _ = _ := Subexp.IncidencePlanSpec.card_incident n scopes v

@[simp] theorem residual_degree (scopes : List (List ℕ)) (mask : List Bool) (v : Free mask) :
    Incidence.degree (residualScope scopes mask) v = degree scopes v.val.val := by
  rw [residualScope, degree_remainingScope]
  exact pattern_degree scopes mask.length v.val

@[simp] theorem completed_degree (scopes : List (List ℕ)) (mask : List Bool) (v : Free mask) :
    Incidence.degree (completedScope scopes mask) v = max 1 (degree scopes v.val.val) := by
  rw [completedScope, neutral_degree_eq, residual_degree]

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsFactor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The exact native neutral ID is the rank of its uncovered original owner.
This is an explicit indexing equivalence, not just equality of cardinalities. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open PackingIncidenceInput LeafStatisticsProgram HighIncidence

theorem free_mem_lowOwners (mask : List Bool) (v : Free mask) :
    v.val.val ∈ lowOwners 0 mask := by
  apply (lowOwners_mem 0 v.val.val mask).mpr
  exact ⟨v.val, by simp, free_bit mask v⟩

/-- The `j`th neutral factor is attached to the `j`th uncovered free owner. -/
def neutralAt (scopes : List (List ℕ)) (mask : List Bool)
    (j : Fin (neutralOwners scopes 0 mask).length) :
    uncovered (residualScope scopes mask) := by
  let u := (neutralOwners scopes 0 mask).get j
  have hm := (neutralOwners_mem scopes 0 u mask).mp (List.get_mem _ j)
  have hb := (lowOwners_bounds 0 u mask hm.1).2
  have hu : u < mask.length := by simpa using hb
  have hf : mask.get ⟨u, hu⟩ = false := by
    obtain ⟨i, hi, hbit⟩ := (lowOwners_mem 0 u mask).mp hm.1
    have he : (⟨u, hu⟩ : Fin mask.length) = i := by
      apply Fin.ext
      simpa using hi.symm
    simpa only [he] using hbit
  let v : Free mask := ⟨⟨u, hu⟩, by rw [mem_highMask, hf]; decide⟩
  refine ⟨v, ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [residual_degree]
  change (Scan.indices scopes u).length = 0
  simp [hm.2]

@[simp] theorem neutralAt_value (scopes : List (List ℕ)) (mask : List Bool)
    (j : Fin (neutralOwners scopes 0 mask).length) :
    (neutralAt scopes mask j).val.val.val = (neutralOwners scopes 0 mask).get j := rfl

theorem factorCount_eq (scopes : List (List ℕ)) (mask : List Bool) :
    Semantics.factorCount scopes mask = scopes.length + (neutralOwners scopes 0 mask).length :=
  counter_eq_numbered_length scopes mask 0 scopes.length

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramExtract
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native removal of the final postfix frame. This exposes the plain
constant-coefficient-first array required by perturbation and interpolation. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl

local infixr:60 " ;; " => Cmd.seq

def extract : Code := SubexpDenseLiteralPadding.take ;;
  SubexpRowPostfixServices.move 21 240 ;; clear 27 ;; clear 28

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramFlatten
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Generic native extraction adapter for a completed postfix interpreter. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg )

abbrev flattenCommand {l : ℕ} (p : Program 16 256 l) : Code := .seq (.call p) extract
abbrev flattenProgram {l : ℕ} (p : Program 16 256 l) := compiled (flattenCommand p) 26 240

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end


