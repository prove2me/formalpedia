-- Prove2me | Definitions.Def_OAIQ081S014
-- name    : OAIQ081S014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:24:10.167056+00:00
-- url     : https://prove2.me/theorems/e45818e1-85b1-49ce-8067-63c1b871de62
-- title:
--   Definitions bundle OAIQ081S014 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 129 declarations of OpenAI's Lean: 104 definitions, 3 inductive types or structures and 22 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.wordDecode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.constraintMassBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.scalarMass`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.initialCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.termCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutRank.columnSelection`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native.stack`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Scan.register`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Scan.stack`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.unary`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.RowProperty`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.RowWorkClean`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.RowsClean`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.Store`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.appendResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.clearedSourceStore`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.emittedBytes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.evaluationInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.executorPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.initializationPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.initializeFinish`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.ownerRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.ownerStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.preparedSourceStore`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.rowBudgetPolynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.rowState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourcePorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.stagedSourceStore`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramInitialize.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness.Preserved`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.bodyCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.loopCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.prepareCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram.Native.stackMap`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram.Native.tapes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram.merge`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram.tapes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafBranchProgram.rankSum`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.cmpPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.cmpRegs` and 67 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LayoutProducedMatrixRank`, `SubexponentialSAT_SqrtLog_LayoutProgramMagnitude`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarCacheCell`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarStep`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceTyped`, `SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupPorts`, `SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupScan`, `SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupSemantics`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramAssembly`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramCore`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramCostBase`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramInitialize`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramInitializeLift`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramReadiness`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramRowsModel`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramSourceCall`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramStaging`, `SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram`, `SubexponentialSAT_SqrtLog_LeafAssignmentMergeProgram`, `SubexponentialSAT_SqrtLog_LeafAssignmentMergeProgramNative`, `SubexponentialSAT_SqrtLog_LeafBranchProgramRun`, `SubexponentialSAT_SqrtLog_LeafFactorDispatchProgram`, `SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramChoose`, `SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramFetch`, `SubexponentialSAT_SqrtLog_LeafHeadFactorsProgram`, `SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramLoop`, `SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramRun`, `SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramVisit`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramAddress`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBoot`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBoundsPrepare`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramStorage`, `SubexponentialSAT_SqrtLog_LeafParametersProgram`, `SubexponentialSAT_SqrtLog_LeafParametersProgramNative`, `SubexponentialSAT_SqrtLog_LeafProgramMass`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramFinalize`, `SubexponentialSAT_SqrtLog_LeafStatisticsSemantics`, `SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsEnumeration`, `SubexponentialSAT_SqrtLog_LeafWeightProgramNative`, `SubexponentialSAT_SubexpDenseLiteralPadding`, `SubexponentialSAT_SubexpDenseOperandIO`, `SubexponentialSAT_SubexpIntervalStart`, `SubexponentialSAT_SubexpPostfixInterpreter`, `SubexponentialSAT_SubexpProjectedInterpreter`, `SubexponentialSAT_SubexpRepresentedRows`, `SubexponentialSAT_SubexpRowInterpolation`, `SubexponentialSAT_SubexpRowPostfixInterpreter`, `SubexponentialSAT_SubexpSwapMultiplicity`, `SubexponentialSAT_SubexpUnaryRangeProgram`, `SubexponentialSAT_Subexp_BasisTransposePlanProgram`, `SubexponentialSAT_Subexp_MismatchPlanSpec`, `SubexponentialSAT_Subexp_TailInterval`, `SubexponentialSAT_Subexp_UniversalRowSource`, `SubexponentialSAT_Subexp_UniversalRowSourceBound`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S036`, `OAIQ081S037`, `OAIQ081S039`, `OAIQ081S041` and `OAIQ081S043`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank.actualMax_rank_budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank.actualRank_sum_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator.centered_rationalDefect_rank_relative` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Spectral.centered_normalizedTail_le_of_sq`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank.actualMax_rank_budget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Spectral.centered_normalizedTail_le_of_sq`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRowInterpolation
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

variable [DecidableEq V]

/-! ## Executable finite expression codes

The following constructors produce polynomial expression data using only
finite `List.ofFn` traversals. Their denotations are the proved polynomials
above. This supplies a concrete path representation in addition to the
executable scalar evaluator.
-/

/-- Finite arithmetic expression data for a univariate polynomial. -/
inductive PolynomialCode (E : Type*) where
  | constant (a : E)
  | indeterminate
  | add (p q : PolynomialCode E)
  | mul (p q : PolynomialCode E)

end SubexponentialSAT.SubexpRowInterpolation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSwapMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Multiplicities of register-swap eigenvalue labels

The negative local labels are strictly below the diagonal and the positive
labels are on or above it. Counting these labels and their tensor words is
independent of the characteristic of the coefficient field.
-/

namespace SubexponentialSAT.SubexpSwapMultiplicity

open scoped BigOperators

/-- Probability of a negative local eigenvalue for a uniformly chosen
ordered pair label. -/
def negativeProbability (r : ℕ) : ℚ := ((r : ℚ) - 1) / (2 * r)

/-! ## General binomial second moment and the interval tail -/

end SubexponentialSAT.SubexpSwapMultiplicity

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TailInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A computable centered interval for the multicolor binomial tail

The swap mean is between (Q - 1) / 4 and (Q - 1) / 2.  Taking the natural
floor of mean - R / 2 gives an interval of R consecutive integer weights.
The rounding error is at most one, absorbed by R ≥ 4.
-/

namespace SubexponentialSAT.Subexp.TailInterval

open SubexponentialSAT.SubexpSwapMultiplicity
open scoped BigOperators

/-- The mean of the Q - 1 independent swap signs. -/
def mean (r Q : ℕ) : ℚ := (Q - 1 : ℕ) * negativeProbability r

/-- A rational-floor computation, with no choice or search oracle. -/
def centeredStart (μ : ℚ) (R : ℕ) : ℕ := ⌊μ - (R : ℚ) / 2⌋₊

/-- The concrete interval start used for the multicolor matrix. -/
def intervalStart (r Q R : ℕ) : ℕ := centeredStart (mean r Q) R

@[simp] theorem interval_card (r Q R : ℕ) :
    (Finset.Ico (intervalStart r Q R) (intervalStart r Q R + R)).card = R := by
  simp

end SubexponentialSAT.Subexp.TailInterval

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProducedMatrixRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Selecting columns in their physical order cannot increase the rational
rank. The map may omit or repeat columns; no runtime permutation is assumed. -/
namespace SubexponentialSAT.SqrtLog.LayoutRank
open Module

variable {J K V W : Type*} [Fintype J] [Fintype K] [Fintype V] [Fintype W]

def columnSelection (e : W → V) : (V → ℚ) →ₗ[ℚ] (W → ℚ) where
  toFun := fun f w => f (e w)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

end SubexponentialSAT.SqrtLog.LayoutRank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramMagnitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Unsigned component-total budgets for the signed-pair implementation.
These bounds do not infer component size from the absolute signed difference.
The physical arithmetic refinement must prove its total obeys this recurrence. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open scoped BigOperators

/-- The nonnegative recurrence for one scalar numerator. Sign swaps leave this
quantity unchanged, and pair addition/multiplication have no cancellation. -/
def scalarMass (R d h : ℕ) (coefficientMass : ℕ → ℕ) : ℕ :=
  ∑ k ∈ Finset.range (R-d),
    coefficientMass (d+k) * 2^(R-1-(d+k)) * h.choose k

/-- Safe full cleared-constraint budget, including the diagonal denominator. -/
def constraintMassBound (Q R : ℕ) : ℕ := (8*Q)^(2*R) + 2^(R-1)

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarCacheCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The unsigned cache recurrence is executed by a one-bit shift followed by
the original finite little-endian adder. Its representation growth is linear
in the number of cells; no canonical-word assumption is used. -/

/-! One complete cache-row transform, including record parsing and preserving
emission of every newly computed value. -/

/-! Complete reusable cache pass: read one encoded row, compute and emit its
new row, append the end marker, reverse the output, and clear the carry. -/

/-! The number of coefficient-cache rows is runtime unary data. This fixed
loop invokes the complete paid row pass and preserves the current encoded row.
-/

/-! The physical unsigned cache computes the original coefficient recurrence's
natural magnitudes, in ascending degree order. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

def initialCache (R : ℕ) : List (List Bool) := List.replicate R [true]

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! A fixed loop builds the initial all-one cache row from a runtime unary
length. The constant program contains one record, independent of that length. -/

/-! One fixed program builds the complete unsigned H cache from the unary
runtime parameters A and R. No coefficient or initial cache is free input. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A single cached scalar term: three parsed operands, three real signed
multiplications, and one real signed addition. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

def termCost (A B : ℕ) : ℕ := 100000000*(A+B+4)^2

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! Polynomial source-step bounds for the concrete cached scalar arithmetic.
The stream has three actual binary signed operands per summand, not a stream
of precomputed products or an assumed arithmetic callback. -/

/-! Exact unsigned component totals for the same concrete scalar program.
The extra invariant controls cancellation without changing any instruction. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRepresentedRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Polynomial rows generated from represented field operations

The producer uses code words, finite expression constructors, and the supplied
arithmetic callbacks. It never extracts coefficients from an abstract field
value. Inverse constants are computed by finite-field powering. The canonical
coefficient lift is applied only after compiling the source polynomial.
-/

namespace SubexponentialSAT.SubexpRepresentedRows

open SubexpRowInterpolation

variable {C E : Type*} {Q : ℕ}

def sumCode (zero : C) (ps : List (PolynomialCode C)) : PolynomialCode C :=
  ps.foldr PolynomialCode.add (.constant zero)

def productCode (one : C) (ps : List (PolynomialCode C)) : PolynomialCode C :=
  ps.foldr PolynomialCode.mul (.constant one)

end SubexponentialSAT.SubexpRepresentedRows

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Filtered row records for the physical interpolation-code emitter

Inactive zero terms and unit factors are omitted from the emitted records.
This is proved as a polynomial identity, without identifying the two different
expression trees or assuming a desired evaluator result.
-/

namespace SubexponentialSAT.Subexp.UniversalRowSource

open scoped BigOperators
open SubexpRowInterpolation SubexpRepresentedRows

variable {C E : Type*} {Q : ℕ}

def selected (s : Finset (Fin Q)) : List (Fin Q) :=
  (List.finRange Q).filter fun i => decide (i ∈ s)

@[simp] theorem selected_toFinset (s : Finset (Fin Q)) : (selected s).toFinset = s := by
  ext i
  simp [selected]

end SubexponentialSAT.Subexp.UniversalRowSource

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceTyped
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Typed witnesses for the actual interpolation table reads. Cached negative
nodes and inverse differences need only have the right decoded value; no
canonical representation or equality with an arithmetic implementation is
assumed. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped

open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.UniversalRowSource
open SubexponentialSAT.SubexpRepresentedRows SubexponentialSAT.SubexpRowInterpolation

variable {C O : Type*} {Q : ℕ}

variable (encode : C → List Bool)
  (values inverse negative : Fin Q → C)
  (difference : Fin Q → Fin Q → C)

/-- A left inverse is used only to state decoding of raw literals. It is not
executed by the polynomial source program. -/
noncomputable def wordDecode [Nonempty C] (encode : C → List Bool) (decode : C → O) : List Bool → O :=
  fun w => decode (Function.invFun encode w)

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup
open SubexponentialSAT

namespace Scan

def register : Fin 5 → Fin 16 := Fin.castAdd 11
def stack : Fin 7 → Fin 12 := ![6,3,8,9,10,11,4]

end Scan
end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupPorts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native
open SubexponentialSAT

def stack : Fin 12 → Fin 340 := ![233,212,216,337,304,315,316,317,318,319,338,339]

end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpUnaryRangeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed unary range enumerator which physically emits every framed index. -/
namespace SubexponentialSAT.SubexpUnaryRangeProgram

def steps : ℕ → ℕ → ℕ
  | _, 0 => 1
  | j, n+1 => 12*j+23 + steps (j+1) n

end SubexponentialSAT.SubexpUnaryRangeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

abbrev unary (n : ℕ) : List Bool := List.replicate n true

end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native framing and postfix accumulation for complete source rows. The
local bank is relocated as a whole by the leaf controller. No polynomial
value is an instruction or an input to these controllers. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT

abbrev Store := Fin 340 → List Bool

def appendResult (s : Store) : Store :=
  Function.update (Function.update s 287 []) 333
    ((s 333).reverse++s 287++[true,false]).reverse

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPostfixInterpreter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A finite postfix interpreter with linked arithmetic services

The interpreter contains the concrete tag dispatcher and literal loader, two
initialization instructions, and the supplied finite arithmetic instruction
tables. Arithmetic correctness is required as a local Boolean-machine trace
contract; an arithmetic operation is never added to the instruction language.
-/

namespace SubexponentialSAT.SubexpPostfixInterpreter

variable {r s a b : ℕ}

def register : Fin 3 → Fin (3 + r) := Fin.castAdd r
def stack : Fin 4 → Fin (4 + s) := Fin.castAdd s

end SubexponentialSAT.SubexpPostfixInterpreter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpDenseOperandIO
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed finite framing operations at the physical postfix operand port.
These routines preserve the code/depth stacks and all surrounding data. -/

namespace SubexponentialSAT.SubexpDenseOperandIO

def parseRegs : Fin 2 → Fin 16 := Fin.castAdd 14
def parseStacks : Fin 2 → Fin 128 := ![27, 29]

def writeRegs : Fin 3 → Fin 16 := Fin.castAdd 13
def writeStacks : Fin 4 → Fin 128 := ![26, 28, 27, 29]

end SubexponentialSAT.SubexpDenseOperandIO

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpDenseLiteralPadding
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

abbrev smallPorts : Fin 128 → Fin 256 := Fin.castAdd 128

def padRegs : Fin 8 → Fin 16 := Fin.castAdd 8
def padPorts : Fin 3 → Fin 256 := ![99, 21, 29]

end SubexponentialSAT.SubexpDenseLiteralPadding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete finite controllers for source fiber sums and ambient source-row
serialization. Parameters are actual finite programs with paid contracts. -/

/-! A runtime owner-fiber fold of actual serialized polynomial sources. -/

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT

def ownerRegisters : Fin 5 → Fin 16 := Fin.castAdd 11
def ownerStacks : Fin 11 → Fin 340 := ![320,337,321,322,323,324,325,326,327,328,329]

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT
attribute [local simp] Fin.coe_ofNat_eq_mod

def rowState (base : Store) (j : ℕ) (remaining acc : List Bool) : Store :=
  Function.update (Function.update (Function.update base 320 (List.replicate j true))
    331 remaining) 332 acc

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {Witness : Type*}

def emittedBytes (encode : Witness → List Bool) (ws : List Witness) : List Bool :=
  ws.flatMap (fun w => encode w++[true,false])

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

/-! Paid bank relocation and register reset for the native polynomial source
executor. The parameter is a finite BitProgram; the integration selects the
checked polynomial executor, never a polynomial-value instruction. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT

def executorPorts : Fin 256 → Fin 340 := Fin.castAdd 84

def evaluationInput (s : Store) : Store :=
  let s1 := Function.update (Function.update s 21 []) 335 (s 21).reverse
  let s2 := Function.update (Function.update s1 26 []) 336 (s 26).reverse
  Function.update (Function.update s2 333 []) 26 (s 333).reverse

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT
attribute [local simp] Fin.coe_ofNat_eq_mod
variable {Witness : Type*}

def RowProperty (encode : Witness → List Bool) (R : ℕ → Witness → Prop) (W : ℕ) :
    ℕ → List Witness → Prop
  | _, [] => True
  | j, w::ws => R j w ∧ (encode w).length=W ∧ RowProperty encode R W (j+1) ws

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

/-! The bytes produced by the runtime fold are the compiler output of the
same finite sum expression, including the empty-owner zero polynomial. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramInitialize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed, width-generic initialization for the source-row executor. All
zero-array construction and copies are paid; only four output stacks change. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramInitialize
open SubexponentialSAT

def budget (D W : ℕ) : ℕ := 240 * (D+1) * (W+1)

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramInitialize

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramInitializeLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT

def initializationPorts : Fin 256 → Fin 340 := Fin.castAdd 84

def initializeFinish (s : Store) (D W : ℕ) : Store :=
  Function.update (Function.update (Function.update (Function.update s
    243 (List.replicate D true)) 242 (List.replicate (D*W) false))
      192 (List.replicate (D*W) false)) 193 (List.replicate D true)

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpProjectedInterpreter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A finite postfix interpreter with a real literal-projection call

The literal bytes are parsed and pushed by the concrete loader, then passed to
an actual finite projection service before dispatch resumes. Arithmetic and
projection contracts refer to traces of supplied Boolean instruction tables.
-/

namespace SubexponentialSAT.SubexpProjectedInterpreter

open SubexpPostfixInterpreter (register stack )

variable {r s a b c : ℕ}

def baseLabel : Fin 37 → Fin (37 + (2 + (a + (b + c)))) := Fin.castAdd _
def bootLabel (i : Fin 2) : Fin (37 + (2 + (a + (b + c)))) :=
  Fin.natAdd 37 (Fin.castAdd (a + (b + c)) i)
def addLabel (i : Fin a) : Fin (37 + (2 + (a + (b + c)))) :=
  Fin.natAdd 37 (Fin.natAdd 2 (Fin.castAdd (b + c) i))
def mulLabel (i : Fin b) : Fin (37 + (2 + (a + (b + c)))) :=
  Fin.natAdd 37 (Fin.natAdd 2 (Fin.natAdd a (Fin.castAdd c i)))
def loadLabel (i : Fin c) : Fin (37 + (2 + (a + (b + c)))) :=
  Fin.natAdd 37 (Fin.natAdd 2 (Fin.natAdd a (Fin.natAdd b i)))


end SubexponentialSAT.SubexpProjectedInterpreter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRowPostfixInterpreter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The source-row postfix interpreter on the fixed 256-stack workspace.
Only port names change; the checked dispatcher and all service transitions
are retained. Parameters such as R and the field remain encoded data. -/

namespace SubexponentialSAT.SubexpRowPostfixInterpreter

def ports : Equiv.Perm (Fin 256) :=
  ((Equiv.swap 0 26).trans (Equiv.swap 1 28)).trans
    ((Equiv.swap 2 27).trans (Equiv.swap 3 29))

@[simp] theorem ports_zero : ports 0 = 26 := by decide
@[simp] theorem ports_one : ports 1 = 28 := by decide
@[simp] theorem ports_two : ports 2 = 27 := by decide
@[simp] theorem ports_three : ports 3 = 29 := by decide
@[simp] theorem ports_symm_26 : ports.symm 26 = 0 := by decide
@[simp] theorem ports_symm_28 : ports.symm 28 = 1 := by decide
@[simp] theorem ports_symm_27 : ports.symm 27 = 2 := by decide
@[simp] theorem ports_symm_29 : ports.symm 29 = 3 := by decide


end SubexponentialSAT.SubexpRowPostfixInterpreter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The fixed outer source-row controller, including cache initialization,
actual pair-plan search, row traversal, and packed-index cleanup. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT

def preparedSourceStore (s : Store) (D W : ℕ) (ps : List (ℕ × ℕ)) (v N f : ℕ) : Store :=
  Function.update (initializeFinish s D W) 304
    (LayoutSourcePlanLookup.unary (ps.idxOf (v,N+f)))

def RowsClean (s : Store) : Prop :=
  ∀ i∈([205,240,330,334,320,331,332,339] : List (Fin 340)), s i=[]

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramCostBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT

def rowBudgetPolynomial (K L D d B S : ℕ) : ℕ :=
  let T := 2+S*(L+2)
  1000*(2*S+1)^2+S*(K+5*S+3*L+15)+
    300000*(T+1)*(D+1)^3*(d+1)^3*(B+1)^2+
    18*(D*(d*B))+12*S+3*T+67

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramReadiness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native readiness of the extracted source executor after the paid zero-array
initializer. The source dimension is the full count on210; no identification
with an earlier jet-length cache is made. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness
open SubexponentialSAT
open SubexponentialSAT.SubexpRowPostfixInterpreter (ports )
open LayoutSourceRowsProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The only ports hidden or changed by extraction and initialization. -/
def Preserved (i : Fin 256) : Prop :=
  i ≠ 21 ∧ i ≠ 26 ∧ i ≠ 27 ∧ i ≠ 28 ∧ i ≠ 29 ∧
    i ≠ 243 ∧ i ≠ 242 ∧ i ≠ 192 ∧ i ≠ 193

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramRowsModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT
attribute [local simp] Fin.coe_ofNat_eq_mod

def RowWorkClean (s : Store) : Prop :=
  ∀ i∈([27,28,29,287,305,333,335,336] : List (Fin 340)), s i=[]

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram
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

def bodyCost (m k W P : ℕ) := (m+k)*(28*W+34)+140*W+18*P+220

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramLoop.lean

/-! The native unary loop produces all triples in increasing binomial index. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

def loopCost : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0,_,_,_ => 2
  | n+1,k,W,P => bodyCost n k W P + 2 + loopCost n (k+1) W P

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramFinish.lean

/-! Initial unary copy/parity and final stream reversal are native paid calls. -/

/-! Complete cache-to-triple primitive program with all scans and copies paid. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

def prepareCost (N A W P : ℕ) : ℕ :=
  9*N+3*A+loopCost N 0 W P+3*(N*(8*W+2*P+9))+21

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_BasisTransposePlanProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical transpose read-plan generation

Two unary countdowns visit columns and rows in decreasing order. Each visit
constructs the unary physical index by repeated copying and emits one actual
framed record. Prepending these visits produces the increasing transpose
read order directly. All counters are runtime stacks and the code is fixed.
-/

namespace SubexponentialSAT.Subexp.BasisTransposePlanProgram

def unary (n : ℕ) : List Bool := List.replicate n true

end SubexponentialSAT.Subexp.BasisTransposePlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MismatchPlanSpec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical mismatch filter on the exact one-hot word representation. -/

namespace SubexponentialSAT.Subexp.MismatchPlanProgram

def oneHot {r : ℕ} (a : Fin r) : List Bool :=
  List.ofFn (fun c : Fin r => decide (a = c))

end SubexponentialSAT.Subexp.MismatchPlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramSourceCall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT

def sourcePorts : Fin 320 → Fin 340 := Fin.castAdd 20

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowSourceBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial bounds for the actual nested row-data and source emitters. -/

namespace SubexponentialSAT.Subexp.UniversalRowSourceBound

def factorBytes (S : ℕ) := 4 * S + 2
def factorsBytes (S : ℕ) := 1 + (2 * factorBytes S + 2) * S
def termBytes (S : ℕ) := 4 * S + 2 + factorsBytes S
def rowBytes (S : ℕ) := 2 * S + 2 + (2 * termBytes S + 2) * S
def inputBound (S : ℕ) := 2 * S + rowBytes S + 1
def factorCallbackBound (S : ℕ) := (28 * S + 60) * S + 9 * S + 80 * S + 140
def factorLoopBound (S : ℕ) := S * (6 * S + factorCallbackBound S + 7)
def sourceLengthBound (S : ℕ) := 300 * inputBound S ^ 2

end SubexponentialSAT.Subexp.UniversalRowSourceBound

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramStaging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The source numerator uses empty scalar work tapes5/10. The polynomial
executor retains its modulus/width there. Two reversible transfers isolate
these phases without touching the native high arithmetic cache. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT
attribute [local simp] Fin.coe_ofNat_eq_mod

def clearedSourceStore (s : Store) : Store := Function.update (Function.update s 5 []) 10 []
def stagedSourceStore (s : Store) : Store :=
  Function.update (Function.update (clearedSourceStore s) 335 (s 5).reverse) 336 (s 10).reverse

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafAssignmentMergeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed physical scan merges a current-head assignment with the bucket
representative, keeping the original ambient coordinate order. -/
namespace SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram

open SubexponentialSAT

def merge : List Bool → List Bool → List Bool → List Bool
  | [], _, _ => []
  | a::as, hs, bs => (if hs.headD false then a else bs.headD false) ::
      merge as hs.tail bs.tail

@[simp] theorem merge_length (a h b : List Bool) : (merge a h b).length = a.length := by
  induction a generalizing h b with
  | nil => rfl
  | cons a as ih => simp [merge,ih]

abbrev tapes (a h b out tmp : List Bool) : Fin 5 → List Bool := ![a,h,b,out,tmp]

end SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafWeightProgramNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserving physical wrapper for the Boolean head-weight scan. The actual
ring zero and one are arbitrary runtime words, so the ring degree is dynamic. -/
namespace SubexponentialSAT.SqrtLog.LeafWeightProgram.Native

open SubexponentialSAT

abbrev tapes (a s h zero one x y z out : List Bool) : Fin 10 → List Bool :=
  ![a,s,h,zero,one,x,y,z,[],out]

@[simp] theorem update5 (a s h zero one x y z out v : List Bool) :
    Function.update (tapes a s h zero one x y z out) 5 v =
      tapes a s h zero one v y z out := by
  funext i; fin_cases i <;> simp [tapes]
@[simp] theorem update6 (a s h zero one x y z out v : List Bool) :
    Function.update (tapes a s h zero one x y z out) 6 v =
      tapes a s h zero one x v z out := by
  funext i; fin_cases i <;> simp [tapes]
@[simp] theorem update7 (a s h zero one x y z out v : List Bool) :
    Function.update (tapes a s h zero one x y z out) 7 v =
      tapes a s h zero one x y v out := by
  funext i; fin_cases i <;> simp [tapes]
@[simp] theorem update9 (a s h zero one x y z out v : List Bool) :
    Function.update (tapes a s h zero one x y z out) 9 v =
      tapes a s h zero one x y z v := by
  funext i; fin_cases i <;> simp [tapes]

end SubexponentialSAT.SqrtLog.LeafWeightProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafAssignmentMergeProgramNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserving shell for the assignment merge. Only output9 and registers
change; the masters and both reserved words are preserved. -/
namespace SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram.Native

open SubexponentialSAT

abbrev tapes := LeafWeightProgram.Native.tapes

def stackMap : Fin 5 → Fin 10 := ![5,6,7,9,8]

end SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The primitive integer accumulator used after each marked-clause count.
Both operands have runtime lengths. The fixed instruction table adds them
exactly and restores little-endian orientation; no arithmetic instruction or
precomputed mass is admitted into the machine model. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Mass

structure Ports (r s : ℕ) where
  register : Fin 8 → Fin r
  stack : Fin 3 → Fin s
  register_injective : Function.Injective register
  stack_injective : Function.Injective stack

end SubexponentialSAT.SqrtLog.LeafProgram.Mass

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafBranchProgramRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual overflow-controlled aggregation. The looser quadratic-in-branches
bound accommodates arbitrary leading zeroes in native binary answers. -/
namespace SubexponentialSAT.SqrtLog.LeafBranchProgram
variable {R S : ℕ}

def rankSum (value : ℕ → ℕ) (start count : ℕ) : ℕ :=
  ((List.range' start count).map value).sum
@[simp] theorem rankSum_zero (value : ℕ → ℕ) (start : ℕ) : rankSum value start 0 = 0 := rfl
@[simp] theorem rankSum_succ (value : ℕ → ℕ) (start count : ℕ) :
    rankSum value start (count+1) = value start + rankSum value (start+1) count := by
  simp [rankSum, List.range'_succ]

end SubexponentialSAT.SqrtLog.LeafBranchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafFactorDispatchProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid factor classification and source lookup. IDs are runtime data. -/
namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT

abbrev unary (n : ℕ) := List.replicate n true

def cmpRegs : Fin 4 → Fin 8 := Fin.castAdd 4
def cmpPorts : Fin 2 → Fin 16 := ![8,9]

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramFetch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The selected payload is fetched by scanning the actual source record list. -/
namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT

def masterPort (marked : Bool) : Fin 16 := if marked then 1 else 0
def fetchRegs : Fin 3 → Fin 8 := Fin.castAdd 5
def fetchPorts (marked : Bool) : Fin 6 → Fin 16 := ![masterPort marked,10,6,11,12,15]

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramChoose
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT

def selectedPayload (rows clauses : List (List Bool)) (hasMarked : Bool) (m f : ℕ) : List Bool :=
  if f < rows.length then rows.getD f []
  else if hasMarked && decide (f=rows.length) then clauses.getD m [] else []

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadFactorsProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Factor head selection uses the full original table and a paid ambient offset. -/
namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT

abbrev unary (n : ℕ) := List.replicate n true
abbrev zeros (n : ℕ) := List.replicate n false

def wordRegs : Fin 5 → Fin 16 := Fin.castAdd 11
def wordPorts : Fin 10 → Fin 64 := ![33,40,38,16,17,36,18,19,20,21]

def lookupCost (j W : ℕ) := j*(14*W+17)+15*W+22


end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramVisit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT

def visitBound (A j W z : ℕ) :=
  lookupCost (A + j) W + 9 * (A + j) + 12 * j + 10 * z + 2 * W + 46

def predicate (rows : List (List Bool)) (A z j : ℕ) : Bool :=
  (rows.getD (A + j) []).getD z false

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT

def chosenIds (p : ℕ → Bool) (n : ℕ) : List ℕ := (List.range n).filter p
def count (p : ℕ → Bool) (n : ℕ) : ℕ := (chosenIds p n).length

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT

def baseStacks (rows : List (List Bool)) (A N W z : ℕ) : Fin 64 → List Bool :=
  fun i => if i=30 then unary N else if i=31 then unary A else if i=32 then unary z
    else if i=33 then rows.flatten else if i=38 then unary W else []

def preparedStacks (rows : List (List Bool)) (A N W z : ℕ) : Fin 64 → List Bool :=
  Function.update (Function.update (baseStacks rows A N W z) 39 (unary N)) 0 [false]

def budget (A N M W z : ℕ) := N*(visitBound A M W z+2)+7*N+26

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramAddress
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The node index and palette size are runtime inputs. This fixed program
initializes the head countdown and computes the first physical color address
by real unary multiplication. Subsequent heads increment that address. -/
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Address
open SubexponentialSAT.Subexp.BasisTransposePlanProgram

def budget (r t : ℕ) := t*(7*r+14)+7*r+13

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Address

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramStorage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid, isolated service calls in the leaf head-builder's reserved bank.
The entire local service bank is moved to340..627. In particular a matrix
entry bank cannot overwrite the persistent ring tables below340. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

def temporary : Fin 768 := 659

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Per-node paid bootstrap: address multiplication, actual plan-record
counting, and construction of the integer interpolation coefficient cache. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
def addressInputs : List (Fin 768 × Fin 7) := [(130,0),(307,2)]
def addressOutputs : List (Fin 7 × Fin 768) := [(3,648),(4,649)]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBoundsPrepare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed polynomial cost of actual head-ID, support-mask, and factor-ID
preparation. Bounds include the real isolated-bank copy/cleanup costs. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds

 def preparationSize (n N : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ) : ℕ :=
  n+N+rows.flatten.length+rows.length+low.length+W+z+2

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact runtime parameter semantics. Every definition below uses natural
arithmetic; the executable refinements are separate from these specifications.
The original ambient dimension is retained through high-incidence branching. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram

structure Parameters where
  L : ℕ
  w : ℕ
  s : ℕ
  r : ℕ
  Q : ℕ
  R : ℕ
  epsilonDen : ℕ
  t : ℕ
  d : ℕ
  N : ℕ
  J : ℕ
  deriving DecidableEq, Repr

def extensionDegree (Q : ℕ) : ℕ := Nat.size Q + 1

end SubexponentialSAT.SqrtLog.LeafParametersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native runtime leaf parameter production, integer guards, and paid setup.
The former composition modules are import-only compatibility shims. -/


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramBankRoots -/

/-! A fixed ten-comparison bit guard. All operands are runtime binary words.
This module states their data relation separately from parameter production. -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute

def guardStacks (i : Fin 20) : Fin 77 := ⟨44+i.val,by omega⟩

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramCircuitBudget -/


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramFinalize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Add precisely the uncovered-variable neutral factors. Inputs are the
unary outputs of the physical scope and variable scans. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Finalize

def neutralArity (a u : ℕ) : ℕ := max a (if u=0 then 0 else 1)
end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Finalize

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The runtime scan equals the statistics of the actual residual scope family,
with precisely one neutral singleton for each unused free coordinate. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open scoped BigOperators
open LeafStatisticsProgram

/-- The native mask uses `true` for a removed (high-incidence) coordinate. -/
def highMask (mask : List Bool) : Finset (Fin mask.length) :=
  Finset.univ.filter fun i => mask.get i = true

abbrev Free (mask : List Bool) := {v : Fin mask.length // v ∉ highMask mask}

@[simp] theorem mem_highMask (mask : List Bool) (i : Fin mask.length) :
    i ∈ highMask mask ↔ mask.get i = true := by simp [highMask]

@[simp] theorem free_bit (mask : List Bool) (i : Free mask) :
    mask.get i.val = false := by
  have h := i.property
  simp only [mem_highMask] at h
  cases hb : mask.get i.val <;> simp_all

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact owner order of the neutral factors emitted by the native scan. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

/-- Free owners in increasing original-coordinate order. -/
def lowOwners : ℕ → List Bool → List ℕ
  | _, [] => []
  | v, high :: rest => if high then lowOwners (v+1) rest else v :: lowOwners (v+1) rest

/-- Forward numbering is independent of the reversed order of emitted records. -/
def numbered : ℕ → List ℕ → List (ℕ × ℕ)
  | _, [] => []
  | z, v :: rest => (v,z) :: numbered (z+1) rest

theorem numbered_mem (owners : List ℕ) :
    ∀ z u e, (u,e) ∈ numbered z owners ↔
      ∃ i : Fin owners.length, owners.get i = u ∧ z+i.val = e := by
  induction owners with
  | nil => intros; simp [numbered]
  | cons v vs ih =>
    intro z u e
    simp [numbered, ih, Fin.exists_fin_succ, Nat.add_comm,
      Nat.add_left_comm, eq_comm, and_comm]

theorem numbered_factor_ge (owners : List ℕ) (z u e : ℕ)
    (hp : (u,e) ∈ numbered z owners) : z ≤ e := by
  obtain ⟨i, _, hi⟩ := (numbered_mem owners z u e).mp hp
  omega

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIntervalStart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Integer arithmetic for the exact centered interval used by the layout. -/

namespace SubexponentialSAT.SubexpIntervalStart

/-- This is computed using two truncated predecessors, products, truncated
subtraction, and natural division. -/
def value (r Q R : ℕ) : ℕ := ((Q - 1) * (r - 1) - R * r) / (2 * r)

theorem value_eq_intervalStart (r Q R : ℕ) (hr : 0 < r) :
    value r Q R = Subexp.TailInterval.intervalStart r Q R := by
  have hr1 : 1 ≤ r := hr
  have hr0 : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr)
  have hcommon : ((Q - 1 : ℕ) : ℚ) * (((r : ℚ) - 1) / (2 * r)) - (R : ℚ) / 2 =
      ((((Q - 1) * (r - 1) : ℕ) : ℚ) - ((R * r : ℕ) : ℚ)) / ((2 * r : ℕ) : ℚ) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hr1, Nat.cast_one]
    field_simp
  unfold Subexp.TailInterval.intervalStart Subexp.TailInterval.centeredStart
    Subexp.TailInterval.mean SubexpSwapMultiplicity.negativeProbability
  rw [hcommon, Nat.floor_div_natCast, Nat.floor_sub_natCast, Nat.floor_natCast]
  rfl

end SubexponentialSAT.SubexpIntervalStart

end OAI.Algorithms
end


