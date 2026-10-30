-- Prove2me | Definitions.Def_OAIQ081S072
-- name    : OAIQ081S072
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:00:43.370836+00:00
-- url     : https://prove2.me/theorems/9e53f971-a081-4f58-944a-2c5fc139a66b
-- title:
--   Definitions bundle OAIQ081S072 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 60 declarations of OpenAI's Lean: 32 definitions, 2 inductive types or structures and 26 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.body`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.findOwner`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.incidenceValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.loop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutHeadPullback.pullback`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.emitRow`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.frame`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.body`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.callback`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.emitMatch`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.finish`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.loop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.pairBytes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.pairPayload`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.push`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.scan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.scanCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.stream`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.NativePacking.Spec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels.Spec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels.Spec.packing`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutScaledMatrices.sourceRow`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.headColorBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Problem.incidences`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Address.address`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingVertexLabels.labelRecords`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingVertexLabels.planPayload`, `OAI.Algorithms.SubexponentialSAT.SubexpAnnihilation.rowForMatrices`, `OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation.mismatchRowPath`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LayoutFiberSumProgram`, `SubexponentialSAT_SqrtLog_LayoutFiberSumProgramLoop`, `SubexponentialSAT_SqrtLog_LayoutFiberSumProgramMove`, `SubexponentialSAT_SqrtLog_LayoutFiberSumProgramNative`, `SubexponentialSAT_SqrtLog_LayoutHeadPullback`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgramPrimitives`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgramRow`, `SubexponentialSAT_SqrtLog_LayoutNumeratorBridge`, `SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgram`, `SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramEmit`, `SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramLoop`, `SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramParse`, `SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramVisit`, `SubexponentialSAT_SqrtLog_LayoutProgramLabels`, `SubexponentialSAT_SqrtLog_LayoutProgramNativePacking`, `SubexponentialSAT_SqrtLog_LayoutProgramPackLabels`, `SubexponentialSAT_SqrtLog_LayoutScaledMatrices`, `SubexponentialSAT_SqrtLog_PackingCallerProgramModel`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputAddress`, `SubexponentialSAT_SqrtLog_PackingRelations`, `SubexponentialSAT_SubexpAnnihilation`, `SubexponentialSAT_SubexpRowInterpolation`, `SubexponentialSAT_SubexpSetupStorage`, `SubexponentialSAT_Subexp_AssignmentAlphabetSemantics`, `SubexponentialSAT_Subexp_AssignmentLabelSerialization`, `SubexponentialSAT_Subexp_PackingVertexLabels`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S047`, `OAIQ081S050`, `OAIQ081S051`, `OAIQ081S053`, `OAIQ081S054` and `OAIQ081S055` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S089`, `OAIQ081S090`, `OAIQ081S091`, `OAIQ081S092`, `OAIQ081S095`, `OAIQ081S096`, `OAIQ081S097` and `OAIQ081S098`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.row_meaning` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.sourceCode_decode`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.row_meaning` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.sourceCode_decode`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S047
import Definitions.Def_OAIQ081S050
import Definitions.Def_OAIQ081S051
import Definitions.Def_OAIQ081S053
import Definitions.Def_OAIQ081S054
import Definitions.Def_OAIQ081S055

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutFiberSumProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

def body (entry : Code) : Code := .seq readIndex (.seq entry (.seq addEntry clearColumn))

def loop (entry : Code) : Code := .seq peek (.while 15 (.seq (body entry) peek))

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingVertexLabels
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Gathering the actual assignment type at every vertex before packing. -/

namespace SubexponentialSAT.Subexp.PackingVertexLabels

open BitProgram StructuredCalls MatrixProgramSupport

def planPayload (plan : List ℕ) : List Bool :=
  Encoding.frame (ProgramEncoding.encodeRecords (GatherProgram.indexRecords plan))

def labelRecords (rows : List (List Bool)) (plans : List (List ℕ)) (start : ℕ) :
    List BucketProgram.Record :=
  plans.zipWith (fun plan i => (GatherProgram.gathered rows plan, List.replicate i true))
    (List.range' start plans.length)

@[simp] theorem labelRecords_nil (rows : List (List Bool)) (start : ℕ) :
    labelRecords rows [] start = [] := rfl

@[simp] theorem labelRecords_length (rows : List (List Bool))
    (plans : List (List ℕ)) (start : ℕ) :
    (labelRecords rows plans start).length = plans.length := by
  simp [labelRecords]

end SubexponentialSAT.Subexp.PackingVertexLabels

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramEmit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

abbrev push := @SubexponentialSAT.Subexp.TupleProgram.pushConst 5 11

def emitMatch : Code := .seq (.call (StackRoutines.copyProgram 7 8 6 0 1))
  (.seq (push 8 0 false) (push 9 0 true))

def finish : Code := .seq (.ite 4 emitMatch (.base .skip))
  (.seq (push 7 0 true) normalize)

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramParse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def pairBytes (v f : ℕ) : List Bool :=
  ProgramEncoding.encodeRecords [unary v,unary f]
def pairPayload (v f : ℕ) : List Bool := Encoding.frame (pairBytes v f)

@[simp] theorem pairBytes_length (v f : ℕ) : (pairBytes v f).length=2*v+2*f+5 := by
  simp [pairBytes,ProgramEncoding.encodeRecords,Encoding.encodeList,Encoding.length_frame]
  omega

@[simp] theorem pairPayload_length (v f : ℕ) : (pairPayload v f).length=4*v+4*f+11 := by
  simp [pairPayload,Encoding.length_frame]
  omega

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramVisit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def callback : Code := .seq parseOwner (.seq compareOwner finish)

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def stream (ps : List (ℕ × ℕ)) : List Bool :=
  Encoding.encodeList (fun p => pairPayload p.1 p.2) ps

def scanCost (query : ℕ) : ℕ → List (ℕ × ℕ) → ℕ
  | _, [] => 1
  | index, p::ps => 6*(pairPayload p.1 p.2).length+callbackCost query index p+6+
      scanCost query (index+1) ps

def body : Code := .seq outerRead (.seq callback popScan)
def loop : Code := .while 0 body
def scan : Code := .seq popScan loop

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def command : Code := .seq copySource (.seq scan (.seq (clear 7) restore))
def program := compiled command 0 10

def budget (query : ℕ) (ps : List (ℕ × ℕ)) : ℕ :=
  7*(stream ps).length+scanCost query 0 ps+2*ps.length+
    3*(encodeIndices (fiberIndices query 0 ps)).length+13

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutFiberSumProgramMove
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def findOwner : Code := .call (ProgramLinking.liftProgram
  LayoutOwnerFiberProgram.program ownerRegisters ownerStacks)

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutFiberSumProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

def command (entry : Code) : Code := .seq parkColumn
  (.seq (.seq findOwner clearCount) (.seq (loop entry) finish))

def budget (T B J query : ℕ) (ps : List (ℕ × ℕ)) : ℕ :=
  let count := (LayoutOwnerFiberProgram.fiberIndices query 0 ps).length
  LayoutOwnerFiberProgram.budget query ps+18*query+2*count+39+
    count*(T+5*J+12+25000*((count+1)*(B+2)+3)^2+9*(B+2))

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed stack and framing adapters for direct construction of all incidence
rows. The adapters expose native instruction counts and exact stack effects. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev frame {s : ℕ} (src dst tmp : Fin s) (htd : tmp ≠ dst) : Code s :=
  lift8 (Subexp.MatrixProgramSupport.emitFrame src dst tmp htd) src dst

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

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

theorem basis_eval_other (u : NodeUnits node) (s : Finset I)
    {i j : I} (hij : i ≠ j) (hj : j ∈ s) :
    (basis u s i).eval (node j) = 0 := by
  simp only [basis, Polynomial.eval_mul, Polynomial.eval_prod]
  have hprod : (∏ k ∈ s.erase i, (basisDivisor u i k).eval (node j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij.symm, hj⟩)
      (basisDivisor_eval_right u i j)
  rw [hprod, mul_zero]

theorem basis_eval_node (u : NodeUnits node) (s : Finset I) (i j : I) (hj : j ∈ s) :
    (basis u s i).eval (node j) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, basis_eval_other u s hij hj]

theorem correctionPolynomial_eval_node (u : NodeUnits node) (s : Finset I) (d : I → E)
    {j : I} (hj : j ∈ s) :
    (correctionPolynomial u s d).eval (node j) = d j := by
  simp [correctionPolynomial, Polynomial.eval_finsetSum, basis_eval_node u s _ _ hj, hj]

variable [DecidableEq V]

theorem columnCorrection_eval_node (Y : Finset V) (A : V → Finset I)
    (u : NodeUnits node) (d : V → I → E) {y : V} (hy : y ∈ Y)
    {i : I} (hi : i ∈ A y) :
    (columnCorrection Y A u d y).eval (node i) = d y i := by
  simp only [columnCorrection, ite_eq_left hy]
  exact correctionPolynomial_eval_node u (A y) (d y) hi

section Mismatches

variable [Fintype I] [Fintype V] [DecidableEq C]

theorem mismatchCorrection_of_not_mem (head : V → I → C) (σ : I → C) (R : ℕ)
    (u : NodeUnits node) (d : V → I → E) (y : V)
    (hy : y ∉ correctionColumns head σ R) :
    mismatchCorrection head σ R u d y = 0 :=
  columnCorrection_of_not_mem _ _ _ _ hy

theorem mismatchCorrection_eval_node (head : V → I → C) (σ : I → C) (R : ℕ)
    (u : NodeUnits node) (d : V → I → E) (y : V)
    (hy : (mismatchPositions head σ y).card ≤ R) (t : I) (ht : head y t ≠ σ t) :
    (mismatchCorrection head σ R u d y).eval (node t) = d y t := by
  apply columnCorrection_eval_node
  · exact (mem_correctionColumns head σ R y).mpr hy
  · exact (mem_mismatchPositions head σ y t).mpr ht

/-- Each other-color side uses the same polynomial and its unique prescription at `t`. -/
theorem mismatchCorrection_eval_other_color (head : V → I → C) (σ : I → C) (R : ℕ)
    (u : NodeUnits node) (d : V → I → E) (y : V)
    (hy : (mismatchPositions head σ y).card ≤ R) (t : I)
    (g : C) (hg : g ≠ σ t) (hyg : head y t = g) :
    (mismatchCorrection head σ R u d y).eval (node t) = d y t :=
  mismatchCorrection_eval_node head σ R u d y hy t (hyg ▸ hg)

/-- The actual polynomial row formed from all mismatch corrections. -/
noncomputable def mismatchRowPath (v : V) (head : V → I → C) (σ : I → C) (R : ℕ)
    (u : NodeUnits node) (d : V → I → E) : V → Polynomial E :=
  rowPath v (mismatchCorrection head σ R u d)

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutHeadPullback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Pullback of a head-coherent incidence layout to the original variables. -/

namespace SubexponentialSAT.SqrtLog.LayoutHeadPullback

open scoped BigOperators
open LayoutPullback LayoutExactBuckets

variable {I V F G O : Type*}
variable [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
variable [Fintype G] [DecidableEq G] [CommRing O]

/-- An actual copy layout whose head labels are induced by `owner` gives an
original-variable layout. All constraints remain integer fiber sums. -/
noncomputable def pullback {Q R : ℕ} (owner : I → V) (factor : I → F)
    (head : Fin Q → V → G)
    (C : Layout.Data (O := O) (G := G) (id : I → I) factor Q R)
    (hhead : ∀ t i, C.head t i = head t (owner i)) :
    Layout.Data (O := O) (G := G) owner factor Q R where
  node := C.node
  units := C.units
  head := head
  color := C.color
  row := fun i => row owner (C.row i)
  row_origin := by
    intro i v
    apply LayoutPullback.row_origin owner (C.row i) i
    intro j
    simpa [Pi.single_apply, eq_comm] using C.row_origin i j
  row_degree := fun i v => LayoutPullback.row_degree owner (C.row i) R
    (C.row_degree i) v
  rowCount := C.rowCount
  constraints := fun t g => pulledConstraints
    (headOwner owner (C.head t) (head t) (hhead t) g) (C.constraints t g)
  locality := by
    intro t i g hg
    have h := killsIntegerKernel_pullback
      (headOwner owner (C.head t) (head t) (hhead t) g)
      (C.constraints t g)
      (fun j : {j : I // C.head t j = g} => (C.row i j.val).eval (C.node t))
      (C.locality t i g hg)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext v
    rw [row_eval, row_restrict owner (C.head t) (head t) (hhead t) g]

end SubexponentialSAT.SqrtLog.LayoutHeadPullback

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpAnnihilation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Simultaneous row annihilation for the multicolor layout

Section 3.3 of `source/subexponential-sat.txt`.  At a fixed interpolation
position, the same row annihilates every color different from its slot color.
The old two-color modules are preserved and used only for generic finite-sum
lemmas.
-/

namespace SubexponentialSAT.SubexpAnnihilation

open scoped BigOperators
open Matrix

section InterpolatedRows

open MulticolorTypes SubexpRowInterpolation

variable {F E : Type*} [Ring F] [CommRing E] {r Q Δ : ℕ}
variable {node : Fin Q → E}

/-- The explicit multicolor polynomial row for a supplied matrix family. -/
noncomputable def rowForMatrices (φ : F →+* E)
    (M : (t : Fin Q) → (g : Fin r) → (i : Fin Δ) →
      Matrix (Joint t g i) (Joint t g i) F)
    (u : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ)
    (units : NodeUnits node) : UniversalType r Q Δ → Polynomial E :=
  mismatchRowPath u (fun y => y.head) (u.slot i) R units
    (matrixPrescription φ M u i)

/-- The same interpolated row annihilates every other color, provided the
actual matrix family has the mismatch support asserted in equation (3.6). -/
theorem rowForMatrices_annihilates_of_fixed (φ : F →+* E)
    (M : (t : Fin Q) → (g : Fin r) → (i : Fin Δ) →
      Matrix (Joint t g i) (Joint t g i) F)
    (u : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ)
    (units : NodeUnits node)
    (hM : ∀ t g i (a b : Joint t g i), M t g i a b ≠ 0 →
      (mismatchPositions (fun y : UniversalType r Q Δ => y.head)
        (a.val.slot i) b.val).card ≤ R)
    (t : Fin Q) (g : Fin r) (hg : g ≠ u.slot i t)
    (z : UniversalType r Q Δ → F)
    (hz : ∀ y, y.head t ≠ g → z y = 0)
    (hfix : M t g i *ᵥ (fun y : Joint t g i => z y) =
      fun y : Joint t g i => z y) :
    (fun y => (rowForMatrices φ M u i R units y).eval (node t))
      ⬝ᵥ (fun y => φ (z y)) = 0 := by
  classical
  unfold rowForMatrices mismatchRowPath
  rw [eval_rowPath]
  apply typeBlock_annihilation t i u g hg
    (correctionColumns (fun y => y.head) (u.slot i) R) ((M t g i).map φ)
  · intro y hy
    simp only [hz y hy, map_zero]
  · intro y hy
    rw [mismatchCorrection_of_not_mem _ _ _ _ _ _ hy]
    simp
  · intro hu y hne
    apply (mem_correctionColumns (fun y => y.head) (u.slot i) R y.val).mpr
    apply hM t g i ⟨u, hu, hg.symm⟩ y
    intro hzero
    exact hne (by simp only [Matrix.map_apply, hzero, map_zero])
  · intro y hy hyt
    have hcard : (mismatchPositions (fun y : UniversalType r Q Δ => y.head)
        (u.slot i) y).card ≤ R :=
      (mem_correctionColumns (fun y : UniversalType r Q Δ => y.head)
        (u.slot i) R y).mp hy
    exact (mismatchCorrection_eval_other_color
      (fun y : UniversalType r Q Δ => y.head) (u.slot i) R units
      (matrixPrescription φ M u i) y hcard t g hg hyt).trans
        (matrixPrescription_on_side φ M u i y t g hyt)
  · exact Annihilation.map_fixedVector φ _ _ hfix

end InterpolatedRows

end SubexponentialSAT.SubexpAnnihilation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutScaledMatrices
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Cleared integer matrices and exact ring-valued source rows

The rational spectral argument will supply integer numerators `N` and a
power-of-two denominator `d`. Over the target coefficient ring only the
unit representing `d` is inverted. Exact integer equations `d I - N`
therefore imply the fixed-vector equations needed by the original
multicolor row construction, without a map from `ℚ` to the target ring.
-/

namespace SubexponentialSAT.SqrtLog.LayoutScaledMatrices

open scoped BigOperators
open Matrix

section SourceRows

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpRowInterpolation

variable {O : Type*} [CommRing O] {r Q Δ : ℕ}
variable {node : Fin Q → O}

noncomputable def sourceRow (N : Numerators r Q Δ) (denom : Oˣ)
    (a : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ)
    (units : NodeUnits node) : UniversalType r Q Δ → Polynomial O :=
  SubexponentialSAT.SubexpAnnihilation.rowForMatrices (RingHom.id O)
    (fun t g j => unitScaled denom (N t g j)) a i R units

/-- This is the actual multicolor path from the immutable library, with
cleared integer source constraints and a unit denominator. -/
theorem sourceRow_annihilates
    (N : Numerators r Q Δ) (d : ℤ) (denom : Oˣ)
    (hdenom : (denom : O) = (d : O))
    (a : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ) (units : NodeUnits node)
    (hsupport : ∀ t g j (a b : Joint t g j), N t g j a b ≠ 0 →
      (mismatchPositions (fun y : UniversalType r Q Δ => y.head)
        (a.val.slot j) b.val).card ≤ R)
    (t : Fin Q) (g : Fin r) (hg : g ≠ a.slot i t)
    (z : UniversalType r Q Δ → ℤ)
    (hz : ∀ y, y.head t ≠ g → z y = 0)
    (hconstraint : clearedDefect d (N t g i) *ᵥ
        (fun y : Joint t g i => z y) = 0) :
    (∑ y, (sourceRow N denom a i R units y).eval (node t) * (z y : O)) = 0 := by
  have hs : ∀ t g j (a b : Joint t g j), unitScaled denom (N t g j) a b ≠ 0 →
      (mismatchPositions (fun y : UniversalType r Q Δ => y.head)
        (a.val.slot j) b.val).card ≤ R := by
    intro t g j a b hab
    apply hsupport t g j a b
    intro heq
    apply hab
    simp [unitScaled, heq]
  have hf := fixed_of_clearedDefect d denom hdenom (N t g i)
    (fun y : Joint t g i => z y) hconstraint
  have h := SubexponentialSAT.SubexpAnnihilation.rowForMatrices_annihilates_of_fixed
    (RingHom.id O) (fun t g j => unitScaled denom (N t g j))
    a i R units hs t g hg (fun y => (z y : O))
    (by intro y hy; simp [hz y hy]) hf
  simpa only [sourceRow, RingHom.id_apply, dotProduct] using h

end SourceRows

end SubexponentialSAT.SqrtLog.LayoutScaledMatrices

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutNumeratorBridge
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# From the rational spectral matrix to the integer constraint family

The integer constraints are literally `d I - N`. Their rational range has
exactly the dimension of `I - M`, and the same numerators supply the ring
row construction from `LayoutScaledMatrices`.
-/

namespace SubexponentialSAT.SqrtLog.LayoutNumerator

open scoped BigOperators
open Matrix Module
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.BinomialInterpolation SubexponentialSAT.Subexp.MatrixSupport
open LayoutScaledMatrices

variable {r Q Δ : ℕ}

/-- The explicit integer numerators now discharge the support hypothesis of
the existing ring-valued interpolation rows. -/
theorem family_sourceRow_annihilates
    {O : Type*} [CommRing O] {node : Fin Q → O}
    (A R : ℕ) (denom : Oˣ) (hdenom : (denom : O) = (denominator R : O))
    (a : UniversalType r Q Δ) (i : Fin Δ)
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node)
    (t : Fin Q) (g : Fin r) (hg : g ≠ a.slot i t)
    (z : UniversalType r Q Δ → ℤ)
    (hz : ∀ y, y.head t ≠ g → z y = 0)
    (hconstraint : clearedDefect (denominator R) (joint i t g A R) *ᵥ
      (fun y : Joint t g i => z y) = 0) :
    (∑ y, (sourceRow (family r Q Δ A R) denom a i R units y).eval (node t) *
      (z y : O)) = 0 := by
  exact sourceRow_annihilates (family r Q Δ A R) (denominator R) denom hdenom
    a i R units (fun t g j u v h => family_support A R t g j u v h)
    t g hg z hz hconstraint

end SubexponentialSAT.SqrtLog.LayoutNumerator

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentAlphabetSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual tuple-generator order is retained in the initializer alphabet. -/

namespace SubexponentialSAT.Subexp.AssignmentAlphabetSemantics

open OneHotAlphabetProgram MulticolorTypes

@[simp] theorem wordBytes_length (r Q : ℕ) : (wordBytes r Q).length = r ^ Q := by
  rw [wordBytes, TupleProgram.generated_count, rows_eq_alphabet]
  simp

end SubexponentialSAT.Subexp.AssignmentAlphabetSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramPackLabels
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Packing from physically produced label records. This route accepts the
incidence pair-gatherer's type labels directly, avoiding reconstruction of a
factor-to-incidence scope table. The fixed program computes blocks, uncovered
coordinates, metadata, storage order, and inverse addresses. It does not
assume any of those outputs. Label and universal-type byte production remain
explicit upstream obligations. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels

open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

structure Spec (U : Type*) [DecidableEq U] where
  params : PackingFrontend.Params
  types : FiniteEnumeration U
  label : Fin params.D → U
  encodeType : U → List Bool
  encodeType_injective : Function.Injective encodeType

namespace Spec

variable {U : Type*} [DecidableEq U]

/-- The packing algorithm is the existing executable bucket/minimum/index
construction applied only to the represented input labels and type list. -/
def packing (s : Spec U) : PackingData (Fin s.params.D) U :=
  ⟨⟨List.finRange s.params.D, List.nodup_finRange _, List.mem_finRange⟩, s.types, s.label⟩

@[simp] theorem packing_vertices (s : Spec U) : s.packing.vertices.values = List.finRange s.params.D := rfl
@[simp] theorem packing_label (s : Spec U) : s.packing.label = s.label := rfl
@[simp] theorem packing_types (s : Spec U) : s.packing.types = s.types := rfl

end Spec

end SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutFiberSumProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Discharge the fiber loop's callback by the concrete integer-entry machine.
All remaining assumptions describe its actual caches and numerical bounds. -/
namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.ConstructivePacking RowSelectionProgram

def incidenceValue {r Q D : ℕ} (P : PackingData (Fin D) (UniversalType r Q 1))
    (A R : ℕ) (t : Fin Q) (row : Fin D) (i : ℕ) : ℤ :=
  if h : i < D then LayoutProgram.localEntry P A R t row ⟨i,h⟩ else 0

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramRow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical row preparation and output framing for all-D construction. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def emitRow : Code 288 := frame 284 24 286 (by decide)

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentLabelSerialization
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The vertex-label producer emits exactly the semantic bucket records,
in ascending vertex order before its explicit accumulator reversal. -/

namespace SubexponentialSAT.Subexp.AssignmentLabelSerialization

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SlotAssignment

theorem labelRecords_finRange {D : ℕ} (rows : List (List Bool))
    (plans : Fin D → List ℕ) :
    PackingVertexLabels.labelRecords rows ((List.finRange D).map plans) 0 =
      (List.finRange D).map (fun v =>
        (GatherProgram.gathered rows (plans v), List.replicate v.val true)) := by
  unfold PackingVertexLabels.labelRecords
  rw [List.length_map, List.length_finRange, ← List.range_eq_range',
    ← List.map_coe_finRange D, List.zipWith_map, List.zipWith_self]

end SubexponentialSAT.Subexp.AssignmentLabelSerialization

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramLabels
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Materialize incidence labels from actual two-address read plans. The
physical gather reads the head and factor words in that order. Incidence
numbers are the read-plan list positions, including repeated plans. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp
open SubexponentialSAT.BitProgram

variable {D r Q : ℕ}

theorem gathered_addressLabel (words : List (Word r Q))
    (address : Fin D → Fin words.length × Fin words.length) (i : Fin D) :
    GatherProgram.gathered (words.map ReadPlan.encodeWord)
      [(address i).1.val, (address i).2.val] =
      CollisionProgram.encodeType (addressLabel words address i) := by
  have hp : (address i).1.val < (words.map ReadPlan.encodeWord).length := by
    simp
  have hn : (address i).2.val < (words.map ReadPlan.encodeWord).length := by
    simp
  simp [GatherProgram.gathered,
    ReadPlan.encodeType_eq_words, List.ofFn_succ, CollisionProgram.registerWord,
    addressLabel]

theorem addressLabel_records (words : List (Word r Q))
    (address : Fin D → Fin words.length × Fin words.length) :
    PackingVertexLabels.labelRecords (words.map ReadPlan.encodeWord)
      (labelPlans words address) 0 =
      BucketProgram.vertexRecords (List.finRange D) (addressLabel words address)
        CollisionProgram.encodeType (fun i => List.replicate i.val true) := by
  rw [labelPlans, AssignmentLabelSerialization.labelRecords_finRange]
  unfold BucketProgram.vertexRecords
  apply List.map_congr_left
  intro i _
  exact Prod.ext (gathered_addressLabel words address i) rfl

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramNativePacking
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! End-to-end physical packing from runtime word rows and native address
plans. Both labels and the full universal type list are generated before the
bucket/block/leftover controller runs. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.NativePacking

open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

structure Spec (U : Type*) [DecidableEq U] where
  params : NativeFrontend.Params
  types : FiniteEnumeration U
  label : Fin params.D → U
  encodeType : U → List Bool
  encodeType_injective : Function.Injective encodeType
  rows_width : ∀ row ∈ params.rows, row.length = params.width.length
  plans_valid : ∀ plan ∈ params.planList, ∀ i ∈ plan, i < params.rows.length
  label_records : PackingVertexLabels.labelRecords params.rows params.planList 0 =
    BucketProgram.vertexRecords (List.finRange params.D) label encodeType
      (fun i => List.replicate i.val true)
  type_records : params.typeRows = types.values.map encodeType

end SubexponentialSAT.SqrtLog.LayoutProgram.NativePacking

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingRelations
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Equality tests for shared-head incidence words and individual head colors. -/
namespace SubexponentialSAT.SqrtLog.Packing
open SubexponentialSAT.MulticolorTypes

/-- The finite Boolean cell used for one coordinate of a word. -/
def headColorBits {r Q : ℕ} (w : Word r Q) (t : Fin Q) : List Bool :=
  List.ofFn (fun c : Fin r => decide (w t = c))

@[simp] theorem headColorBits_length {r Q : ℕ} (w : Word r Q) (t : Fin Q) :
    (headColorBits w t).length = r := by simp [headColorBits]

end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical storage operations for the closed parameter setup

All copies, clears, and register resets are fixed instruction sequences or
calls to proved bit programs. Their state transformations below are assertion
notation only. The setup program uses them to isolate dirty arithmetic
subroutines from the persistent parameter words.
-/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

theorem copyMany_eval {S : ℕ} (tmp : Fin S) (ps : List (Fin S × Fin S)) (a : Data S)
    (hports : ∀ p ∈ ps, p.1 ≠ p.2 ∧ p.1 ≠ tmp ∧ tmp ≠ p.2)
    (ht : a.stacks tmp = []) :
    Eval (copyMany tmp ps) (copyManyCost ps a) a (copyManyState ps a) := by
  induction ps generalizing a with
  | nil => exact .base (.skip a)
  | cons p ps ih =>
    obtain ⟨src, dst⟩ := p
    have hp := hports (src, dst) (by simp)
    have hrest : ∀ p ∈ ps, p.1 ≠ p.2 ∧ p.1 ≠ tmp ∧ tmp ≠ p.2 := by
      intro p hm
      exact hports p (by simp [hm])
    have ht' : (copyState src dst a).stacks tmp = [] :=
      (copyState_frame src dst tmp a hp.2.2).trans ht
    exact .seq (copy_eval src dst tmp a hp.1 hp.2.1 hp.2.2 ht)
      (ih (copyState src dst a) hrest ht')

theorem clearMany_stacks {S : ℕ} (ps : List (Fin S)) (a : Data S) (i : Fin S) :
    (clearManyState ps a).stacks i = if i ∈ ps then [] else a.stacks i := by
  induction ps generalizing a with
  | nil => simp [clearManyState]
  | cons p ps ih =>
    rw [clearManyState, ih]
    by_cases hp : i = p <;> by_cases hs : i ∈ ps <;>
      simp [clearState, hp, hs]

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputAddress
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The saved native plan stream is exactly the layout's typed word-address
stream, in the native incidence enumeration order. No conversion is required. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Address
open SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

variable {r Q : ℕ}

def address (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hm : mask.length ≤ n) (words : List (Word r Q))
    (hw : words.length = n + Semantics.factorCount scopes mask)
    (i : Semantics.Incidences scopes mask) : Fin words.length × Fin words.length :=
  (⟨(Semantics.owner scopes n mask hm i).val, by
      have h := (Semantics.owner scopes n mask hm i).isLt
      omega⟩,
   ⟨n + (Semantics.factor scopes n mask hm i).val, by
      have h := (Semantics.factor scopes n mask hm i).isLt
      omega⟩)

@[simp] theorem head_val (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hm : mask.length ≤ n) (words : List (Word r Q))
    (hw : words.length = n + Semantics.factorCount scopes mask)
    (i : Semantics.Incidences scopes mask) :
    (address scopes n mask hm words hw i).1.val =
      ((Semantics.nativeEntries scopes mask).get i).1 := rfl

@[simp] theorem factor_val (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hm : mask.length ≤ n) (words : List (Word r Q))
    (hw : words.length = n + Semantics.factorCount scopes mask)
    (i : Semantics.Incidences scopes mask) :
    (address scopes n mask hm words hw i).2.val =
      n + ((Semantics.nativeEntries scopes mask).get i).2 := rfl

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Address

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingIncidenceInput

namespace Problem

abbrev incidences (p : Problem) := (Semantics.nativeEntries p.scopes p.mask).length

end Problem

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end


