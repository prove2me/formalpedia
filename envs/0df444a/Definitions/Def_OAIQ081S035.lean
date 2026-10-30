-- Prove2me | Definitions.Def_OAIQ081S035
-- name    : OAIQ081S035
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:31:10.259034+00:00
-- url     : https://prove2.me/theorems/42aff19c-31e6-4496-ab0f-58c1c1f52ace
-- title:
--   Definitions bundle OAIQ081S035 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 144 declarations of OpenAI's Lean: 114 definitions, 1 inductive type or structure and 29 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.encodeIndices`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.peekRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.lift8`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.pairLength`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOffsetProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.pairTail`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.reset`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.maxSelected`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.ArrayData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Count.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Defect.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Defect.Ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Defect.addPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Defect.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Defect.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Defect.output`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.integerLength`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry.Saved`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.NativeFrontend.Params.base`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.NativeFrontend.Params.typeRows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.Saved`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.ScanRestore.restore`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.powerCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.powerLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.powerProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.powerPutZero`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.powerRead`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.Saved`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.totalCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.initializeOne`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.numeratorFoldCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.one`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native.scalarAllowance`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.advance`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.initializeTriples`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.parityCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.popCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.popH` and 75 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLog_LayoutFiberSumProgramBasic`, `SubexponentialSAT_SqrtLog_LayoutFiberSumProgramLoop`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgramPrimitives`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgramSource`, `SubexponentialSAT_SqrtLog_LayoutNumerator`, `SubexponentialSAT_SqrtLog_LayoutOffsetProgram`, `SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramCore`, `SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramEmit`, `SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramParse`, `SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramVisit`, `SubexponentialSAT_SqrtLog_LayoutProducedHeads`, `SubexponentialSAT_SqrtLog_LayoutProgramArrays`, `SubexponentialSAT_SqrtLog_LayoutProgramCount`, `SubexponentialSAT_SqrtLog_LayoutProgramDefect`, `SubexponentialSAT_SqrtLog_LayoutProgramEntryBankCost`, `SubexponentialSAT_SqrtLog_LayoutProgramFrontend`, `SubexponentialSAT_SqrtLog_LayoutProgramIntegerEntry`, `SubexponentialSAT_SqrtLog_LayoutProgramNumerator`, `SubexponentialSAT_SqrtLog_LayoutProgramPower`, `SubexponentialSAT_SqrtLog_LayoutProgramScalar`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarFromCountsDefinitions`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarFromCountsPrimitives`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarNumerator`, `SubexponentialSAT_SqrtLog_LayoutProgramScanRestore`, `SubexponentialSAT_SqrtLog_LayoutSourceValuesProgram`, `SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram`, `SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgramBasic`, `SubexponentialSAT_SqrtLog_LeafParametersProgramNative`, `SubexponentialSAT_SqrtLog_PackingAlgorithm`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputEntry`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputNative`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputSemantics`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyScope`, `SubexponentialSAT_SubexpAnnihilation`, `SubexponentialSAT_SubexpTupleRefinement`, `SubexponentialSAT_SubexpVectorEnumeration`, `SubexponentialSAT_Subexp_AssignmentAlphabetSemantics`, `SubexponentialSAT_Subexp_BucketProgram`, `SubexponentialSAT_Subexp_CandidateScoreProgram`, `SubexponentialSAT_Subexp_ConstraintEntryCompare`, `SubexponentialSAT_Subexp_GatherProgram`, `SubexponentialSAT_Subexp_GlobalBasisMetadata`, `SubexponentialSAT_Subexp_LocalExpectation`, `SubexponentialSAT_Subexp_MatrixAnchorGuardProgram`, `SubexponentialSAT_Subexp_MatrixAnchorReadProgram`, `SubexponentialSAT_Subexp_MatrixColorReadProgram`, `SubexponentialSAT_Subexp_MatrixEntryCore`, `SubexponentialSAT_Subexp_MatrixExtendedEntryProgram`, `SubexponentialSAT_Subexp_MatrixInputAccess`, `SubexponentialSAT_Subexp_MatrixParityProgram`, `SubexponentialSAT_Subexp_MatrixPositionCountProgram`, `SubexponentialSAT_Subexp_MatrixPositionProgram`, `SubexponentialSAT_Subexp_MatrixScanProgram`, `SubexponentialSAT_Subexp_MatrixScanSemantics`, `SubexponentialSAT_Subexp_PackingBucketTable`, `SubexponentialSAT_Subexp_PackingEntryEmitter`, `SubexponentialSAT_Subexp_PackingExtractionBlock`, `SubexponentialSAT_Subexp_PackingExtractionEmit`, `SubexponentialSAT_Subexp_PackingExtractionOuter`, `SubexponentialSAT_Subexp_PackingLeftoverEmitter`, `SubexponentialSAT_Subexp_PackingLeftovers`, `SubexponentialSAT_Subexp_PackingProgramSupport`, `SubexponentialSAT_Subexp_PackingVertexLabels`, `SubexponentialSAT_Subexp_SelectorOutput`, `SubexponentialSAT_Subexp_TensorSpectrum`, `SubexponentialSAT_Subexp_TupleProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S000`, `OAIQ081S001`, `OAIQ081S002`, `OAIQ081S003`, `OAIQ081S004`, `OAIQ081S005`, `OAIQ081S006`, `OAIQ081S007`, `OAIQ081S008`, `OAIQ081S010`, `OAIQ081S011`, `OAIQ081S012` and `OAIQ081S013` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S047`, `OAIQ081S053`, `OAIQ081S054`, `OAIQ081S055`, `OAIQ081S056`, `OAIQ081S057`, `OAIQ081S058`, `OAIQ081S060`, `OAIQ081S061`, `OAIQ081S062`, `OAIQ081S063` and `OAIQ081S064`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S000
import Definitions.Def_OAIQ081S001
import Definitions.Def_OAIQ081S002
import Definitions.Def_OAIQ081S003
import Definitions.Def_OAIQ081S004
import Definitions.Def_OAIQ081S005
import Definitions.Def_OAIQ081S006
import Definitions.Def_OAIQ081S007
import Definitions.Def_OAIQ081S008
import Definitions.Def_OAIQ081S010
import Definitions.Def_OAIQ081S011
import Definitions.Def_OAIQ081S012
import Definitions.Def_OAIQ081S013

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete components of the sharp clause/core search from Appendix A.
The guard counts actual framed literals and executes the preserving subset tester.
The complete search and its polynomial resource bound are developed separately below. -/


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls

abbrev Formula := List Clause

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control Cartesian tuple generation

Alphabet words, tuple payloads, and iteration depths are stack data.  The
instruction tables below do not depend on any of their lengths.
-/

namespace SubexponentialSAT.Subexp.TupleProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-! The fixed ABI uses ten Boolean registers and nine Boolean stacks:
0 prior tuples, 1 saved alphabet, 2 current reversed tuple, 3 alphabet cursor,
4 reversed word, 5 output, 6 copied tuple, 7 copy scratch, 8 unary depth.
Registers 0--2 and 3--5 belong to the two framed iterators, 6--7 are scratch,
and 8--9 belong to the eventual depth loop. -/

theorem cartesianOutput_perm (tuples alphabet : Records) :
    (cartesianOutput tuples alphabet).Perm
      (tuples.flatMap fun tuple => alphabet.map (tuple ++ ·)) := by
  exact List.reverse_perm _

end SubexponentialSAT.Subexp.TupleProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutFiberSumProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native owner-fiber summation helpers. The remaining fiber is a stream of
actual unary index fields, never an array of precomputed matrix entries. -/
namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open RowSelectionProgram

def encodeIndices (is : List ℕ) : List Bool := is.flatMap Encoding.encodeNat

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end

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

def peekRegs (regs : Fin 16 → Bool) (queue : List Bool) : Fin 16 → Bool :=
  readRegs regs 14 15 queue.head?

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

abbrev Code (s : ℕ) := Cmd 16 s

abbrev lift8 {s : ℕ} (c : Cmd 8 s) (input output : Fin s) : Code s :=
  .call (ProgramLinking.liftProgram (compiled c input output) regs8 id)

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Relocatable finite-bank contract for integer incidence entries, and the
fixed physical storage layout used by the direct all-row matrix builder. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def pairLength (p : Pair) : ℕ := p.1.length+p.2.length

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutNumerator
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Integer numerators for the actual universal swap matrices

The parity coefficients are the immutable library's coefficients, instantiated
over the integers. Their images are the same coefficients over every
commutative ring. Clearing the projector denominators uses only powers of two.
-/

namespace SubexponentialSAT.SqrtLog.LayoutNumerator

open scoped BigOperators
open SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.BinomialInterpolation
open SubexponentialSAT.Subexp.MatrixSupport

theorem parityCoefficients_intCast (K : Type*) [CommRing K] (A R : ℕ)
    (j : Fin R) :
    (parityCoefficients (K := ℤ) A R j : K) =
      parityCoefficients (K := K) A R j := by
  have hs : ∀ d : Fin R,
      ∑ j : Fin R, (parityCoefficients (K := ℤ) A R j : K) *
        ((A + d.val).choose j.val : K) = (-1 : K) ^ (A + d.val) := by
    intro d
    have hz := congrArg (Int.castRingHom K) (parityCoefficients_spec (K := ℤ) A R d)
    simpa using hz
  have h := (existsUnique_binomial_interpolation (K := K) A R
    (fun d : Fin R => (-1 : K) ^ (A + d.val))).unique
      hs (parityCoefficients_spec A R)
  exact congrFun h j

theorem extend_parityCoefficients_intCast (K : Type*) [CommRing K]
    (A R j : ℕ) :
    ((extendCoefficients (parityCoefficients (K := ℤ) A R) j : ℤ) : K) =
      extendCoefficients (parityCoefficients (K := K) A R) j := by
  by_cases hj : j < R
  · simp [extendCoefficients, hj, parityCoefficients_intCast]
  · simp [extendCoefficients, hj]

end SubexponentialSAT.SqrtLog.LayoutNumerator

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOffsetProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed native producer of the signed-bucket offset 2*B*(8*Q)^(2*R).
All arithmetic acts on runtime binary words. This offset is unrelated to
the unary scalar-row width 1+2*A*R+Q. -/
namespace SubexponentialSAT.SqrtLog.LayoutOffsetProgram
open SubexponentialSAT BitProgram StructuredCalls BinaryArithmetic
open SubexpBlockParameterProgram

abbrev Data := State 8 22

end SubexponentialSAT.SqrtLog.LayoutOffsetProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_LocalExpectation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Uniform multi-color conditional expectation

All parameters remain visible. The local evaluator enumerates only each pair's
read support, and its total evaluation bound is a fixed polynomial in the
number of chunks and universal types. Natural completion counts also give a
common-denominator representation for the rational conditional scores.
-/

namespace SubexponentialSAT.Subexp.LocalExpectation

open SubexponentialSAT.LocalExpectation SubexponentialSAT.ConditionalExpectation
open scoped BigOperators

variable {I W J : Type*} [DecidableEq I]

/-- A local numerator scaled to a common power of the word alphabet size. -/
def scaledCount (alphabet : List W) (f : (I → W) → ℕ) (support : Finset I)
    (S : ℕ) (remaining : List I) (ω : I → W) : ℕ :=
  alphabet.length ^ (S - (active support remaining).length) *
    completionCount alphabet f (active support remaining) ω

/-- Natural common numerator for a sum of bounded-support local indicators. -/
def commonNumerator (alphabet : List W) (terms : List J)
    (f : J → (I → W) → ℕ) (support : J → Finset I) (S : ℕ)
    (remaining : List I) (ω : I → W) : ℕ :=
  (terms.map (fun j => scaledCount alphabet (f j) (support j) S remaining ω)).sum

end SubexponentialSAT.Subexp.LocalExpectation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_BucketProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed bit program for one packing bucket

The input is a framed query followed by framed `(type key, vertex payload)`
records. The routine compares actual bit strings. It consumes all records,
keeps the query on port 2, and prepends matching framed payloads on port 5.
Supplying records in reverse vertex order produces the original bucket order.
-/

namespace SubexponentialSAT.Subexp.BucketProgram

open BitProgram StructuredProgram StructuredCalls SubexpRecordScan

def encodeRecords : List Record → List Bool
  | [] => []
  | (key, payload) :: rs => Encoding.frame key ++ (Encoding.frame payload ++ encodeRecords rs)

def selected : List Record → List Bool → List (List Bool)
  | [], _ => []
  | (key, payload) :: rs, query =>
    if key = query then payload :: selected rs query else selected rs query

abbrev peekInput : StructuredCalls.Cmd 5 6 := .base (.atom (.peek 0 0 1))

end SubexponentialSAT.Subexp.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_GatherProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed program gathering runtime-selected rows

The packed assignment is on stack 0 and its unary row width on stack 3.
Stack 8 contains `ProgramEncoding.encodeRecords` of unary index words.
The program preserves the assignment and width and writes the selected rows,
in plan order, to stack 1. All widths and indices are stack data.
-/

namespace SubexponentialSAT.Subexp.GatherProgram

open BitProgram StackRoutines StructuredCalls

theorem lookupPort_injective : Function.Injective lookupPort := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 10 => x.val) h)

theorem gathered_length (rows : List (List Bool)) (plan : List ℕ) (w : ℕ)
    (hrows : ∀ row ∈ rows, row.length = w) (hplan : ∀ i ∈ plan, i < rows.length) :
    (gathered rows plan).length = plan.length * w := by
  induction plan with
  | nil => simp [gathered]
  | cons i plan ih =>
      have hi := hplan i (by simp)
      have htail : ∀ j ∈ plan, j < rows.length := fun j hj => hplan j (by simp [hj])
      have hr : (rows.getD i []).length = w := by
        rw [List.getD_eq_getElem rows [] hi]
        exact hrows _ (List.getElem_mem hi)
      change (rows.getD i [] ++ gathered rows plan).length = (plan.length + 1) * w
      rw [List.length_append, hr, ih htail]
      ring

theorem accumulator_fold (rows : List (List Bool)) (plan : List ℕ) (acc : List Bool) :
    (indexRecords plan).foldl
      (fun out bits => (rows.getD bits.length []).reverse ++ out) acc =
      (gathered rows plan).reverse ++ acc := by
  induction plan generalizing acc with
  | nil => simp [indexRecords, gathered]
  | cons i plan ih =>
      simpa only [indexRecords, List.map_cons, List.foldl_cons, List.length_replicate,
        gathered, List.flatMap_cons, List.reverse_append, List.append_assoc] using
        ih ((rows.getD i []).reverse ++ acc)

theorem indexRecords_valid (rows : List (List Bool)) (plan : List ℕ)
    (hplan : ∀ i ∈ plan, i < rows.length) :
    ∀ bits ∈ indexRecords plan, bits.length < rows.length := by
  intro bits hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  simpa using hplan i hi

/-- The concrete trace budget, including the final reversal and halt. -/
def traceCost (rows : List (List Bool)) (width : ℕ) (plan : List ℕ) : ℕ :=
  7 + RecordPrograms.budget (callbackCost width) (indexRecords plan) +
    3 * (gathered rows plan).length

theorem iterator_budget_eq (width : ℕ) (plan : List ℕ) :
    RecordPrograms.budget (callbackCost width) (indexRecords plan) =
      (14 * width + 16) * plan.sum + (18 * width + 27) * plan.length := by
  induction plan with
  | nil => simp [RecordPrograms.budget, indexRecords]
  | cons i plan ih =>
      change 6 * (List.replicate i true).length + callbackCost width (List.replicate i true) +
        7 + RecordPrograms.budget (callbackCost width) (indexRecords plan) = _
      rw [ih]
      simp only [List.length_replicate, callbackCost, List.sum_cons, List.length_cons]
      ring

end SubexponentialSAT.Subexp.GatherProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectorOutput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The output boundary for the fixed first-match selector. A matching payload
is parsed onto the output port; an absent key copies the original query. -/

namespace SubexponentialSAT.Subexp.SelectorProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

def budget (query : List Bool) (records : List (List Bool × List Bool)) : ℕ :=
  scanBudget query records + materializeBudget query (records.lookup query) + 3

end SubexponentialSAT.Subexp.SelectorProgram

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

open BitProgram StructuredCalls

theorem gatherRegs_injective : Function.Injective gatherRegs := by
  intro i j h
  exact Fin.ext (congrArg (fun z : Fin 8 => z.val) h)

theorem gatherPorts_injective : Function.Injective gatherPorts := by
  intro i j h
  exact Fin.ext (congrArg (fun z : Fin 15 => z.val) h)

abbrev sequence (cs : List (Cmd 8 15)) : Cmd 8 15 :=
  cs.foldr Cmd.seq (.base .skip)

end SubexponentialSAT.Subexp.PackingVertexLabels

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native owner-fiber scan primitives. Original ambient IDs are compared as
unary strings; the emitted indices count positions in the actual plan stream. -/
namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls

@[simp] theorem status_read (regs : Fin 5 → Bool) :
    readRegs regs (0 : Fin 5) 1 none=status regs false false := by
  first | done | (first | done | (funext i; fin_cases i <;> rfl))

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

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
open SubexponentialSAT BitProgram StructuredCalls

def reset (regs : Fin 5 → Bool) : Fin 5 → Bool :=
  Function.update (status regs false true) 4 false

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
open SubexponentialSAT BitProgram StructuredCalls

def pairTail (f : ℕ) : List Bool := true :: (Encoding.frame (unary f) ++ [false])

@[simp] theorem pairTail_length (f : ℕ) : (pairTail f).length=2*f+3 := by
  simp [pairTail,Encoding.length_frame]

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
open SubexponentialSAT BitProgram StructuredCalls

@[simp] theorem unary_eq (v q : ℕ) : unary v=unary q ↔ v=q := by
  constructor
  · intro h
    have hh := congrArg List.length h
    simpa using hh
  · rintro rfl; rfl

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpVectorEnumeration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Duplicate-free executable coefficient enumeration

These proofs concern the explicit lists used by `QuarticSearch`; they do not
replace the lists by an abstract enumeration of a finite type.
-/

namespace SubexponentialSAT.SubexpVectorEnumeration

/-- Prefixing different alphabet entries gives disjoint blocks, while
prefixing one entry preserves the distinctness of the shorter vectors. -/
theorem vectors_nodup {A : Type*} (alphabet : List A)
    (h : alphabet.Nodup) (d : ℕ) : (QuarticSearch.vectors alphabet d).Nodup := by
  induction d with
  | zero => simp [QuarticSearch.vectors]
  | succ d ih =>
      rw [QuarticSearch.vectors]
      apply List.nodup_flatMap.mpr
      refine ⟨fun a _ => ih.map (fun u v huv => ?_), ?_⟩
      · funext i
        exact congrFun huv i.succ
      · exact h.imp fun {a b} hab x hx hy => by
          rcases List.mem_map.mp hx with ⟨v, _, rfl⟩
          rcases List.mem_map.mp hy with ⟨w, _, hw⟩
          exact hab (Fin.cons_inj.mp hw).1.symm

end SubexponentialSAT.SubexpVectorEnumeration

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTupleRefinement
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Representation and coverage of the fixed tuple program

The tuple program reverses its record order at each Cartesian expansion.
These theorems retain that actual order and show that it is a permutation of
the explicit coefficient-vector enumeration. Fixed-width injective encodings
then give uniqueness, not just coverage.
-/

namespace SubexponentialSAT.SubexpTupleRefinement

open Subexp.TupleProgram

/-- All record reversals affect order only; every prefix/suffix combination
is generated with its correct multiplicity. -/
theorem powerRows_perm (alphabet rows : List (List Bool)) (n : ℕ) :
    (powerRows alphabet n rows).Perm
      (rows.flatMap fun pre => (QuarticSearch.vectors alphabet n).map
        (fun v => pre ++ tuplePayload v)) := by
  induction n generalizing rows with
  | zero => simp [powerRows, QuarticSearch.vectors, tuplePayload]
  | succ n ih =>
    change (powerRows alphabet n (cartesianOutput rows alphabet)).Perm _
    refine (ih (cartesianOutput rows alphabet)).trans ?_
    refine ((cartesianOutput_perm rows alphabet).flatMap_right
      (fun pre => (QuarticSearch.vectors alphabet n).map
        (fun v => pre ++ tuplePayload v))).trans ?_
    apply List.Perm.of_eq
    simp only [QuarticSearch.vectors, List.flatMap_assoc, List.flatMap_map,
      List.map_flatMap, List.map_map, Function.comp_def, tuplePayload_cons,
      List.append_assoc]

theorem powerRows_empty_perm (alphabet : List (List Bool)) (n : ℕ) :
    (powerRows alphabet n [[]]).Perm
      ((QuarticSearch.vectors alphabet n).map tuplePayload) := by
  simpa using powerRows_perm alphabet [[]] n

end SubexponentialSAT.SubexpTupleRefinement

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

def resetList {r s : ℕ} : List (Fin r) → StructuredProgram.Cmd r s
  | [] => .skip
  | i :: rest => .seq (.atom (.set i false)) (resetList rest)

end SubexponentialSAT.Subexp.CandidateScoreProgram

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

theorem rows_eq_alphabet (r : ℕ) :
    rows 0 r = (List.finRange r).reverse.map oneHot := by
  rw [rows_eq_range]
  rw [Nat.zero_add, ← List.range_eq_range']
  rw [← List.map_coe_finRange r]
  simp only [List.map_reverse, List.map_map]
  apply congrArg List.reverse
  apply List.map_congr_left
  intro c _
  exact (oneHot_eq c).symm

def colorCode {r : ℕ} (hr : 0 < r) : StackEncoding.BlockCode (Fin r) where
  width := r
  width_pos := hr
  block := oneHot
  length_block _ := List.length_ofFn
  injective_block := oneHot_injective r

def wordBytes (r Q : ℕ) : List (List Bool) :=
  TupleProgram.powerRows (rows 0 r) Q [[]]

end SubexponentialSAT.Subexp.AssignmentAlphabetSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_GlobalBasisMetadata
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical packing metadata lookup

The raw packing table and query remain on stacks 0 and 1. A successful lookup
returns either a block/type pair on 2/3, or a leftover rank on 4. Register 4
distinguishes those cases; all other registers and stacks 5 through 11 are
cleared. Keys, indices, and type encodings are runtime words.
-/

namespace SubexponentialSAT.Subexp.GlobalBasisMetadata

open BitProgram StructuredCalls


def Metadata.encode : Metadata → List Bool
  | .covered block typeCode => true :: (Encoding.frame block ++ Encoding.frame typeCode)
  | .leftover rank => false :: Encoding.frame rank

def Metadata.block : Metadata → List Bool
  | .covered block _ => block
  | .leftover _ => []

def Metadata.typeCode : Metadata → List Bool
  | .covered _ typeCode => typeCode
  | .leftover _ => []

def Metadata.rank : Metadata → List Bool
  | .covered .. => []
  | .leftover rank => rank

end SubexponentialSAT.Subexp.GlobalBasisMetadata

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingAlgorithm
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A deterministic conditional-expectation algorithm with at most four word reads per term. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation

section Algorithm
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

variable [NeZero r]

def numberedScoreSupport (indices : List (V ⊕ E)) (z : ScoreTerm I V Q) : Finset ℕ :=
  (scoreSupport ivar factor z).image (indexCode indices)

end Algorithm
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingBucketTable
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The fixed all-key bucket/minimum controller. -/

namespace SubexponentialSAT.Subexp.PackingBucketTable

open BitProgram StructuredCalls PackingBucketCalls

def minimum (records : List BucketProgram.Record) (keys : List (List Bool)) (initial : ℕ) : ℕ :=
  keys.foldl (fun m key => min m (BucketProgram.selected records key).length) initial

def callbackCost (records : List BucketProgram.Record) (key : List Bool) : ℕ :=
  100 * ((BucketProgram.encodeRecords records).length + 1) * (key.length + 1)

end SubexponentialSAT.Subexp.PackingBucketTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TensorSpectrum
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Tensor eigenbases for the multicolor register swap

The finite change of basis is constructed from invertible local kernels. This
module then specializes it to the actual register swap and transports it to the
joint fiber of universal types; multiplicities count those actual basis labels.
-/

namespace SubexponentialSAT.Subexp.TensorSpectrum

open scoped BigOperators

section ProductKernel

variable (K : Type*) [Field K]
variable {β ι : Type*} [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]

theorem productKernel_inverse (A B : β → β → K)
    (h : ∀ x y, (∑ z, A x z * B z y) = if x = y then 1 else 0)
    (x y : ι → β) :
    (∑ z, productKernel K A x z * productKernel K B z y) =
      if x = y then 1 else 0 := by
  classical
  simp only [productKernel, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun l z => A (x l) z * B z (y l))]
  simp_rw [h]
  by_cases hxy : x = y
  · subst y
    simp
  · rw [ite_eq_right hxy]
    obtain ⟨l, hl⟩ := Function.ne_iff.mp hxy
    exact Finset.prod_eq_zero (Finset.mem_univ l) (ite_eq_right hl)

end ProductKernel

section JointBasis

open SubexponentialSAT.MulticolorTypes

variable {r Q Δ : ℕ}

theorem pairKernel_inverse (K : Type*) [Field K] (h2 : (2 : K) ≠ 0)
    (d : DecidableEq (Fin r × Fin r)) (x y : Fin r × Fin r) :
    (∑ z, LocalSpectrum.localKernel K x z * LocalSpectrum.localDualKernel K z y) =
      @ite K (x = y) (d x y) 1 0 := by
  by_cases hxy : x = y
  · simpa only [ite_eq_left hxy] using LocalSpectrum.localKernel_inverse K h2 x y
  · simpa only [ite_eq_right hxy] using LocalSpectrum.localKernel_inverse K h2 x y

theorem pairDualKernel_inverse (K : Type*) [Field K] (h2 : (2 : K) ≠ 0)
    (d : DecidableEq (Fin r × Fin r)) (x y : Fin r × Fin r) :
    (∑ z, LocalSpectrum.localDualKernel K x z * LocalSpectrum.localKernel K z y) =
      @ite K (x = y) (d x y) 1 0 := by
  by_cases hxy : x = y
  · simpa only [ite_eq_left hxy] using LocalSpectrum.localDualKernel_inverse K h2 x y
  · simpa only [ite_eq_right hxy] using LocalSpectrum.localDualKernel_inverse K h2 x y

end JointBasis

end SubexponentialSAT.Subexp.TensorSpectrum

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProducedHeads
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual emitted original-ID head lists inherit the searched packing's
head bound. Taking the maximum is proof-only and introduces no new search. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LayoutProducedHeads
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes LeafHeadSetupProgram

variable {I : Type*} [Fintype I] [DecidableEq I] {n N r Q : ℕ}

def maxSelected (n Q r : ℕ) (rows : List (List Bool)) (low : List Bool) : ℕ :=
  (Finset.univ : Finset (Fin Q × Fin r)).sup
    (fun z => (selectedHeads n rows low (z.1.val*r+z.2.val)).length)

end SubexponentialSAT.SqrtLog.LayoutProducedHeads

end
end OAI.Algorithms
end

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

abbrev ArrayData := State 2 11

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The scalar loop length R−d is computed by deleting actual unary tokens.
The scan's distinguished unchanged anchor is removed first. Neither natural
subtraction nor a loop-count constructor is a machine primitive. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Count

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 2 2

end SubexponentialSAT.SqrtLog.LayoutProgram.Count

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramDefect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical clearing-defect entries from the actual signed numerator pair.
A diagonal entry is D−(P−N), an off-diagonal entry is −(P−N). The numerator
and cached denominator remain intact; the result is a fresh signed pair.
The diagonal flag is a runtime bit, supplied by the type equality scan. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Defect

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

abbrev Data := State 8 10

def addPorts : SubexponentialSAT.ArithmeticCalls.Ports 10 where
  left := 1
  right := 2
  out := 3
  work := ⟨![5,6,7,8,9], by decide⟩
  out_ne_left := by decide
  out_ne_right := by decide
  work_ne_left := by decide
  work_ne_right := by decide
  work_ne_out := by decide

abbrev command : Cmd 8 10 :=
  .seq (SubexponentialSAT.ArithmeticCalls.copyAt 0 4 5)
    (.ite 7 (SubexponentialSAT.ArithmeticCalls.addAt addPorts) (SubexponentialSAT.ArithmeticCalls.copyAt 1 3 5))

def Ready (d : Data) : Prop := ∀ j : Fin 10, 3 ≤ j.val → d.stacks j = []
def output (d : Data) (positive negative : List Bool) : Fin 10 → List Bool :=
  Function.update (Function.update d.stacks 4 negative) 3 positive

def budget (d : Data) : ℕ :=
  7*(d.stacks 0).length + 100*((d.stacks 1).length+(d.stacks 2).length+1)^2+12

end SubexponentialSAT.SqrtLog.LayoutProgram.Defect

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpAnnihilation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

section MatrixExtension

variable {V F E : Type*} [Ring F] [Ring E]

theorem zeroExtendMatrix_of_row_mem (J : Set V) [DecidablePred (· ∈ J)]
    (M : Matrix J J F) (u y : V) (hu : u ∈ J) :
    zeroExtendMatrix J M u y = Annihilation.extendRow J (M ⟨u, hu⟩) y := by
  classical
  by_cases hy : y ∈ J <;>
    simp [zeroExtendMatrix, Annihilation.extendRow, hu, hy]

end MatrixExtension

end SubexponentialSAT.SubexpAnnihilation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixInputAccess
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-port array access used to prepare the matrix-entry comparison. -/

namespace SubexponentialSAT.Subexp.MatrixInputAccess

open BitProgram StructuredCalls StackRoutines

abbrev copy (src dst : Fin 29) : Cmd 8 29 := .call (copyProgram src dst 8 0 1)

end SubexponentialSAT.Subexp.MatrixInputAccess

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixAnchorReadProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Read the selected color from each of four preserved word streams. The
position is a unary runtime cursor on stack37; color width is on stack21. -/

namespace SubexponentialSAT.Subexp.MatrixAnchorReadProgram

open BitProgram StructuredCalls StackRoutines

abbrev copy (src dst : Fin 42) : Cmd 10 42 := .call (copyProgram src dst 8 0 1)

abbrev transfer (src dst : Fin 42) : Cmd 10 42 := .call (transferProgram src dst 0 1)

abbrev move (src dst : Fin 42) : Cmd 10 42 := .seq (transfer src 8) (transfer 8 dst)

end SubexponentialSAT.Subexp.MatrixAnchorReadProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ConstraintEntryCompare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Compare the two preserved universal-type byte arrays without changing
the scalar result or any input stack of the matrix-entry service. -/

namespace SubexponentialSAT.Subexp.ConstraintEntryCompare

open BitProgram StructuredCalls StackRoutines

abbrev copy (src dst : Fin 46) : Cmd 10 46 :=
  .call (copyProgram src dst 42 0 1)

end SubexponentialSAT.Subexp.ConstraintEntryCompare

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixColorReadProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed program that consumes one color word from each of the four
matrix-input streams. The word width is supplied as a unary stack. -/

namespace SubexponentialSAT.Subexp.MatrixColorReadProgram

open BitProgram StructuredCalls StackRoutines

abbrev copyWidth : Cmd 8 23 := .call (copyProgram 21 10 0 0 1)

abbrev restore (dst : Fin 23) : Cmd 8 23 := .call (transferProgram 4 dst 0 1)

end SubexponentialSAT.Subexp.MatrixColorReadProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixPositionProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical comparison of the two color pairs at one matrix position.
The four color words occupy stacks 13--16. They are preserved. Actual copies,
the existing bit-equality table, and actual cleanup produce the comparison
bits; no semantic equality callback is assumed. -/

namespace SubexponentialSAT.Subexp.MatrixPositionProgram

open BitProgram StructuredCalls StackRoutines

abbrev copy (src dst : Fin 17) : Cmd 8 17 := .call (copyProgram src dst 0 0 1)

abbrev prepare (swapped : Bool) : Cmd 8 17 :=
  .seq (copy (firstSource swapped) 1) (.seq (copy (secondSource swapped) 1)
    (.seq (copy 16 12) (copy 15 12)))

end SubexponentialSAT.Subexp.MatrixPositionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixPositionCountProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One physical active-position step for a normalized matrix entry.
Stack 2 counts unchanged nonfixed pairs, stack 3 counts swapped nonfixed
pairs, and register 7 records compatibility of all positions seen so far. -/

namespace SubexponentialSAT.Subexp.MatrixPositionCountProgram

open BitProgram StructuredCalls StackRoutines MatrixPositionProgram

abbrev popResult (out : Fin 8) : Cmd 8 17 := .base (.atom (.pop 11 out 5))

abbrev reset : Cmd 8 17 :=
  .seq (.base (.atom (.set 0 false))) (.seq (.base (.atom (.set 4 false)))
    (.seq (.base (.atom (.set 5 false))) (.base (.atom (.set 6 false)))))

end SubexponentialSAT.Subexp.MatrixPositionCountProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixScanProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The finite loop that scans the four color streams. Its loop count and
color width are runtime stacks. The result is specified by a finite fold of
the already proved physical scan step. -/

namespace SubexponentialSAT.Subexp.MatrixScanProgram

open BitProgram StructuredCalls StackRoutines

abbrev popCount : Cmd 8 23 := .base (.atom (.pop 22 4 6))

end SubexponentialSAT.Subexp.MatrixScanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixScanSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Arithmetic meaning of the two physical unary counters and the
compatibility register, including the one-hot color encoding boundary. -/

namespace SubexponentialSAT.Subexp.MatrixScanProgram

open BitProgram StructuredCalls StackRoutines

def same (w : ColorRow) : Bool := decide (w 0 ++ w 1 = w 2 ++ w 3)
def swapped (w : ColorRow) : Bool := decide (w 1 ++ w 0 = w 2 ++ w 3)

def unchangedCount : List ColorRow → ℕ
  | [] => 0
  | w :: ws => unchangedCount ws + if same w && !swapped w then 1 else 0

def transposedCount : List ColorRow → ℕ
  | [] => 0
  | w :: ws => transposedCount ws + if swapped w && !same w then 1 else 0

@[simp] theorem encodeColor_length {r : ℕ} (c : Fin r) : (encodeColor c).length = r := by
  simp [encodeColor]

end SubexponentialSAT.Subexp.MatrixScanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixParityProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A four-label program computes the sign parity of a unary index. The
bits of the counter are irrelevant; only its length is used. -/

namespace SubexponentialSAT.Subexp.MatrixParityProgram

open BitProgram

abbrev program : Program 3 1 4 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code := ![.pop 0 0 1 1, .branch 1 2 3, .bnot 2 2 0, .halt]

end SubexponentialSAT.Subexp.MatrixParityProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixEntryCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The fixed arithmetic workspace and subroutines of the joint-entry program. -/

namespace SubexponentialSAT.Subexp.MatrixEntryProgram

open BitProgram StructuredCalls StackRoutines

abbrev Code := Cmd 9 37

def series : List Code → Code
  | [] => .base .skip
  | c :: cs => .seq c (series cs)

def copy (src dst : Fin 37) : Code := .call (copyProgram src dst 9 0 1)

end SubexponentialSAT.Subexp.MatrixEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixAnchorGuardProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Three physical byte comparisons for the selected joint coordinate. -/

namespace SubexponentialSAT.Subexp.MatrixAnchorGuardProgram

open BitProgram StructuredCalls StackRoutines

abbrev copy (src dst : Fin 42) : Cmd 10 42 := .call (copyProgram src dst 0 0 1)

abbrev pop : Cmd 10 42 := .base (.atom (.pop 11 3 4))

abbrev setFalse : Cmd 10 42 := .base (.atom (.set 9 false))
abbrev accept (expected : Bool) : Cmd 10 42 :=
  if expected then .ite 3 (.base .skip) setFalse else .ite 3 setFalse (.base .skip)

end SubexponentialSAT.Subexp.MatrixAnchorGuardProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixExtendedEntryProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed control for the zero-extended joint entry on arbitrary universal
types. The unary position cursor is preserved on37. -/

namespace SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

open BitProgram StructuredCalls StackRoutines MulticolorTypes

abbrev Code := Cmd 10 42

open BitProgram StructuredCalls StackRoutines

open BitProgram StructuredCalls StackRoutines MulticolorTypes


end SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

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

def one : WordPair := ([true],[])

abbrev initializeOne : Cmd 8 18 :=
  .seq (.base (.atom (.set 0 true))) (.base (.atom (.push 0 0)))

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarFromCountsPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

structure Saved where
  hp : List Bool
  hn : List Bool
  width : List Bool
  power : WordPair
  r : List Bool
  a : List Bool

end SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed port assignments for cache access and triple serialization. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Code := Cmd 9 20

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

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
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open RowSelectionProgram

def advance : Code := .seq (.base (.atom (.bnot 8 8)))
  (.seq (.base (.atom (.set 0 true))) (.base (.atom (.push 9 0))))

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramBody.lean

/-! A fixed, paid iteration producing the three real scalar operands. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

def popH : Code := .base (.atom (.pop 8 0 1))

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramLoop.lean

/-! The native unary loop produces all triples in increasing binomial index. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

def popCount : Code := .base (.atom (.pop 7 6 7))

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramFinish.lean

/-! Initial unary copy/parity and final stream reversal are native paid calls. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

def parityCall : Code := .call (ProgramLinking.liftProgram
  SubexponentialSAT.Subexp.MatrixParityProgram.program parityRegisters parityPorts)

def initializeTriples : Code := .seq (.call (StackRoutines.copyProgram 7 8 10 0 1))
  (.seq (.base (.atom (.set 8 false))) parityCall)

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgram.lean

/-! Complete cache-to-triple primitive program with all scans and copies paid. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarNumerator
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The complete cached scalar call preserves both arrays, the width and the
clearing power. It constructs its operand stream and performs every signed
arithmetic operation on the primitive machine. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram
open LayoutTriplePreparationProgram

def numeratorFoldCost (N W P : ℕ) : ℕ :=
  200000000*(N+1)*(N*termGrowth (2*W+P)+(2*W+P)+4)^2+1

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarFromCountsDefinitions
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram
open LayoutTriplePreparationProgram


def totalCost (A R d h W P : ℕ) : ℕ :=
  14*R+7*A+15+(3*d+4)+binomialCost h R W+
  (numeratorPrepareCost (R-d) A W P+numeratorFoldCost (R-d) W P+1)+4*(R*W)+6+1


end SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScanRestore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The old classifier parks the unary Q word on33. This wrapper physically
returns that word to22 and exposes only the two new counters and flag. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.ScanRestore

open SubexponentialSAT.Subexp SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.MatrixEntryProgram

abbrev restore : Cmd 10 64 := .call (StackRoutines.transferProgram 33 22 0 1)

end SubexponentialSAT.SqrtLog.LayoutProgram.ScanRestore

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramNumerator
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete universal numerator evaluation from encoded type words and the
paid unsigned coefficient cache. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Numerator

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open UniversalEntry RowSelectionProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Saved := LayoutProgramScalar.FromCounts.Saved

end SubexponentialSAT.SqrtLog.LayoutProgram.Numerator

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramIntegerEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Literal integer universal constraints from the actual numerator program.
The outer anchor test also suppresses the clearing diagonal outside the joint. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open UniversalEntry RowSelectionProgram MatrixExtendedEntryProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Saved := LayoutProgramScalar.FromCounts.Saved

end SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingProgramSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact finite-port framing for the physical packing controller. -/

namespace SubexponentialSAT.Subexp.PackingProgramSupport

open BitProgram StructuredCalls

theorem registers_injective {r : ℕ} (h : r ≤ 16) : Function.Injective (registers h) := by
  intro i j hij
  exact Fin.ext (congrArg (fun x : Fin 16 => x.val) hij)

abbrev lowCall {r s l : ℕ} (p : Program r s l) (hr : r ≤ 16) (hs : s ≤ 48) : Cmd 16 48 :=
  .call (ProgramLinking.liftProgram p (registers hr) (stackPorts hs))

abbrev copy (src dst tmp : Fin 48) : Cmd 16 48 :=
  .call (StackRoutines.copyProgram src dst tmp 0 1)

abbrev transfer (src dst : Fin 48) : Cmd 16 48 :=
  .call (StackRoutines.transferProgram src dst 0 1)

end SubexponentialSAT.Subexp.PackingProgramSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingEntryEmitter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed emission of one covered packing vertex

The three accumulators are real runtime stacks. Storage receives one reversed
outer record; the two lookup streams receive raw pairs of framed words.
All payloads and counters are data, and every frame is built by fixed programs.
-/
namespace SubexponentialSAT.Subexp.PackingEntryEmitter

open BitProgram StructuredCalls

abbrev Code := Cmd 8 10

def metadataPayload (block typeBytes : List Bool) : List Bool :=
  true :: (Encoding.frame block ++ Encoding.frame typeBytes)

def storageOutput (vertex storage : List Bool) : List Bool :=
  (true :: Encoding.frame vertex).reverse ++ storage

def metadataOutput (vertex typeBytes block metadata : List Bool) : List Bool :=
  Encoding.frame vertex ++ (Encoding.frame (metadataPayload block typeBytes) ++ metadata)

def addressOutput (vertex address addresses : List Bool) : List Bool :=
  Encoding.frame vertex ++ (Encoding.frame address ++ addresses)

@[simp] theorem metadataPayload_length (block typeBytes : List Bool) :
    (metadataPayload block typeBytes).length = 2*block.length+2*typeBytes.length+3 := by
  simp [metadataPayload,Encoding.length_frame]
  omega

@[simp] theorem storageOutput_length (vertex storage : List Bool) :
    (storageOutput vertex storage).length = 2*vertex.length+2+storage.length := by
  simp [storageOutput,Encoding.length_frame]
  omega

@[simp] theorem metadataOutput_length (vertex typeBytes block metadata : List Bool) :
    (metadataOutput vertex typeBytes block metadata).length =
      2*vertex.length+4*block.length+4*typeBytes.length+8+metadata.length := by
  simp [metadataOutput,Encoding.length_frame]
  omega

@[simp] theorem addressOutput_length (vertex address addresses : List Bool) :
    (addressOutput vertex address addresses).length =
      2*vertex.length+2*address.length+2+addresses.length := by
  simp [addressOutput,Encoding.length_frame]
  omega

end SubexponentialSAT.Subexp.PackingEntryEmitter


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingExtractionEmit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Lift the actual covered-entry emitter into the extraction controller. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

open BitProgram StructuredCalls

def emitted (c : Context) (key vertex : List Bool) : Context :=
  { c with
    address := true :: c.address
    storage := PackingEntryEmitter.storageOutput vertex c.storage
    metadata := PackingEntryEmitter.metadataOutput vertex key c.block c.metadata
    addresses := PackingEntryEmitter.addressOutput vertex c.address c.addresses }

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingExtractionBlock
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Scan the ordered type buckets for one complete block. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

open BitProgram StructuredCalls

def emitEntries (i : ℕ) (entries : List Entry) (c : Context) : Context :=
  entries.foldl (fun d e => emitted d e.1 (entryVertex i e)) c

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingExtractionOuter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The fixed outer loop extracts all complete blocks in block-major order. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

open BitProgram StructuredCalls

def advanced (i : ℕ) (entries : List Entry) (c : Context) : Context :=
  let d := emitEntries i entries c
  { d with block := true :: d.block, remaining := d.remaining.tail }

def advanceMany (entries : List Entry) : ℕ → ℕ → Context → Context
  | 0, _, c => c
  | n + 1, i, c => advanceMany entries n (i + 1) (advanced i entries c)

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingLeftoverEmitter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual emission and covered-key lookup for the leftover packing pass. -/
namespace SubexponentialSAT.Subexp.PackingLeftoverEmitter

open BitProgram StructuredCalls

def metadataPayload (rank : List Bool) : List Bool := false :: Encoding.frame rank

def storageOutput (vertex storage : List Bool) : List Bool :=
  (true :: Encoding.frame vertex).reverse ++ storage

def metadataOutput (vertex rank metadata : List Bool) : List Bool :=
  Encoding.frame vertex ++ (Encoding.frame (metadataPayload rank) ++ metadata)

def addressOutput (vertex address addresses : List Bool) : List Bool :=
  Encoding.frame vertex ++ (Encoding.frame address ++ addresses)

end SubexponentialSAT.Subexp.PackingLeftoverEmitter


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

open BitProgram StructuredCalls

def appendVertex (s : Snapshot) (v : ℕ) : Snapshot :=
  ⟨s.rank+1,s.address+1,
    PackingLeftoverEmitter.storageOutput (unary v) s.storage,
    PackingLeftoverEmitter.metadataOutput (unary v) (unary s.rank) s.metadata,
    PackingLeftoverEmitter.addressOutput (unary v) (unary s.address) s.addresses⟩

def covered (records : Records) (v : ℕ) : Bool := (records.lookup (unary v)).isSome

def advance (records : Records) (s : Snapshot) (v : ℕ) : Snapshot :=
  if covered records v then s else appendVertex s v

end SubexponentialSAT.Subexp.PackingLeftovers

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


/-! Closed correction-table construction from type metadata and integer/ring
caches. No correction-scalar table is supplied to the program or theorem. -/


/-! Uniform polynomial accounting and per-index observation of generated
correction tables. All parameters describe actual bytes and runtime counts. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open MulticolorTypes IntegerRingLiftProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram (WordPair )
open scoped BigOperators

/-- Every truncated recurrence count is bounded by R; the two scanned counts
are bounded by Q. This expression is a fixed polynomial in A,R,Q,W,P. -/
def scalarAllowance (A R Q W P : ℕ) : ℕ :=
  14*R+7*A+15+(3*Q+4)+LayoutProgramScalar.FromCounts.binomialCost Q R W+
    (LayoutProgramScalar.numeratorPrepareCost R A W P+
      LayoutProgramScalar.numeratorFoldCost R W P+1)+4*(R*W)+6+1

end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBankCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform numerical bounds for the concrete entry program. The universal
type words affect the result, but no type-dependent search is charged here. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

open SubexponentialSAT.BitProgram SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes RowSelectionProgram

variable {r Q : ℕ}

def integerLength (R W P D : ℕ) : ℕ :=
  R*LayoutProgramScalar.termGrowth (2*W+P)+D+1

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramFrontend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical label/type frontend for arbitrary runtime incidence plans.
The plans have already been produced by the native incidence scan. This
frontend gathers their actual words and generates the complete type alphabet;
it does not accept label records or block metadata as input. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.NativeFrontend

open SubexponentialSAT.Subexp SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.PackingProgramSupport

namespace Params

def base (p : Params) : PackingFrontend.Params :=
  ⟨p.D,p.Δ,[],p.rows,p.width,p.alphabet⟩
def typeRows (p : Params) : List (List Bool) :=
  TupleProgram.powerRows p.alphabet (p.Δ+1) [[]]

end Params

end SubexponentialSAT.SqrtLog.LayoutProgram.NativeFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramPower
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed bit program generates the power-of-two clearing denominator from
its unary exponent. The exponent is runtime data, never control-table size. -/

namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.BinaryArithmetic

abbrev powerRead : Cmd 2 2 := .base (.atom (.pop 0 0 1))
abbrev powerPutZero : Cmd 2 2 := .seq (.base (.atom (.set 0 false)))
  (.base (.atom (.push 1 0)))
abbrev powerLoop : Cmd 2 2 := .while 1 (.seq powerPutZero powerRead)
abbrev powerCommand : Cmd 2 2 :=
  .seq (.base (.atom (.set 0 true)))
    (.seq (.base (.atom (.push 1 0))) (.seq powerRead powerLoop))
def powerProgram := compiled powerCommand 0 1

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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


namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout

open Circuit Bank BinaryArithmetic Asymptotic

def inputMeasure (x : Input) (l : Fin 8 → ℕ) : ℕ := magnitude x+∑ i, l i

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramDispatchCost -/


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Convert a physically scanned factor-index stream to incidence plans. -/


/-! Native per-variable incident-factor scan from the original scope stream. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def indices (scopes : List (List ℕ)) (v : ℕ) := IncidencePlanSpec.incidentIndices scopes v
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan


/-! Fixed cleanup for the native scope-address scanner. -/


/-! Calls to the fixed record mapper inside the native scope scan. -/


/-! One native low-variable step, including its uncovered neutral factor. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Step
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def next (scopes : List (List ℕ)) (v z : ℕ) :=
  if Scan.indices scopes v = [] then z+1 else z
def factors (scopes : List (List ℕ)) (v z : ℕ) :=
  if Scan.indices scopes v = [] then [z] else Scan.indices scopes v
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Step


/-! Runtime high-mask loop for the original-address incidence stream. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Loop
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
def finalCounter (scopes : List (List ℕ)) : ℕ → ℕ → List Bool → ℕ
  | _,z,[] => z
  | v,z,high::rest => finalCounter scopes (v+1)
      (if high then z else Step.next scopes v z) rest
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Loop


/-! Count the physical scope stream before constructing native incidence plans. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Typed original-variable/factor semantics of the native address list. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Semantics
open SubexponentialSAT.Subexp

def entries (scopes : List (List ℕ)) : ℕ → ℕ → List Bool → List (ℕ × ℕ)
  | _,_,[] => []
  | v,z,high::rest => entries scopes (v+1) (if high then z else Step.next scopes v z) rest ++
      if high then [] else (Step.factors scopes v z).map fun e => (v,e)

theorem next_le (scopes : List (List ℕ)) (v z : ℕ) : z ≤ Step.next scopes v z := by
  unfold Step.next; split <;> omega

theorem counter_mono (scopes : List (List ℕ)) (mask : List Bool) :
    ∀ v z, z ≤ Loop.finalCounter scopes v z mask := by
  induction mask with
  | nil => intros; rfl
  | cons high mask ih =>
      intro v z
      cases high
      · exact (next_le scopes v z).trans (ih (v+1) (Step.next scopes v z))
      · exact ih (v+1) z

def nativeEntries (scopes : List (List ℕ)) (mask : List Bool) := entries scopes 0 scopes.length mask
def factorCount (scopes : List (List ℕ)) (mask : List Bool) := Loop.finalCounter scopes 0 scopes.length mask
abbrev Incidences (scopes : List (List ℕ)) (mask : List Bool) := Fin (nativeEntries scopes mask).length
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Semantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Entry from the actual descending high mask produced by the high-variable pass. -/


/-! Raw scopes and the computed mask feed the actual incidence-pair producer. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Finished
open SubexponentialSAT.BitProgram SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp

abbrev incidenceList (scopes : List (List ℕ)) (mask : List Bool) :=
  List.finRange (Semantics.nativeEntries scopes mask).length

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Finished

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyScope
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native-scope specialization of the fixed weighted packing selector. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.SqrtLog.Packing

def pairs (scopes : List (List ℕ)) (mask : List Bool) :=
  (PackingIncidenceInput.Finished.incidenceList scopes mask).product (PackingIncidenceInput.Finished.incidenceList scopes mask)
def terms (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) (Q : ℕ) :
    List (ScoreTerm (PackingIncidenceInput.Semantics.Incidences scopes mask) (Fin n) Q) :=
  (pairs scopes mask).map Sum.inl ++ PackingHeadIncremental.headTerms (List.finRange n)

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope

end OAI.Algorithms
end


