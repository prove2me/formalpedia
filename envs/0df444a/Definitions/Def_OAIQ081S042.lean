-- Prove2me | Definitions.Def_OAIQ081S042
-- name    : OAIQ081S042
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:34:06.200268+00:00
-- url     : https://prove2.me/theorems/1a505542-d1e7-4709-b500-888e29cd7cb2
-- title:
--   Definitions bundle OAIQ081S042 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 143 declarations of OpenAI's Lean: 97 definitions, 2 inductive types or structures, 1 instance and 43 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.literalReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.literalSourceState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.lowScratch`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.nativeRowBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.originKey`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.rowWorkPolynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.shiftBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaFrames.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaFrames.transfer`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgram.Padding.cell`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgram.Padding.output`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgram.Padding.step`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.addCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.mulCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRank.rationalDenominator`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplay.rebaseCfg`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplay.rebaseState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.nodeValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.controllerBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.initializationBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.Index.indexPrefix`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgramTupleCheck.Read.finish`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgramTupleCheck.Read.start`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.PortGraph.HasMixing`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.PortGraph.edgeCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.PortGraph.edgesBetween`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedLocal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedShifts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.shorten`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.totalRows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.FrameData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.erasedOutput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.frameData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.frameReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.put`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram.Store`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram.idle`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram.nativeIdle` and 59 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_ABI`, `SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram`, `SubexponentialSAT_SqrtLogSpace_BooleanDifferences`, `SubexponentialSAT_SqrtLogSpace_CodeCandidates`, `SubexponentialSAT_SqrtLogSpace_CodeChecks`, `SubexponentialSAT_SqrtLogSpace_DifferencePairsProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_BinaryClogProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_BinaryCompareProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSCompletedTree`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSCountProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSVisit`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_NegatedCoreProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseControllerProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseFrontierProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityPrimitives`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointSparsify`, `SubexponentialSAT_SqrtLogSpace_DisjointSparsifyProgram`, `SubexponentialSAT_SqrtLogSpace_FactorAssignmentLoop`, `SubexponentialSAT_SqrtLogSpace_FactorAssignmentProgram`, `SubexponentialSAT_SqrtLogSpace_FactorTableProgram`, `SubexponentialSAT_SqrtLogSpace_FactorTableSpace`, `SubexponentialSAT_SqrtLogSpace_HashTrialStage`, `SubexponentialSAT_SqrtLogSpace_StructuredSpace`, `SubexponentialSAT_SqrtLogSpace_VisitedTape`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyBounds`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyLow`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyNativeLiteral`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyNativeScan`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyOrigin`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyOuter`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyShift`, `SubexponentialSAT_SqrtLog_PerturbationBetaProgramFrames`, `SubexponentialSAT_SqrtLog_PerturbationProgramPadding`, `SubexponentialSAT_SqrtLog_PerturbationProgramPaddingRun`, `SubexponentialSAT_SqrtLog_PolynomialExecutorProgramBounds`, `SubexponentialSAT_SqrtLog_ProducedQueryRankProvenance`, `SubexponentialSAT_SqrtLog_ProgramTapeReplay`, `SubexponentialSAT_SqrtLog_ReconstructionProgramControl`, `SubexponentialSAT_SqrtLog_ReconstructionProgramHorner`, `SubexponentialSAT_SqrtLog_ReconstructionProgramMiddle`, `SubexponentialSAT_SqrtLog_ReconstructionProgramSetup`, `SubexponentialSAT_SqrtLog_RowSelectionProgramIndex`, `SubexponentialSAT_SqrtLog_RowSelectionProgramTupleCheckRead`, `SubexponentialSAT_SqrtLog_SparseCodeBasic`, `SubexponentialSAT_SqrtLog_SparseCodeBounds`, `SubexponentialSAT_SqrtLog_SparseCodeParameters`, `SubexponentialSAT_SqrtLog_SparseCodeShorten`, `SubexponentialSAT_SqrtLog_SparseCodeSupplied`, `SubexponentialSAT_SqrtLog_SquarefreeMaskDecode`, `SubexponentialSAT_SqrtLog_SquarefreeProgramFrame`, `SubexponentialSAT_SqrtLog_SquarefreeProgramScan`, `SubexponentialSAT_SqrtLog_SquarefreeProgramSemantics`, `SubexponentialSAT_SqrtLog_SquarefreeScaleProgram`, `SubexponentialSAT_SqrtLog_SquarefreeSparse`, `SubexponentialSAT_SqrtLog_WalshExistence`, `SubexponentialSAT_SubexpDensePaddingSpec`, `SubexponentialSAT_SubexpRowInterpolation`, `SubexponentialSAT_SubexpTautologyProgram`, `SubexponentialSAT_Subexp_UniversalRowProgram`, `SubexponentialSAT_SunflowerBranch`, `SubexponentialSAT_TruncatedInverse`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S000`, `OAIQ081S001`, `OAIQ081S002`, `OAIQ081S003`, `OAIQ081S004`, `OAIQ081S005`, `OAIQ081S006`, `OAIQ081S007`, `OAIQ081S008`, `OAIQ081S009`, `OAIQ081S011`, `OAIQ081S012`, `OAIQ081S013`, `OAIQ081S015`, `OAIQ081S017`, `OAIQ081S019`, `OAIQ081S020` and `OAIQ081S021` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S063`, `OAIQ081S064`, `OAIQ081S065` and `OAIQ081S066`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localScan_localFactor`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.hasMixing_of_smallWalsh`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.serializedRows_kernel_bound` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.reconstructionBudget_le`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.hasMixing_of_smallWalsh` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.reconstructionBudget_le`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
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
import Definitions.Def_OAIQ081S009
import Definitions.Def_OAIQ081S011
import Definitions.Def_OAIQ081S012
import Definitions.Def_OAIQ081S013
import Definitions.Def_OAIQ081S015
import Definitions.Def_OAIQ081S017
import Definitions.Def_OAIQ081S019
import Definitions.Def_OAIQ081S020
import Definitions.Def_OAIQ081S021

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_ABI
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed disjoint register and stack banks for the counting machine. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ABI

/-- A real finite leaf table is installed in the disjoint upper bank. -/
def leafCall {l : ℕ} (p : BitProgram.Program 40 896 l) : StructuredCalls.Cmd 80 1220 :=
  .call (ProgramLinking.liftProgram p leafRegisters leafStacks)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ABI
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_VisitedTape
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Passive absolute-coordinate instrumentation for the primitive machine.
The interval on every tape includes its initial input cells and every visited
head coordinate. The instrumentation never changes a primitive transition. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open OAI.Algorithms.SubexponentialSAT.Computation
open scoped BigOperators

theorem trace_same_length_unique {α : Type*} {step : α → Option α}
    {a b c : α} {steps : ℕ}
    (hb : Computation.Trace step steps a b)
    (hc : Computation.Trace step steps a c) : b = c :=
  Option.some.inj (hb.iterate.symm.trans hc.iterate)


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StructuredSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Prefix resource preservation for the actual finite instruction linker.
The source bound concerns every intermediate configuration. Unassigned caller
stacks retain their original contents. Local runtime bounds may be used for
polynomial subroutines, but no accumulated outer-loop time appears here. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace

open BitProgram

def commandLabel {r s L : ℕ} (c : StructuredCalls.Cmd r s)
    (embed : StructuredCalls.Site c → Fin L) (exit : Fin L) :
    Fin (StructuredCalls.size c + 1) → Fin L := fun pc =>
  match (StructuredCalls.labelEquiv c).symm pc with
  | none => exit
  | some site => embed site

@[simp] theorem commandLabel_site {r s L : ℕ} (c : StructuredCalls.Cmd r s)
    (embed : StructuredCalls.Site c → Fin L) (exit : Fin L)
    (site : StructuredCalls.Site c) :
    commandLabel c embed exit (StructuredCalls.siteAddress c site) = embed site := by
  change (match (StructuredCalls.siteEquiv c).optionCongr.symm
    ((StructuredCalls.siteEquiv c).optionCongr (some site)) with
    | none => exit
    | some site => embed site) = embed site
  rw [Equiv.symm_apply_apply]

@[simp] theorem commandLabel_exit {r s L : ℕ} (c : StructuredCalls.Cmd r s)
    (embed : StructuredCalls.Site c → Fin L) (exit : Fin L) :
    commandLabel c embed exit (StructuredCalls.exitAddress c) = exit := by
  change (match (StructuredCalls.siteEquiv c).optionCongr.symm
    ((StructuredCalls.siteEquiv c).optionCongr none) with
    | none => exit
    | some site => embed site) = exit
  rw [Equiv.symm_apply_apply]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SunflowerBranch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Literal-set sunflower branching

Concrete CNF children and their semantic union, together with the absorption
invariants used by the cumulative-insertion argument. Opposite polarities are
distinct literals; no variable-disjointness premise is used.
-/

namespace SubexponentialSAT.SunflowerBranch

open SubexponentialSAT.SAT

universe u
variable {V : Type u} [DecidableEq V]

/-- The antichain convention at each normalized node. -/
def Antichain (F : CNF V) : Prop :=
  ∀ C ∈ F, ∀ D ∈ F, C ⊆ D → C = D

end SubexponentialSAT.SunflowerBranch

namespace SubexponentialSAT.SunflowerBranch

open SubexponentialSAT.SAT
universe u
variable {V : Type u} [DecidableEq V]

/-- Extract the petals by removing a known common core. -/
def petalFamily (F : CNF V) (H : Clause V) : CNF V :=
  F.image fun C => C \ H

end SubexponentialSAT.SunflowerBranch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Native full-key computation for the resumable attained-signature scan

One invocation preserves the assignment and all raw integer constraint rows.
Its local polynomial-time bound controls every scratch stack at every source
prefix. The generator retains candidate and predecessor cursors separately.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

namespace Rescan

def keyBound (W : List Bool) (h d B : ℕ) : ℕ :=
  d * (2 * (widthBound W h B + 1) + 1)

end Rescan

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_BooleanDifferences
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Boolean finite differences (ETH, Lemma `boolean-differences`).
The finite sets in this module specify sums; they are not operational enumerators. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.BooleanDifferences

open scoped BigOperators

variable {V R : Type*} [DecidableEq V] [CommRing R]

@[simp] theorem evalAt_monomial (U : Finset V) (d : V →₀ ℕ) (c : R) :
    evalAt U (MvPolynomial.monomial d c) = if d.support ⊆ U then c else 0 := by
  classical
  rw [evalAt, MvPolynomial.eval_monomial, Finsupp.prod]
  by_cases h : d.support ⊆ U
  · rw [ite_eq_left h, Finset.prod_eq_one (fun v hv => by simp [h hv]), mul_one]
  · obtain ⟨v, hv, hvU⟩ := Finset.not_subset.mp h
    have hd : d v ≠ 0 := Finsupp.mem_support_iff.mp hv
    rw [Finset.prod_eq_zero hv (by simp [hvU, hd]), mul_zero, ite_eq_right h]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.BooleanDifferences
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_TruncatedInverse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit finite geometric inversion and local CRT factors

The inverses in this file are finite polynomial expressions. Scalar inverses are
input data with multiplication certificates; no Bézout coefficients are chosen.
-/

noncomputable section

namespace SubexponentialSAT.TruncatedInverse

open Polynomial
open scoped BigOperators

variable {A : Type*} [CommRing A]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The other nodes' factors, expressed in node `i`'s local coordinate. -/
def localFactor (θ : ι → A) (D : ℕ) (i : ι) : A[X] :=
  (JetCRT.cofactor θ D i).comp (X + C (θ i))

end SubexponentialSAT.TruncatedInverse

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CodeCandidates
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The retained domain of the code search is one word of two-bit scalars.
The tuple counter visits all four digits; the physical converter rejects the
unused digits and produces the original scalar-frame arithmetic format. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidates

open SubexpEnumerationPayload

def scalarFrames (xs : List (Bool × Bool)) : List Bool :=
  xs.flatMap (Encoding.frame ∘ digitBits)

@[simp] theorem scalarFrames_length (xs : List (Bool × Bool)) :
    (scalarFrames xs).length = 5 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [scalarFrames, digitBits] at *; omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidates
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Shared interfaces for sparse ternary parity checks

The definitions distinguish edge coordinates from graph vertices. Parallel
edges have different ports. All construction theorems built on these interfaces
must eventually discharge the local-distance and graph-mixing hypotheses.
-/

namespace SubexponentialSAT.SqrtLog.SparseCode

open scoped BigOperators

namespace PortGraph

variable {V P : Type*} [Fintype V] [Fintype P] [DecidableEq V]

def edgesBetween (G : PortGraph V P) (U W : Finset V) : Finset (V × P) :=
  Finset.univ.filter fun e => e.1 ∈ U ∧ (G.rotation e).1 ∈ W

def edgeCount (G : PortGraph V P) (U W : Finset V) : ℕ :=
  (G.edgesBetween U W).card

/-- The only spectral consequence needed by the global distance proof. -/
def HasMixing (G : PortGraph V P) (ε : ℝ) : Prop :=
  ∀ U W : Finset V,
    (G.edgeCount U W : ℝ) ≤
      (Fintype.card P : ℝ) * U.card * W.card / Fintype.card V +
      ε * Fintype.card P * Real.sqrt ((U.card : ℝ) * W.card)

end PortGraph

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_WalshExistence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Existence and finite executable search for a small Walsh spectrum. -/
namespace SubexponentialSAT.SqrtLog.WalshExistence

open scoped BigOperators
open Cayley

def Good {r D : ℕ} (q : ℕ) (s : Fin D → Cube r) : Prop :=
  ∀ a, a ≠ 0 → (q : ℤ) * |walshInt s a| ≤ D

instance instDecidableGood {r D : ℕ} (q : ℕ) (s : Fin D → Cube r) : Decidable (Good q s) :=
  inferInstanceAs (Decidable (∀ a, a ≠ 0 → (q : ℤ) * |walshInt s a| ≤ D))

end SubexponentialSAT.SqrtLog.WalshExistence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CodeChecks
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Space of the concrete sparse-code predicates

The local-code and Walsh predicates are polynomial-time bit programs. These bounds apply
to every candidate, including losing candidates, and every stack in each actual source
prefix. They are intended as the body estimates of bounded-memory enumeration; the
materialized candidate-family programs are not used here.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

def graphStreamBudget (D r qlen Dlen : ℕ) : ℕ :=
  4 ^ r * (graphCallbackBudget D r qlen Dlen + 110 * r + 36) + 3

def localStreamBudget (t D d : ℕ) : ℕ :=
  4 ^ D * (callbackBudget t D d + 110 * D + 36) + 3

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DifferencePairsProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed finite control for the pruned pair DFS. Four protected stacks hold
remaining depth, remaining strict budget, and the two current masks. The masks
also encode the DFS phases `00`, `10`, `11`; no completed-pair list is retained.
The callback receives the masks in reverse coordinate order. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram

open OAI.Algorithms.SubexponentialSAT.StructuredProgram (Atom)
open OAI.Algorithms.SubexponentialSAT.StructuredCalls

variable {r s : ℕ}

def atoms (code : List (Atom r s)) : Cmd r s :=
  .base (code.foldr (fun a rest => .seq (.atom a) rest) .skip)

def pushBit (p : Ports r s) (i : Fin 4) (b : Bool) : Cmd r s :=
  atoms [.set (p.register 2) b, .push (p.stack i) (p.register 2)]

def pushed (p : Ports r s) (i : Fin 4) (b : Bool) (d : State r s) : State r s :=
  ⟨Function.update d.regs (p.register 2) b,
    Function.update d.stacks (p.stack i) (b :: d.stacks (p.stack i))⟩

def enter (p : Ports r s) (e u : Bool) : Cmd r s :=
  .seq (pushBit p 2 e) (.seq (pushBit p 3 u) (atoms [.set (p.register 0) true]))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_BinaryClogProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual floor and ceiling logarithm bit programs, without packing or schedule imports. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Floor

open OAI.Algorithms.SubexponentialSAT.BitProgram
open OAI.Algorithms.SubexponentialSAT.CounterPrograms

def atoms {r s : ℕ} : List (StructuredProgram.Atom r s) → StructuredProgram.Cmd r s
  | [] => .skip
  | op :: ops => .seq (.atom op) (atoms ops)

/-- Four low bits are discarded; the two read registers are then cleared. -/
def trimProgram : Program 3 3 6 where
  inputStack := 1
  outputStack := 1
  entry := 0
  code q := match q.val with
    | 0 => .pop 1 0 1 1
    | 1 => .branch 1 2 3
    | 2 => .branch 0 3 0
    | 3 => .set 0 false 4
    | 4 => .set 1 false 5
    | _ => .halt

@[simp] theorem update_lengthStacks_one (a b c d : List Bool) :
    Function.update (lengthStacks a b c) 1 d = lengthStacks a d c := by
  funext i
  fin_cases i <;> simp [lengthStacks]

/-! ## Concrete input reversal -/

def reverseTransfer : Program 3 3 4 := StackRoutines.transferProgram 0 1 0 1

def prepareLogProgram : Program 3 3 10 := ProgramLinking.link reverseTransfer trimProgram

/-! ## Reindex and call the checked binary word-length counter -/

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Floor
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_BinaryCompareProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Minimal actual binary comparison, extracted from SubexpGuardProgram.
Only the concrete Boolean borrow operation and fixed comparison machine are retained.
The source map and hashes are recorded in verification/counting-draft/worker04/extraction.json. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryCompareProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.BinaryArithmetic

namespace Compare

/-- Eight one-bit registers, two stacks, and twelve fixed labels. Register zero
is the result; both operand stacks are consumed. Entry resets the borrow bit. -/
def program : Program 8 2 12 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code q := match q.val with
    | 0 => .set 0 false 1
    | 1 => .pop 0 1 3 2
    | 2 => .pop 1 2 4 3
    | 3 => .bor 5 3 4 4
    | 4 => .branch 5 5 11
    | 5 => .bnot 6 1 6
    | 6 => .band 6 6 2 7
    | 7 => .bxor 7 1 2 8
    | 8 => .bnot 7 7 9
    | 9 => .band 7 7 0 10
    | 10 => .bor 0 6 7 1
    | _ => .halt

def cfg (pc : Option (Fin 12)) (regs : Fin 8 → Bool) (xs ys : List Bool) : Cfg 8 2 12 :=
  ⟨pc, regs, operandStacks xs ys⟩

def read (regs : Fin 8 → Bool) (a b : Option Bool) : Fin 8 → Bool :=
  readRegs (readRegs regs 1 3 a) 2 4 b

def roundRegs (regs : Fin 8 → Bool) (a b : Option Bool) : Fin 8 → Bool :=
  let r := read regs a b
  let r := Function.update r 5 (a.isSome || b.isSome)
  let r := Function.update r 6 (!a.getD false)
  let r := Function.update r 6 ((!a.getD false) && b.getD false)
  let r := Function.update r 7 (a.getD false ^^ b.getD false)
  let r := Function.update r 7 (!(a.getD false ^^ b.getD false))
  let r := Function.update r 7 ((!(a.getD false ^^ b.getD false)) && regs 0)
  Function.update r 0 (((!a.getD false) && b.getD false) ||
    ((!(a.getD false ^^ b.getD false)) && regs 0))

def exitRegs (regs : Fin 8 → Bool) : Fin 8 → Bool :=
  Function.update (read regs none none) 5 false

@[simp] theorem exitRegs_borrow (regs : Fin 8 → Bool) : exitRegs regs 0 = regs 0 := by
  simp [exitRegs, read, readRegs]

end Compare

open StructuredProgram

/-- Restrict caller data to the fixed ports of a subroutine. This is assertion
notation, not an instruction available to the program. -/
def restrictState {R S : ℕ} (register : Fin 8 → Fin R) (stack : Fin 2 → Fin S)
    (a : State R S) : State 8 2 :=
  ⟨fun i => a.regs (register i), fun i => a.stacks (stack i)⟩


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryCompareProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointSparsify
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Appendix A: literal-core branching with disjoint exact-count children. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranch

open OAI.Algorithms.SubexponentialSAT.SAT

universe u
variable {V : Type u} [DecidableEq V]

/-- All clauses of the chosen width containing the chosen core. -/
def selected (F : CNF V) (c : ℕ) (H : Clause V) : CNF V :=
  F.filter fun C => C.card = c ∧ H ⊆ C

/-- Petals are remainders, with no disjointness requirement between them. -/
def petals (F : CNF V) (c : ℕ) (H : Clause V) : CNF V :=
  SunflowerBranch.petalFamily (selected F c H) H

/-- Unit clauses forcing every core literal to be false. -/
def negatedCoreUnits (H : Clause V) : CNF V :=
  H.image fun l => {l.negate}

/-- Only genuinely new clauses are counted as insertion events. -/
def insertedB (F : CNF V) (c : ℕ) (H : Clause V) : CNF V :=
  (petals F c H ∪ negatedCoreUnits H) \ F

@[simp] theorem mem_selected {F : CNF V} {c : ℕ} {H C : Clause V} :
    C ∈ selected F c H ↔ C ∈ F ∧ C.card = c ∧ H ⊆ C :=
  Finset.mem_filter

theorem selected_subset (F : CNF V) (c : ℕ) (H : Clause V) :
    selected F c H ⊆ F := Finset.filter_subset _ _

theorem petal_card {F : CNF V} {c : ℕ} {H P : Clause V}
    (hP : P ∈ petals F c H) : P.card = c - H.card := by
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hP
  rw [Finset.card_sdiff,
    Finset.inter_eq_left.mpr (mem_selected.mp hC).2.2,
    (mem_selected.mp hC).2.1]

theorem core_strict_subset {F : CNF V} {c : ℕ} {H C : Clause V}
    (hC : C ∈ selected F c H) (hproper : H.card < c) : H ⊂ C := by
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨(mem_selected.mp hC).2.2, ?_⟩
  intro h
  have hc := (mem_selected.mp hC).2.1
  rw [← h] at hc
  omega

theorem petal_strict_subset {F : CNF V} {c : ℕ} {H C : Clause V}
    (hC : C ∈ selected F c H) (hH : H.Nonempty) : C \ H ⊂ C :=
  Finset.sdiff_ssubset (mem_selected.mp hC).2.2 hH

theorem no_old_subset_core {F : CNF V} {c : ℕ} {H E : Clause V}
    (hF : SunflowerBranch.Antichain F) (hsel : (selected F c H).Nonempty)
    (hproper : H.card < c) (hE : E ∈ F) : ¬ E ⊆ H := by
  intro hEH
  obtain ⟨C, hC⟩ := hsel
  have hHC := core_strict_subset hC hproper
  have hEC := hF E hE C (selected_subset F c H hC)
    (hEH.trans (Finset.ssubset_iff_subset_ne.mp hHC).1)
  have hCH : C ⊆ H := hEC ▸ hEH
  exact (Finset.ssubset_iff_subset_ne.mp hHC).2
    (Finset.Subset.antisymm (mem_selected.mp hC).2.2 hCH)

theorem no_old_subset_petal {F : CNF V} {c : ℕ} {H P E : Clause V}
    (hF : SunflowerBranch.Antichain F) (hH : H.Nonempty)
    (hP : P ∈ petals F c H) (hE : E ∈ F) : ¬ E ⊆ P := by
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hP
  intro hEP
  have hEC := hF E hE C (selected_subset F c H hC) (hEP.trans Finset.sdiff_subset)
  have hCP : C ⊆ C \ H := hEC ▸ hEP
  exact (Finset.ssubset_iff_subset_ne.mp (petal_strict_subset hC hH)).2
    (Finset.Subset.antisymm Finset.sdiff_subset hCP)

theorem core_new {F : CNF V} {c : ℕ} {H : Clause V}
    (hF : SunflowerBranch.Antichain F) (hsel : (selected F c H).Nonempty)
    (hproper : H.card < c) : H ∉ F := by
  intro hH
  exact no_old_subset_core hF hsel hproper hH (Finset.Subset.refl _)

theorem petal_new {F : CNF V} {c : ℕ} {H P : Clause V}
    (hF : SunflowerBranch.Antichain F) (hH : H.Nonempty)
    (hP : P ∈ petals F c H) : P ∉ F := by
  intro hPF
  exact no_old_subset_petal hF hH hP hPF (Finset.Subset.refl _)

theorem parent_clause_nonempty {F : CNF V} {c : ℕ} {H C : Clause V}
    (hF : SunflowerBranch.Antichain F) (hsel : (selected F c H).Nonempty)
    (hproper : H.card < c) (hC : C ∈ F) : C.Nonempty := by
  by_contra h
  have he := Finset.not_nonempty_iff_eq_empty.mp h
  exact no_old_subset_core hF hsel hproper hC (by rw [he]; exact Finset.empty_subset _)

theorem rawB_clause_nonempty {F : CNF V} {c : ℕ} {H C : Clause V}
    (hF : SunflowerBranch.Antichain F) (hsel : (selected F c H).Nonempty)
    (hproper : H.card < c)
    (hC : C ∈ ((F \ selected F c H) ∪ petals F c H) ∪ negatedCoreUnits H) :
    C.Nonempty := by
  rcases Finset.mem_union.mp hC with hC | hC
  · rcases Finset.mem_union.mp hC with hC | hC
    · exact parent_clause_nonempty hF hsel hproper (Finset.mem_sdiff.mp hC).1
    · apply Finset.card_pos.mp
      rw [petal_card hC]
      exact Nat.sub_pos_of_lt hproper
  · obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hC
    exact Finset.singleton_nonempty _

theorem petals_subset_insertedB {F : CNF V} {c : ℕ} {H : Clause V}
    (hF : SunflowerBranch.Antichain F) (hH : H.Nonempty) :
    petals F c H ⊆ insertedB F c H := by
  intro P hP
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hP, petal_new hF hH hP⟩

theorem insertedB_disjoint (F : CNF V) (c : ℕ) (H : Clause V) :
    Disjoint F (insertedB F c H) := Finset.disjoint_sdiff

theorem insertedB_nonempty {F : CNF V} {c : ℕ} {H P : Clause V}
    (hproper : H.card < c) (hP : P ∈ insertedB F c H) : P.Nonempty := by
  rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hP).1 with hP | hP
  · apply Finset.card_pos.mp
    rw [petal_card hP]
    exact Nat.sub_pos_of_lt hproper
  · obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hP
    exact Finset.singleton_nonempty _

theorem insertedB_width_lt {F : CNF V} {c : ℕ} {H P : Clause V}
    (hH : H.Nonempty) (hproper : H.card < c) (hP : P ∈ insertedB F c H) :
    P.card < c := by
  have hHpos := Finset.card_pos.mpr hH
  rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hP).1 with hP | hP
  · rw [petal_card hP]
    omega
  · obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hP
    rw [Finset.card_singleton]
    omega

open scoped BigOperators

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranch
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseControllerProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete control composition for fixed finite bit commands. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram.Controller

open BitProgram StructuredCalls

/-- The list is part of finite control, chosen with `k`, not an input table. -/
def firstHit {R S : ℕ} (flag : Fin R) : List (Cmd R S) → Cmd R S
  | [] => .base .skip
  | command :: rest => .ite flag (.base .skip) (.seq command (firstHit flag rest))


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram.Controller
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseFrontierProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete LIFO storage for normalized formula bodies.

Stack zero is the current body, stack two is the framed pending list, and stack
three is scratch. Stack one is preserved and may hold the declared variable
count. The list's final false bit is retained; emptiness is tested by peeking,
so an empty frontier never causes an unguarded removal of a sentinel.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseFrontierProgram

open BitProgram StructuredCalls SubexpPostfixControl

def transfer (src dst : Fin 4) : Cmd 3 4 :=
  .call (StackRoutines.transferProgram src dst (0 : Fin 3) 1)

/-- The test preserves every stack, including the empty-list sentinel. -/
def test : Cmd 3 4 := .base (.atom (.peek 2 2 1))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseFrontierProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete record-count and emission primitives extracted from supplied sources.
No sparsification schedule or formula evaluator is imported. Provenance is recorded
in verification/counting-draft/worker04/extraction.json. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityPrimitives

open BitProgram StructuredCalls BinaryArithmetic

namespace Tuple

def copy (src dst : Fin 9) : Cmd 13 9 :=
  .call (StackRoutines.copyProgram src dst 8 0 1)

def compare (left right : Fin 9) : Cmd 13 9 :=
  .call (ProgramLinking.liftProgram BinaryCompareProgram.Compare.program workReg (pairPort left right))

end Tuple

namespace Count

open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityPrimitives.Tuple
  (copy )

def less (left right : Fin 9) : Cmd 13 9 :=
  .seq (copy left 5) (.seq (copy right 7) (Tuple.compare 5 7))

end Count

namespace FrameWriter

@[simp] theorem update_triple_zero {α : Type*} (a b c d : α) :
    Function.update (triple a b c) 0 d = triple d b c := by
  funext i
  fin_cases i <;> simp [triple]

@[simp] theorem update_triple_one {α : Type*} (a b c d : α) :
    Function.update (triple a b c) 1 d = triple a d c := by
  funext i
  fin_cases i <;> simp [triple]

@[simp] theorem update_triple_two {α : Type*} (a b c d : α) :
    Function.update (triple a b c) 2 d = triple a b d := by
  funext i
  fin_cases i <;> simp [triple]

@[simp] theorem update_quadruple_zero {α : Type*} (a b c d e : α) :
    Function.update (quadruple a b c d) 0 e = quadruple e b c d := by
  funext i; fin_cases i <;> simp [quadruple]
@[simp] theorem update_quadruple_one {α : Type*} (a b c d e : α) :
    Function.update (quadruple a b c d) 1 e = quadruple a e c d := by
  funext i; fin_cases i <;> simp [quadruple]
@[simp] theorem update_quadruple_two {α : Type*} (a b c d e : α) :
    Function.update (quadruple a b c d) 2 e = quadruple a b e d := by
  funext i; fin_cases i <;> simp [quadruple]
@[simp] theorem update_quadruple_three {α : Type*} (a b c d e : α) :
    Function.update (quadruple a b c d) 3 e = quadruple a b c e := by
  funext i; fin_cases i <;> simp [quadruple]


end FrameWriter

namespace Filter

def resetFilterFlags : StructuredProgram.Cmd 3 4 :=
  .seq (.atom (.set 0 false)) (.seq (.atom (.set 1 true)) (.atom (.set 2 false)))


end Filter

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityPrimitives
end

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

/-- Raw-list specification of the selected family; all runtime tests are bit programs below. -/
def selectedRaw {α : Type*} [DecidableEq α] (F : List (List α)) (c : ℕ)
    (H : List α) : List (List α) :=
  F.filter fun C => decide (C.length = c) && ExecCNF.subset H C

def rawCandidates {α : Type*} (k : ℕ) (F : List (List α)) : List (ℕ × List α) :=
  F.flatMap fun C => (masks k).map fun mask => (C.length, masked mask C)

/-- A scan certificate records only tested candidates and preceding failed tests. -/
structure RawPriority {α : Type*} [DecidableEq α] (k : ℕ) (F : List (List α))
    (M c : ℕ) (H : List α) : Prop where
  candidate : (c, H) ∈ rawCandidates k F
  core_nonempty : 0 < H.length
  core_proper : H.length < c
  threshold : M ^ (c - H.length) ≤ (selectedRaw F c H).length
  minimum : ∀ d core, (d, core) ∈ rawCandidates k F → 0 < core.length → core.length < d →
    d < c → (selectedRaw F d core).length < M ^ (d - core.length)
  maximum : ∀ core, (c, core) ∈ rawCandidates k F → H.length < core.length → core.length < c →
    (selectedRaw F c core).length < M ^ (c - core.length)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTautologyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual encoded-clause tautology testing

The outer iterator reads unary literal records. For each literal, a concrete
program builds its opposite's query, copies the preserved clause, and runs the
proved encoded membership program. All data-dependent repetition is in those
finite programs and the record iterator.
-/

namespace SubexponentialSAT.SubexpTautologyProgram

open BitProgram StructuredCalls

def encodedClause (C : List ℕ) : List Bool := Encoding.encodeList Encoding.encodeNat C

end SubexponentialSAT.SubexpTautologyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_NegatedCoreProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete negated singleton generation for the disjoint B child.
The fixed routine consumes a unary literal-record list on stack 0 and prepends
its negated singleton clauses to the encoded formula on stack 2. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.NegatedCoreProgram

open BitProgram StructuredCalls

abbrev clauseCode := SubexpTautologyProgram.encodedClause

def formulaCode (F : List (List ℕ)) : List Bool :=
  Encoding.encodeList clauseCode F

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.NegatedCoreProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointSparsifyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! List-level outputs for the concrete disjoint splitter.
The declared variable universe is retained by the surrounding controller.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram

open OAI.Algorithms.SubexponentialSAT.SAT

open BitProgram StructuredCalls

def copyCore : Cmd 15 16 := .call (StackRoutines.copyProgram 9 0 10 0 1)

open ExecBranchControllerSupport

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSCompletedTree
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! A completed concrete transition history determines a proof-only branch
forest backwards. This transfers the sharp tree-node bound to the actual
number of visits, without storing a tree or list of visits on the machine.
-/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCompletedTree

open SparseDFSRefinement
variable {n : ℕ}

def nodes (trees : List BranchTree.Tree) : ℕ := (trees.map BranchTree.Tree.nodeCount).sum

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCompletedTree
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSVisit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! One complete native DFS visit. The leaf callback below is an intermediate
implementation contract for a fixed finite command, not a final theorem premise.
The actual streamed leaf program must instantiate it at integration.
-/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit

open BitProgram StructuredCalls SparseDFSProgram SparseDFSRefinement

variable {n : ℕ}

def visitTime (k n bodyLength thresholdLength leafTime bound : ℕ) : ℕ :=
  9 * bodyLength + 11 +
    (SparsePriorityProgram.Selector.selectorCoefficient k * (bodyLength + thresholdLength + 1) ^ 4 + 1 +
      (max (621000 * (4 * bodyLength + 3) ^ 2) (leafTime + 100 * (n + 1)) + 1 +
        ((2 * bound + 3) * 257 + 1)))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSCountProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete count command including startup and physical full-word export.
The actual positivity suffix is appended by the shared native integration.
-/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCountProgram

open BitProgram StructuredCalls SparseDFSProgram SparseDFSRefinement DFSVisit
variable {n : ℕ}

/-- An explicit numerical sum of the four independently proved local resource
requirements. It contains no traversal count or exponential time term. -/
def visitSpace (k n m thresholdLength : ℕ) : ℕ :=
  let P := SparseCountProgram.formulaBound n k
  let Q := SparseDFSBoundarySpace.frontierBound P (m * k)
  (n + 1 + Q + 11 * P + 13) +
    ((SparsePriorityProgram.Selector.selectorCoefficient k + 24) * (P + thresholdLength + 1) ^ 4) +
    (Q + (n + 1) + 620001 * (4 * P + 3) ^ 2) + 100 * (n + 1)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCountProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSparse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Computable normalized sparse coefficient lists. Zero coefficients may stay
in the list; keys are unique, so this does not enlarge the finite index bound.
No equality decision for coefficients or full ambient Boolean table is used. -/

namespace SubexponentialSAT.SqrtLog.Squarefree.Sparse

open scoped BigOperators

variable {K R A : Type*} [DecidableEq K] [AddCommMonoid R]

def insert (k : K) (c : R) (l : Data K R) : Data K R :=
  (k, c + fetch k l) :: erase k l

end SubexponentialSAT.SqrtLog.Squarefree.Sparse

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed frame emitter. The source is a reversed payload. It is consumed
and the forward framed payload is prepended to the destination. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

abbrev FrameData := State 3 2

def frameData (regs : Fin 3 → Bool) (source output : List Bool) : FrameData :=
  ⟨regs, ![source, output]⟩

def frameReady (regs : Fin 3 → Bool) (source output : List Bool) : FrameData :=
  frameData (readRegs regs 0 1 source.head?) source.tail output

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime-sized dictionary deletion. One fixed loop visits every encoded
record and retains every nonmatching record, reversing record order. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

abbrev erasedOutput (query : List Bool) : List ByteRecord → List Bool → List Bool
  | [], output => output
  | (key,payload) :: rest, output => erasedOutput query rest
      (if key = query then output else Encoding.frame key ++ Encoding.frame payload ++ output)

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Semantic contract of the primitive dictionary replacement, including its
use as the storage step of normalized additive insertion. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram

variable {K C A : Type*} [DecidableEq K] [AddCommMonoid C]

def put (k : K) (c : C) (entries : Sparse.Data K C) : Sparse.Data K C :=
  (k,c) :: (Sparse.erase k entries).reverse

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeScaleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Base stage. -/
/-! Fixed physical ABI for scaling all coefficients in a sparse dictionary.
The low 32 stacks are the common coefficient-ring service. The eight high
stacks hold source, reversed output, scalar, key, coefficient staging, frame
staging, final output, and a preserved copy of the unary degree. -/

namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

structure Store where
  native : RingScan.ServiceStore
  source : List Bool := []
  accum : List Bool := []
  scalar : List Bool := []
  key : List Bool := []
  coeff : List Bool := []
  frame : List Bool := []
  output : List Bool := []
  count : List Bool := []

def tapes (s : Store) (i : Fin 40) : List Bool :=
  if i = 0 then s.native.result else if i = 5 then s.native.modulus
  else if i = 8 then s.native.x else if i = 9 then s.native.y
  else if i = 11 then s.native.degree else if i = 12 then s.native.width
  else if i = 15 then s.native.outer else if i = 16 then s.native.inner
  else if i = 17 then s.native.zero else if i = 20 then s.native.tableWork
  else if i = 21 then s.native.reverseStream else if i = 22 then s.native.table
  else if i = 23 then s.native.stream else if i = 32 then s.source
  else if i = 33 then s.accum else if i = 34 then s.scalar
  else if i = 35 then s.key else if i = 36 then s.coeff
  else if i = 37 then s.frame else if i = 38 then s.output
  else if i = 39 then s.count else []

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Moves stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

def nativeIdle (e : Environment) : RingScan.ServiceStore :=
  { modulus := e.modulus, result := [], x := [], y := [], degree := [],
    width := e.width, zero := e.zero, table := e.table }

def idle (e : Environment) (source accum : List Bool) : Store :=
  ⟨nativeIdle e, source, accum, e.scalar, [], [], [], [], e.count⟩

def prepared (e : Environment) (key coeff tail accum : List Bool) : Store :=
  {idle e tail accum with
    key := key.reverse
    native := {nativeIdle e with x := e.scalar, y := coeff, degree := e.count}}

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Emit stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

def productReady (e : Environment) (key result tail accum : List Bool) : Store :=
  {idle e tail accum with
    key := key.reverse
    native := {nativeIdle e with result := result}}

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Native stage. -/

/-! Loop stage. -/

/-! Cost stage. -/

/-! Semantics stage. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramTupleCheckRead
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The raw natural-field reader. Its stopping delimiter is consumed, while
all subsequent fields and all other bank are preserved. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgramTupleCheck.Read
open SubexponentialSAT.BitProgram

def start {r s : ℕ} (regs : Fin r → Bool) (bank : Fin s → List Bool) : Cfg r s 4 :=
  ⟨some 0, regs, bank⟩

def finish {r s : ℕ} (src dst : Fin s) (value present : Fin r)
    (regs : Fin r → Bool) (bank : Fin s → List Bool) (n : ℕ) (tail : List Bool) : Cfg r s 4 :=
  ⟨none, readRegs regs value present (some false),
    Function.update (Function.update bank src tail) dst (List.replicate n true ++ bank dst)⟩

end SubexponentialSAT.SqrtLog.RowSelectionProgramTupleCheck.Read

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpDensePaddingSpec
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-width bit padding and dense polynomial coefficients

The literal loader pads or truncates a flat payload to a whole number of
coefficient cells. This file identifies that operation at the cell level.
Preservation of a complete polynomial requires its degree to be below the
number of retained cells; this condition is explicit before any Taylor shift.
-/

namespace SubexponentialSAT.SubexpDensePaddingSpec

open ModularArithmetic

section Expressions

variable {B S R : Type*} [CommRing R]

/-- Value-level execution with the same literal/add/multiply operations that
the postfix services refine. No denotation function is used during execution. -/
def evalWith (literal : B → S) (add mul : S → S → S) : Algorithm.Expr B → S
  | .lit b => literal b
  | .add e f => add (evalWith literal add mul e) (evalWith literal add mul f)
  | .mul e f => mul (evalWith literal add mul e) (evalWith literal add mul f)

end Expressions

end SubexponentialSAT.SubexpDensePaddingSpec

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial bit bounds for the fixed source interpreter. Source size and
raw literal bytes are charged separately from the retained coefficient count. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

def addCost (B d J : ℕ) : ℕ :=
  binaryBound (DensePolynomialProgram.AddService.budget d B J J) (J*(d*B))
def mulCost (B d J : ℕ) : ℕ :=
  binaryBound (DensePolynomialProgram.nativeMulBudget J d B) (J*(d*B))


end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

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

section FieldUnits

variable {F : Type*} [Field F]

/-- Construct the unit data directly from field inversion and its laws. -/
def NodeUnits.ofField (node : I → F) (hinj : Function.Injective node)
    (hne : ∀ i, node i ≠ 0) : NodeUnits node where
  nodeUnit i := Units.mk0 (node i) (hne i)
  nodeUnit_val _ := rfl
  differenceUnit i j hij := Units.mk0 (node i - node j)
    (fun h => hij (hinj (sub_eq_zero.mp h)))
  differenceUnit_val _ _ _ := rfl

end FieldUnits

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
open SubexpKernelControl (Word )

def factorExpression {R : Type*} (x : R) (f : Factor R) : Algorithm.Expr R :=
  .mul (.lit f.inverseDifference) (.add (.lit x) (.lit f.negativeNode))

def termExpression {R : Type*} [One R] (x : R) (t : Term R) : Algorithm.Expr R :=
  .mul (.lit t.value) (.mul (.mul (.lit t.inverseNode) (.lit x))
    (Algorithm.Expr.product (t.factors.map (factorExpression x))))

end SubexponentialSAT.Subexp.UniversalRowProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationProgramPadding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit finite scalar-to-polynomial padding. The runtime degree and
coefficient width are tapes, so this command is independent of all dimensions. -/
namespace SubexponentialSAT.SqrtLog.PerturbationProgram.Padding
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram.Constructor

def cell (D W : ℕ) (bits : List Bool) : List Bool :=
  Counter.paddedBits W bits (List.replicate W false) D

def step {C : Type*} (encode : C → List Bool) (D W : ℕ)
    (acc : List Bool) (c : C) : List Bool := cell D W (encode c)++acc

end SubexponentialSAT.SqrtLog.PerturbationProgram.Padding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationProgramPaddingRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PerturbationProgram.Padding
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl

def output {C : Type*} (encode : C → List Bool) (D W : ℕ) (cs : List C) : List Bool :=
  cs.flatMap fun c => cell D W (encode c)

end SubexponentialSAT.SqrtLog.PerturbationProgram.Padding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyShift
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native composition from a complete scalar coefficient row to its shifted
jet. Padding and both runtime counters are executed, rather than supplied. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open PerturbationProgram
open CRTLocalProgram (LowFrame )

def shiftBudget (N J W Km Ka : ℕ) : ℕ :=
  (6*(N*W)+7*N+7*W+16) + Padding.budget N J W +
  (6*(N*J*W)+7*N+2*W+14*(J*W)+24) +
  HornerProgram.budget N (J*W) Km Ka + (2*(J*W)+3)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationBetaProgramFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed16/256 frame primitives for beta evaluation. These use the immutable
reader and transfer programs and are independent of the larger moment driver. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaFrames
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev Code := Cmd 16 256

abbrev transfer (src dst : Fin 256) : Code := .call (transferProgram src dst 0 1)

end SubexponentialSAT.SqrtLog.PerturbationBetaFrames

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyNativeScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete native coordinate-row scan with arithmetic callbacks discharged. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def nativeRowBudget (N J n W Km Ka : ℕ) : ℕ :=
  15*(N*W)+30*n+43+shiftBudget N J W Km Ka+PerturbationEmitProgram.budget J n W

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyOrigin
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Emit the computed beta at the actual all-zero sparse key. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl

def originKey (n : ℕ) : List Bool :=
  PerturbationEmitProgram.keyBits (List.replicate n false) 0

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyLow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed low-variable incidence preparation from physical coefficient rows.
Beta evaluation, point construction, polynomial Horner, sparse emission, and
cache restoration are all performed by fixed finite commands. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- All temporary words of the complete low-variable worker. -/
def lowScratch : List (Fin 256) :=
  PerturbationBetaProgram.workPorts ++ originScratch ++ targetScratch ++
    coordinateLoadScratch ++ shiftScratch ++ coordinateEmitScratch ++ [218,230,231]

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyOuter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Relocation and the finite total-variable table traversal. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl

attribute [local simp] Fin.coe_ofNat_eq_mod

def literalReady (s : OuterStore) (count acc : List Bool) : OuterStore :=
  Function.update (Function.update s 573 count) 569 acc

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyNativeLiteral
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native source-to-literal composition. The source premise is the execution
of one fixed finite source command; all beta, shift, and emission services are
fully discharged by LowInput.run. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def literalSourceState (s : OuterStore) (j : ℕ) (words : List Bool) : OuterStore :=
  Function.update (Function.update s 555 (Encoding.encodeNat j)) 545 words

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual selected-factor table runs over ambient variable IDs. Each low
payload is specialized immediately before its framed table entry is retained.
The source scratch embedding excludes persistent layout masters. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI BitProgram StructuredCalls SubexpConvolutionControl
open PerturbationAssembly OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

attribute [local simp] Fin.coe_ofNat_eq_mod

/-- Clearing only the private worker preserves the selected factor556 and
all caller masters; staging reconstructs every required arithmetic cache. -/
def entryPorts : List (Fin 896) :=
  ((LeafProgram.Incidence.workerPorts.filter (fun i => i ≠ 556)).map basePort) ++
    [62,680,681,682,683,684,881,882]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The accepted-assignment factor product uses the original finite-ring
indicator and clause programs after the concrete specialized table producer.
Every cache is rebuilt from persistent source words by paid native copies;
neutral factor IDs leave the running multiplicative identity unchanged. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram

open OAI BitProgram StructuredCalls SubexpSetupStorage
open SqrtLog SqrtLog.LeafProgram
noncomputable section

/-- Only transient arithmetic, parser and source-worker storage is cleared.
The current record149, pending records150 and running product151 remain live. -/
def callbackScratch : List (Fin 768) :=
  List.map Factor.indicatorStacks FactorServices.indicatorScratch ++
    [62, 64, 159, 556] ++ FactorDispatch.scratch ++ Expansion.scratch ++ [358]

/-- Reclaim all private callback and relocated source storage before the
first factor. The fixed finite list excludes every live caller master. -/
def entryScratch : List (Fin 896) :=
  [149, 150, 151, 159, 854] ++ callbackScratch.map lowStack ++
    FactorTableProgram.entryPorts

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Relational execution of the fixed specialized factor-record loop. This
adapts the original FactorLoop reader/while proof to the shared 896-stack ABI
and empty-support dictionaries. The explicit callback premise must be proved
for the actual callback before this component can close an algorithm endpoint. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop
attribute [local simp] Fin.coe_ofNat_eq_mod
open OAI BitProgram StructuredCalls SqrtLog SqrtLog.LeafProgram MomentsProgram

def records (ids : List ℕ) : List (List Bool) := ids.map Encoding.encodeNat

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Space for one actual ambient-coordinate table construction. Its unary
traversal has only n iterations, so its polynomial local time bounds every
source prefix. No outer signature or finite-difference iteration count occurs
in this estimate. The concrete literal and staging traces are instantiated by
the factor-table producer, rather than supplied to a final counting endpoint. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace

open SqrtLog

open BitProgram StructuredCalls FactorTableProgram

/-- Exactly the ports that may be changed by the table command: relocated
private worker, exported table, and physical copy temporaries. -/
def writtenPorts : List (Fin 896) :=
  LeafProgram.Incidence.workerPorts.map basePort ++ [62,680,681,682,683,684,881,882]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashTrialStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact finite staging extracted from `SqrtLog.LeafOuterNativeStage` for the
space-aware hash pipeline. Semantic query provenance remains in the original
module, while these declarations live in the stronger development's namespace. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative
open OAI BitProgram StructuredCalls SqrtLog.LeafOuterProgram
open Subexp

def masterRoutes : List Route := [(784,700),(782,707),(783,708),(785,709),(777,701)]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit polynomial work and storage bounds for native shifted rows. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT

def rowWorkPolynomial (N J n d B : ℕ) : ℕ :=
  15*(N*(d*B))+30*n+43+1000*(N+1)*(J+1)*(d*B+1)+
    (N+1)*(100000*(J+1)^3*(d+1)^3*(B+1)^2+
      DensePolynomialProgram.AddService.budget d B J J)+
    150*(J+1)*(J+n+d*B+1)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeParameters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SparseCode

theorem logSize_pos (m : ℕ) : 0 < logSize m := by simp [logSize]

theorem gapDenom_pos (m : ℕ) {B : ℕ} (hB : 0 < B) : 0 < gapDenom m B := by
  have := logSize_pos m
  unfold gapDenom
  positivity

theorem degreeBound_pos (m : ℕ) {B : ℕ} (hB : 0 < B) : 0 < degreeBound m B := by
  have := gapDenom_pos m hB
  have := logSize_pos m
  unfold degreeBound
  positivity

theorem degree_pos {m B : ℕ} (hm : 0 < m) (hB : 0 < B) : 0 < degree m B := by
  exact lt_min hm (degreeBound_pos m hB)

theorem dimensionFor_spec (m : ℕ) {D : ℕ} (hD : 0 < D) :
    m ≤ D * 2 ^ dimensionFor m D := by
  simp only [dimensionFor, dite_eq_left hD]
  exact Nat.find_spec (exists_dimension m hD)

theorem graph_edge_lower {m B : ℕ} (hm : 0 < m) (hB : 0 < B) :
    m ≤ 2 ^ dimension m B * degree m B := by
  simpa [dimension, Nat.mul_comm] using dimensionFor_spec m (degree_pos hm hB)

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SparseCode

def totalRows (m B : ℕ) : ℕ := 2 * 2 ^ dimension m B * localRows m B

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeShorten
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SparseCode

open scoped BigOperators

variable {C E R : Type*} [Fintype C] [Fintype E]
    [DecidableEq C] [DecidableEq E]

/-- Keep selected columns. Its code is a zero-shortening, not a puncture. -/
def shorten (Q : CheckMatrix R E) (e : C ↪ E) : CheckMatrix R C :=
  fun r c => Q r (e c)

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryRankProvenance
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The rank certificate refers to the packing and word table actually
produced by the native packing caller, with its original incidence order. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.ProducedQueryRank
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open PackingCallerProgram

def rationalDenominator (R : ℕ) : ℚˣ :=
  Units.mk0 (LayoutNumerator.denominator R : ℚ) (by
    simp only [LayoutNumerator.denominator]
    positivity)

@[simp] theorem rationalDenominator_val (R : ℕ) :
    (rationalDenominator R : ℚ)=(LayoutNumerator.denominator R : ℚ) := rfl

end SubexponentialSAT.SqrtLog.ProducedQueryRank

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProgramTapeReplay
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact-time replay under replacement of syntactically untouched tapes. -/
namespace SubexponentialSAT.SqrtLog.ProgramTapeReplay
open SubexponentialSAT BitProgram StructuredCalls

variable {r s l : ℕ}

def rebaseState (H : Fin s → Prop) [DecidablePred H]
    (frame : Fin s → List Bool) (a : StructuredProgram.State r s) : StructuredProgram.State r s :=
  ⟨a.regs, rebaseStacks H frame a.stacks⟩

def rebaseCfg (H : Fin s → Prop) [DecidablePred H]
    (frame : Fin s → List Bool) (a : Cfg r s l) : Cfg r s l :=
  ⟨a.pc, a.regs, rebaseStacks H frame a.stacks⟩

@[simp] theorem rebaseStacks_of_mem (H : Fin s → Prop) [DecidablePred H]
    (frame data : Fin s → List Bool) (i : Fin s) (hi : H i) :
    rebaseStacks H frame data i = frame i := ite_eq_left hi

@[simp] theorem rebaseStacks_of_not_mem (H : Fin s → Prop) [DecidablePred H]
    (frame data : Fin s → List Bool) (i : Fin s) (hi : ¬ H i) :
    rebaseStacks H frame data i = data i := ite_eq_right hi

@[simp] theorem rebaseState_regs (H : Fin s → Prop) [DecidablePred H]
    (frame : Fin s → List Bool) (a : StructuredProgram.State r s) :
    (rebaseState H frame a).regs = a.regs := rfl

@[simp] theorem rebaseCfg_withPC (H : Fin s → Prop) [DecidablePred H]
    (frame : Fin s → List Bool) (a : StructuredProgram.State r s) (pc : Option (Fin l)) :
    rebaseCfg H frame (a.withPC pc) = (rebaseState H frame a).withPC pc := rfl

@[simp] theorem rebaseStacks_update (H : Fin s → Prop) [DecidablePred H]
    (frame data : Fin s → List Bool) (i : Fin s) (value : List Bool) (hi : ¬ H i) :
    rebaseStacks H frame (Function.update data i value) =
      Function.update (rebaseStacks H frame data) i value := by
  funext j
  by_cases hj : j = i
  · subst j; simp [rebaseStacks,hi]
  · simp [rebaseStacks,Function.update_of_ne hj]

end SubexponentialSAT.SqrtLog.ProgramTapeReplay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Arbitrary-width physical CRT initialization. The computed ring-zero word
is passed on stack 280; all copying, width construction and unary-to-binary
conversion are charged by actual primitive traces. -/

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram

def initializationBudget (W J nodeBits jetBits : ℕ) : ℕ :=
  14 * W + SubexpFactorCountSetup.countBudget J + J * (7 * W + 14) +
    14 * nodeBits + 7 * jetBits + 37

end SubexponentialSAT.SqrtLog.ReconstructionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-table outer Hermite traversal for arbitrary coefficient width.
Only the arithmetic middle is parameterized; this module charges all input
copying, node/jet transport, indexing, iteration and final cleanup. -/

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram

def controllerBudget (W D Q K : ℕ) : ℕ :=
  initializationBudget W D (Q * W) (Q * (D * W)) +
    Q * (K + transportCost W (D * W) Q + 2) +
    cleanupBudget W (D * W) Q D + 2


end SubexponentialSAT.SqrtLog.ReconstructionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramHorner
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical staging of local CRT correction evaluation. The dense correction
is consumed from 244; its value at the retained point 263 is returned on 264. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner

open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram
open CRTLocalProgram (LowFrame)

def budget (J W Km Ka : ℕ) : ℕ :=
  HornerProgram.budget J W Km Ka + 6 * J * W + 31 * W + 7 * J + 39

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramMiddle
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Composition of the physical arithmetic stages for one Hermite node. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle

open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram
open CRTLocalProgram (LowFrame )

def budget (Q J W Km Ka Kl : ℕ) : ℕ :=
  CofactorOuter.budget Q Km W J + (Km + 26 * W + 26) + Local.budget (J*W) J Kl +
    Horner.budget J W Km Ka + (Km + Ka + 58 * W + 61)

def nodeValue {C : Type*} (mul add : C → C → C) (minusOne zero unit node acc : C)
    (J : ℕ) (remaining processed correction : List C) : C :=
  add acc (mul ((remaining ++ processed).foldl (Cofactor.includeValue mul minusOne J) unit)
    (HornerProgram.fold (HornerProgram.stepValue mul add (mul node minusOne)) correction.reverse zero))

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramIndex
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime, self-delimiting natural-index alphabet. The range control is the
existing unary loop, with one delimiter inserted in each emitted payload. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram.Index
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpIncidencePlanPrimitives

def indexPrefix (js : List ℕ) : List Bool :=
  js.flatMap fun j => true :: Encoding.frame (Encoding.encodeNat j)

end SubexponentialSAT.SqrtLog.RowSelectionProgram.Index

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeSupplied
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The sparse-code assembly accepts any successful physical search output.
It does not require agreement with the semantic search enumeration order.
Physical serializers must emit the local incidence slots, rather than all
columns of these extensional matrices. -/
namespace SubexponentialSAT.SqrtLog.SparseCode

open scoped BigOperators

abbrev SuppliedShifts (m B : ℕ) := Fin (degree m B) → Cayley.Cube (dimension m B)
abbrev SuppliedLocal (m B : ℕ) := CheckMatrix (Fin (localRows m B)) (Fin (degree m B))

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeMaskDecode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The fixed-length support-mask encoding and its executable inverse.
Words shorter than n are padded by false; longer words are truncated.
On length-n words these operations are mutually inverse. -/

namespace SubexponentialSAT.SqrtLog.Squarefree

@[simp] theorem decodeMask_encodeMask {n : ℕ} (s : Finset (Fin n)) :
    decodeMask n (encodeMask s) = s := by
  ext i
  simp [decodeMask, encodeMask]

@[simp] theorem encodeMask_count {n : ℕ} (s : Finset (Fin n)) :
    (encodeMask s).count true = s.card := by
  let selected := (List.finRange n).filter (fun i => decide (i ∈ s))
  have hn : selected.Nodup := (List.nodup_finRange n).filter _
  have hs : selected.toFinset = s := by
    ext i
    simp [selected]
  have hc : ∀ l : List (Fin n),
      (l.map (fun i => decide (i ∈ s))).count true =
        (l.filter (fun i => decide (i ∈ s))).length := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih => by_cases hi : i ∈ s <;> simp [hi, ih]
  calc
    (encodeMask s).count true = selected.length := by
      simpa only [encodeMask, List.ofFn_eq_map, selected] using hc (List.finRange n)
    _ = selected.toFinset.card := (List.toFinset_card_of_nodup hn).symm
    _ = s.card := congrArg Finset.card hs

end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end


