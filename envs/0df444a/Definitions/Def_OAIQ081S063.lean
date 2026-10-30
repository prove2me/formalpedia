-- Prove2me | Definitions.Def_OAIQ081S063
-- name    : OAIQ081S063
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:49:47.541366+00:00
-- url     : https://prove2.me/theorems/2ccb6ea8-a8c7-4b89-a4ae-1506276d74c4
-- title:
--   Definitions bundle OAIQ081S063 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 73 declarations of OpenAI's Lean: 54 definitions and 19 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.weightedScoreValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.hornerInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.loaded`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaFrames.framePorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaFrames.readFrame`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgram.Traversal.ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgram.betaValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgram.polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Reconstruction.HasJets`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.LocalValue.inverse`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.Index.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.Ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.StreamData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.inputLength`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.readScore`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgramSelect.FrameData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgramSelect.framePopped`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgramSelect.frameState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.HasRelativeDistance`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.PortGraph.IsTannerCodeword`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.columnEmbedding`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.rowEquiv`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.suppliedMatrix`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Admissible`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Bounded`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.accumulated`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.encoded`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.environment`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.lookupResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Sparse.indexUniverse`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Sparse.jetCoeff`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Sparse.row`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ZAdmissible`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.evalBool`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.bodyBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.bodyCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.boundaryBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.polynomialBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.spaceBudget` and 14 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram`, `SubexponentialSAT_SqrtLogSpace_AttainedSignatureRescan`, `SubexponentialSAT_SqrtLogSpace_CodeCandidateProgram`, `SubexponentialSAT_SqrtLogSpace_CodeCandidates`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLogSpace_HashGreedyProgram`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputStats`, `SubexponentialSAT_SqrtLog_PackingProgramArithmetic`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyControl`, `SubexponentialSAT_SqrtLog_PerturbationBetaProgramFrames`, `SubexponentialSAT_SqrtLog_PerturbationEmitProgram`, `SubexponentialSAT_SqrtLog_PerturbationProgram`, `SubexponentialSAT_SqrtLog_PerturbationProgramTraversal`, `SubexponentialSAT_SqrtLog_ProgramTapeReplay`, `SubexponentialSAT_SqrtLog_Reconstruction`, `SubexponentialSAT_SqrtLog_ReconstructionProgramLocalValue`, `SubexponentialSAT_SqrtLog_ResidualEmbedding`, `SubexponentialSAT_SqrtLog_RowSelectionProgramArithmetic`, `SubexponentialSAT_SqrtLog_RowSelectionProgramIndex`, `SubexponentialSAT_SqrtLog_RowSelectionProgramParser`, `SubexponentialSAT_SqrtLog_RowSelectionProgramSelectFrame`, `SubexponentialSAT_SqrtLog_SparseCodeBasic`, `SubexponentialSAT_SqrtLog_SparseCodeConstruct`, `SubexponentialSAT_SqrtLog_SparseCodeSupplied`, `SubexponentialSAT_SqrtLog_SquarefreeBasic`, `SubexponentialSAT_SqrtLog_SquarefreeJet`, `SubexponentialSAT_SqrtLog_SquarefreeKeyMapProgram`, `SubexponentialSAT_SqrtLog_SquarefreeProgramLookup`, `SubexponentialSAT_SqrtLog_SquarefreeSparseBounds`, `SubexponentialSAT_SqrtLog_SquarefreeSparseOps`, `SubexponentialSAT_SqrtLog_SquarefreeSparseProduct`, `SubexponentialSAT_SqrtLog_TotalOrderArray`, `SubexponentialSAT_SqrtLog_TotalOrderBasic`, `SubexponentialSAT_SubexpInputFrames`, `SubexponentialSAT_SubexpSetupStorage`, `SubexponentialSAT_Subexp_AssignmentInputProgram`, `SubexponentialSAT_Subexp_AssignmentInputState`, `SubexponentialSAT_Subexp_UniversalRowProgram`, `SubexponentialSAT_TruncatedInverse`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S023`, `OAIQ081S024`, `OAIQ081S025`, `OAIQ081S027`, `OAIQ081S028`, `OAIQ081S029`, `OAIQ081S030`, `OAIQ081S032`, `OAIQ081S033`, `OAIQ081S034`, `OAIQ081S035`, `OAIQ081S036`, `OAIQ081S039`, `OAIQ081S040`, `OAIQ081S041` and `OAIQ081S042` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S079`, `OAIQ081S080` and `OAIQ081S081`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.corrected_denote`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.shiftU_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.row_meaning`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.keyPhase_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.supplied_kernel_bound_of_coverage`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.corrected_denote`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localScan_localFactor`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.serializedRows_kernel_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.writeRow_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWordCallback_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordCallback_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.literalDictionary_hit`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.queryPolynomial_origin`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.insert_hit_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.fetchAdd_miss` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.supplied_kernel_bound_of_coverage`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S023
import Definitions.Def_OAIQ081S024
import Definitions.Def_OAIQ081S025
import Definitions.Def_OAIQ081S027
import Definitions.Def_OAIQ081S028
import Definitions.Def_OAIQ081S029
import Definitions.Def_OAIQ081S030
import Definitions.Def_OAIQ081S032
import Definitions.Def_OAIQ081S033
import Definitions.Def_OAIQ081S034
import Definitions.Def_OAIQ081S035
import Definitions.Def_OAIQ081S036
import Definitions.Def_OAIQ081S039
import Definitions.Def_OAIQ081S040
import Definitions.Def_OAIQ081S041
import Definitions.Def_OAIQ081S042

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

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

def cost (W bits : List Bool) (rows : List (List (List Bool))) : ℕ :=
  7 * (words (rows.map words)).length + 5 + (signatureCost W bits rows + 2)

namespace Rescan

def bodyCost (W predecessor saved : List Bool) (rows : List (List (List Bool))) : ℕ :=
  7 * predecessor.length + 5 + (cost W predecessor rows + 1) +
    (18 * (signatureValue W predecessor rows).length + 9 * saved.length + 26) + 8 +
    (2 * predecessor.length + 3) + (2 * (signatureValue W predecessor rows).length + 3) +
    (CounterPrograms.rippleCost true predecessor + 1)

def bodyBound (W saved : List Bool) (rows : List (List (List Bool))) (h B : ℕ) : ℕ :=
  17 * h + 20 * keyBound W h rows.length B + 9 * saved.length +
    7 * (words (rows.map words)).length + rows.length * (signatureRowBound W h B + 2) + 62

end Rescan

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatureRescan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual bounded-word predecessor rescan and its uniform source-prefix storage. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

namespace Rescan

def boundaryBound (W saved : List Bool) (rows : List (List (List Bool))) (h : ℕ) : ℕ :=
  W.length + (words (rows.map words)).length + saved.length + 3 * h + 1

/-- A uniform polynomial local budget, before the exponential scan counts. -/
def polynomialBudget (W : List Bool) (rows : List (List (List Bool))) (h B : ℕ) : ℕ :=
  14 * (words (rows.map words)).length +
    2 * (rows.length * (signatureRowBound W h B + 2)) +
    38 * keyBound W h rows.length B + 62 * h + 129

def spaceBudget (W : List Bool) (rows : List (List (List Bool))) (h B : ℕ) : ℕ :=
  40 * (W.length + (words (rows.map words)).length + keyBound W h rows.length B + 3 * h + 1) +
    polynomialBudget W rows h B + 16


end Rescan

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
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

@[simp] theorem trunc_idempotent (D : ℕ) (f : A[X]) :
    Truncation.trunc D (Truncation.trunc D f) = Truncation.trunc D f := by
  ext n
  by_cases hn : n < D <;> simp [Truncation.coeff_trunc, hn]

/-- The inverse represented by exactly its first `D` coefficients. -/
def inverse (B : A[X]) (a : A) (D : ℕ) : A[X] :=
  Truncation.trunc D (rawInverse B a D)

/-- Multiply a jet by the inverse, keeping precisely the local order. -/
def correctedJet (B J : A[X]) (a : A) (D : ℕ) : A[X] :=
  Truncation.trunc D (J * inverse B a D)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def correction (θ : ι → A) (D : ℕ) (a : ι → A) (J : ι → A[X]) (i : ι) : A[X] :=
  correctedJet (localFactor θ D i) (J i) (a i) D

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

/-- Physical counter words for a single field vector, never a family of vectors. -/
def fieldWords {p d : ℕ} [Fact p.Prime] (v : Fin d → ZMod p) : List (List Bool) :=
  List.ofFn fun i => scalarBits (v i)

@[simp] theorem fieldWords_shape {p d : ℕ} [Fact p.Prime] (v : Fin d → ZMod p) :
    (fieldWords v).map List.length = List.replicate d (scalarWidth p) := by
  simp [fieldWords, List.map_ofFn, Function.comp_def]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidates
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CodeCandidateProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed-table conversion of one odometer tuple to one arithmetic candidate.
The input contains only the current candidate. The output is reversed scalar
frames, directly suitable for the existing word and matrix callbacks. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidateProgram

open BitProgram CodeCandidates

/-- Construct the zero candidate from a runtime unary dimension word.
The instruction table is independent of the dimension. -/
def zeroTupleProgram : Program 4 2 12 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code := ![.set 0 false 1, .set 1 true 2, .push 1 0 3,
    .pop 0 2 3 4, .branch 3 5 11,
    .push 1 0 6, .push 1 0 7, .push 1 1 8,
    .push 1 0 9, .push 1 1 10, .push 1 1 3, .halt]

def initializeCfg (pc : Option (Fin 12)) (regs : Fin 4 → Bool)
    (input output : List Bool) : Cfg 4 2 12 := ⟨pc, regs, ![input, output]⟩

/-- `ternary = false` is the graph alphabet; `true` is the local-code alphabet.
Register 4 reports an unused digit. No candidate family is ever constructed. -/
def convert (ternary : Bool) : Program 5 2 18 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code := ![.set 4 false 1, .pop 0 0 1 2, .branch 0 3 17,
    .pop 0 0 1 4, .pop 0 2 1 5, .pop 0 0 1 6, .pop 0 3 1 7,
    .pop 0 0 1 8, .set 0 true 9, .push 1 0 10, .push 1 2 11,
    .push 1 0 12, .push 1 3 13, .set 0 false 14, .push 1 0 15,
    (if ternary then .band 2 2 3 16 else .copy 2 3 16),
    .bor 4 4 2 1, .halt]

def cfg (pc : Option (Fin 18)) (regs : Fin 5 → Bool)
    (input output : List Bool) : Cfg 5 2 18 :=
  ⟨pc, regs, ![input, output]⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidateProgram
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

namespace Filter

def ports : RecordPrograms.Ports 16 14 where
  tag := 13
  present := 14
  found := 15
  source := 11
  payload := 13
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide


end Filter

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

section Words

variable {C R : Type*} [Fintype C]

def HasRelativeDistance (Q : CheckMatrix R C) (δ : ℝ) : Prop :=
  ∀ w, IsCodeword Q w → w ≠ 0 → δ * Fintype.card C ≤ (weight w : ℝ)

end Words

namespace PortGraph

variable {V P : Type*} [Fintype V] [Fintype P] [DecidableEq V]

/-- Semantic Tanner constraints before turning the local checks into one
explicit sparse matrix. -/
def IsTannerCodeword {R : Type*} (G : PortGraph V P)
    (Q : CheckMatrix R P) (w : V × P → F3) : Prop :=
  (∀ v, IsCodeword Q (leftWord w v)) ∧
  (∀ v, IsCodeword Q (G.rightWord w v))

end PortGraph

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual fixed binary comparison/update used by the streaming selector.
Its queue port is a bounded iterator frame, not a list of candidate records. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open scoped BigOperators


/-- Serialization uses the existing measured bit escaping routine. -/
def appendPorts : RecordPrograms.Ports 8 10 where
  tag := 0
  present := 1
  found := 7
  source := 2
  payload := 9
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputStats
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The address stream and the native statistics use the same mask scan. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Stats
open SubexponentialSAT.Subexp
open LeafStatisticsProgram

theorem next_eq (scopes : List (List ℕ)) (v z : ℕ) :
    Step.next scopes v z = z + if degree scopes v = 0 then 1 else 0 := by
  change Step.next scopes v z = z + if (Scan.indices scopes v).length = 0 then 1 else 0
  by_cases h : Scan.indices scopes v = [] <;>
    simp [Step.next,List.length_eq_zero_iff,h]

theorem counter_agrees (scopes : List (List ℕ)) (mask : List Bool) :
    ∀ v z (t : Totals), Loop.finalCounter scopes v z mask + t.uncovered =
      z + (variableTotals scopes v mask t).uncovered := by
  induction mask with
  | nil => intros; simp [Loop.finalCounter,variableTotals]
  | cons b bs ih =>
      intro v z t
      cases b
      · have h := ih (v+1) (Step.next scopes v z) (t.add (degree scopes v))
        simp only [Totals.add,next_eq] at h
        simp only [Loop.finalCounter,variableTotals,Bool.false_eq_true,ite_false]
        simp only [Totals.add,next_eq] at *
        omega
      · simpa [Loop.finalCounter,variableTotals] using ih (v+1) z t

theorem native_factor_count (scopes : List (List ℕ)) (mask : List Bool) :
    Semantics.factorCount scopes mask = scopes.length +
      (variableTotals scopes 0 mask zero).uncovered := by
  simpa [Semantics.factorCount,zero] using counter_agrees scopes mask 0 scopes.length zero
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Stats

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed binary machine combines the two collision counts. Its instruction
count and every output length are charged in terms of actual input bit lengths. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls

def weightedScoreValue (d : ArithmeticData) : ℕ :=
  SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 0) * SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 1) +
    SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 2) * SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 3)

end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationProgramTraversal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native bounded traversal with distinct input cells and output accumulator.
This is used to construct the padded polynomial-cell stream before Horner. -/
namespace SubexponentialSAT.SqrtLog.PerturbationProgram.Traversal
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl

variable {C : Type*}

def ready (base : Store) (encode : C → List Bool)
    (cs : List C) (acc count : List Bool) : Store :=
  Function.update (Function.update (Function.update base 246
    (HornerProgram.backward encode cs)) 240 acc) 248 count

end SubexponentialSAT.SqrtLog.PerturbationProgram.Traversal

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native staging for the complete per-coordinate perturbation worker.
All dimensions and values are runtime tapes. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl

def loaded (s : Store) : Store :=
  Function.update (Function.update (Function.update (Function.update s 219 [])
    246 (s 219)) 248 (s 210)) 250 (s 211)

def hornerInput (s : Store) : Store :=
  Function.update (Function.update (Function.update (Function.update s
    240 (s 192)) 246 (s 240)) 248 (s 210)) 250 (s 192)

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

def framePorts (src dst : Fin 256) (hsd : src ≠ dst) : RecordPrograms.Ports 16 256 where
  tag := 0
  present := 1
  found := 2
  source := src
  payload := dst
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := hsd

abbrev readFrame (src dst : Fin 256) (hsd : src ≠ dst) : Code :=
  RecordPrograms.reader (framePorts src dst hsd)

end SubexponentialSAT.SqrtLog.PerturbationBetaFrames

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Sparse squarefree polynomials. The index monoid multiplies by support union,
so the coefficient algebra imposes X_v^2 = X_v without enumerating all supports. -/

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

variable {V R : Type*}

noncomputable section

variable [DecidableEq V] [CommSemiring R]

omit [DecidableEq V] in
theorem boolValue_idempotent (x : V → Bool) (v : V) :
    boolValue (R := R) x v * boolValue x v = boolValue x v := by
  cases h : x v <;> simp [boolValue, h]

def evalBool (x : V → Bool) : Poly V R →+* R := evalHom (boolValue x) (boolValue_idempotent x)

/-- A support-cardinality bound, with no finiteness assumption on the ambient variables. -/
def Bounded (d : ℕ) (f : Poly V R) : Prop :=
  ∀ s ∈ f.coeff.support, s.vars.card ≤ d

end
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeJet
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! U is the outer polynomial variable, Z the inner one. Support cardinality
is charged only to Z degree; no formal X support is charged to U. -/

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

noncomputable section

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

def ZAdmissible (f : ZJet V R) : Prop := ∀ j, Bounded j (f.coeff j)
def Admissible (f : Jet V R) : Prop := ∀ u, ZAdmissible (f.coeff u)

end
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSparseProduct
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

namespace Sparse

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

def row (t J : ℕ) (a : Index V × R) : Data (Index V) R → Data (Index V) R
  | [] => []
  | b :: l =>
      if (a.1.join b.1).Kept t J then (a.1.join b.1, a.2*b.2) :: row t J a l
      else row t J a l

end Sparse
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSparseOps
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree

namespace Sparse

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

noncomputable def jetCoeff (a : Index V) (f : Jet V R) : R :=
  coeff a.vars ((f.coeff a.u).coeff a.z)

end Sparse

end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSparseBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

namespace Sparse

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

def indexUniverse (vars : Finset V) (t J : ℕ) : Finset (Index V) :=
  (((Finset.range t) ×ˢ (Finset.range J)) ×ˢ supportUniverse vars J).image
    (fun a => ⟨a.1.1, a.1.2, a.2⟩)

end Sparse
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit coefficient preparation for incidence perturbations.
The coefficient arrays are ordered from degree zero upwards. Every shift and
node evaluation is the existing finite represented-ring loop, not an oracle.
Counters here charge coefficient callbacks and list visits; primitive execution
is a separate interface and is not asserted by these counter theorems. -/
namespace SubexponentialSAT.SqrtLog.PerturbationProgram

open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpDensePolynomial
open scoped BigOperators

variable {C R : Type*} [CommRing R]

noncomputable def polynomial (ops : RepresentedRing C R) (p : List C) : Polynomial R :=
  PolynomialAlgorithm.denote (decodeList ops p)

noncomputable def betaValue (ops : RepresentedRing C R) (theta : C)
    (rows : List (List C × Bool)) : R :=
  (rows.map fun a => if a.2 then (polynomial ops a.1).eval (ops.decode theta) else 0).sum

end SubexponentialSAT.SqrtLog.PerturbationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationEmitProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native emission of the positive part of a shifted coefficient array.
The dimensions and the singleton support mask are runtime data. The constant
cell is consumed without emission; all later cells are framed, including zero
coefficients. No normalization or arithmetic oracle is used. -/


namespace SubexponentialSAT.SqrtLog.PerturbationEmitProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl

def ready (base : Store) (j : ℕ) (cs : List (List Bool))
    (acc count : List Bool) : Store :=
  Function.update (Function.update (Function.update (Function.update base
    240 (array cs)) 217 acc) 221 (List.replicate j true)) 225 count

end SubexponentialSAT.SqrtLog.PerturbationEmitProgram


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

theorem execInstr_rebase (H : Fin s → Prop) [DecidablePred H]
    (frame : Fin s → List Bool) (i : Instr r s l) (a : Cfg r s l)
    (hi : AvoidsInstr H i) :
    execInstr i (rebaseCfg H frame a) = rebaseCfg H frame (execInstr i a) := by
  cases i <;> simp only [AvoidsInstr] at hi <;>
    (simp [execInstr,rebaseCfg,hi,rebaseStacks_update] <;> rfl)

theorem step_rebase (H : Fin s → Prop) [DecidablePred H]
    (frame : Fin s → List Bool) (p : Program r s l) (hp : AvoidsProgram H p)
    (a : Cfg r s l) :
    step p (rebaseCfg H frame a) = (step p a).map (rebaseCfg H frame) := by
  cases hpc : a.pc with
  | none => simp [step,rebaseCfg,hpc]
  | some q =>
    simp only [step,rebaseCfg,hpc,Option.map_some]
    exact congrArg some (execInstr_rebase H frame (p.code q) a (hp q))

theorem trace_rebase (H : Fin s → Prop) [DecidablePred H]
    {p : Program r s l} (hp : AvoidsProgram H p) {n : ℕ} {a b : Cfg r s l}
    (h : Trace p n a b) (frame : Fin s → List Bool) :
    Trace p n (rebaseCfg H frame a) (rebaseCfg H frame b) := by
  induction h with
  | refl a => exact .refl _
  | @cons n a b c hab hbc ih =>
    exact .cons (by rw [step_rebase H frame p hp,hab]; rfl) ih

theorem atom_eval_rebase (H : Fin s → Prop) [DecidablePred H]
    (frame : Fin s → List Bool) (a : StructuredProgram.Atom r s)
    (ha : AvoidsAtom H a) (d : StructuredProgram.State r s) :
    a.eval (rebaseState H frame d) = rebaseState H frame (a.eval d) :=
  congrArg StructuredProgram.State.ofCfg
    (execInstr_rebase H frame (a.instr (0 : Fin 1)) (d.withPC none)
      (atom_instr_avoids H a ha _))

theorem base_eval_rebase (H : Fin s → Prop) [DecidablePred H]
    {c : StructuredProgram.Cmd r s} (hc : AvoidsBase H c)
    {n : ℕ} {a b : StructuredProgram.State r s} (h : StructuredProgram.Eval c n a b)
    (frame : Fin s → List Bool) :
    StructuredProgram.Eval c n (rebaseState H frame a) (rebaseState H frame b) := by
  induction h with
  | skip d => exact .skip _
  | atom op d =>
    rw [← atom_eval_rebase H frame op hc d]
    exact .atom _ _
  | seq h₁ h₂ ih₁ ih₂ => exact .seq (ih₁ hc.1) (ih₂ hc.2)
  | ite_true ht he ih => exact .ite_true ht (ih hc.1)
  | ite_false ht he ih => exact .ite_false ht (ih hc.2)
  | while_false ht => exact .while_false ht
  | while_true ht hb hw ihb ihw => exact .while_true ht (ihb hc) (ihw hc)

end SubexponentialSAT.SqrtLog.ProgramTapeReplay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_Reconstruction
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit reconstruction for independently chosen node and jet counts

This interface reuses the audited dense-list Hermite program. Its inverse
table is computed by finite powers and geometric sums. No interpolation
choice, scalar-inverse oracle, or field assumption on the coefficient ring
occurs in `run`. The represented arithmetic callbacks carry their own costs.
-/

namespace SubexponentialSAT.SqrtLog.Reconstruction

noncomputable section

open Polynomial

variable {C A : Type*} [CommRing A]

/-- The node evaluator can supply either this identity or coefficient identities. -/
def HasJets (ops : SubexpSymbolicCost.RepresentedRing C A)
    {Q : ℕ} (nodes : Fin Q → C) (order : ℕ)
    (jets : Fin Q → List C) (target : Polynomial A) : Prop :=
  ∀ i, Truncation.trunc order
    (PolynomialAlgorithm.denote ((jets i).map ops.decode)) =
      JetCRT.jet (ops.decode (nodes i)) order target

end
end SubexponentialSAT.SqrtLog.Reconstruction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramLocalValue
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical local factor and correction have the canonical Hermite
meaning independently of the encoded representative of their head word. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.LocalValue

open SubexponentialSAT Polynomial
open SubexpSymbolicCost DensePolynomialProgram
open CRTLocalProgram

variable {B d J Q : ℕ} {R : Type*} [CommRing R]

noncomputable def inverse (theta : Fin Q → R) (q t J : ℕ) (i : Fin Q) : R :=
  (SubexpResidueInverse.inverseWithCost q t
    ((Truncation.trunc J (TruncatedInverse.localFactor theta J i)).coeff 0)).1

end SubexponentialSAT.SqrtLog.ReconstructionProgram.LocalValue

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ResidualEmbedding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Injective padding of residual squarefree variables into their original
ambient coordinate universe. This is a semantic map, not runtime renumbering. -/
namespace SubexponentialSAT.SqrtLog.ResidualEmbedding

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open scoped BigOperators
noncomputable section

variable {V W R : Type*} [DecidableEq V] [DecidableEq W] [CommSemiring R]

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem weight_map (e : V ↪ W) (x : W → R) (s : Finset V) :
    weight x (s.map e) = weight (fun v => x (e v)) s := by
  simp [weight]

end
end SubexponentialSAT.SqrtLog.ResidualEmbedding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact signed arithmetic for minor enumeration. Integers are represented as
pairs of natural binary words. No modular arithmetic, integer oracle, or
parameter-dependent instruction table is used. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.BinaryArithmetic

def inputLength (d : Data) : ℕ :=
  (d.stacks 0).length + (d.stacks 1).length +
  (d.stacks 2).length + (d.stacks 3).length

def Ready (d : Data) : Prop := ∀ j : Fin 15, 4 ≤ j.val → d.stacks j = []

def readScore (ports : Fin 12 → Fin 15) (d : Data) : PackingProgram.ArithmeticData :=
  ⟨d.regs, fun j => d.stacks (ports j)⟩

end SubexponentialSAT.SqrtLog.RowSelectionProgram

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

abbrev Data := StructuredProgram.State 10 10

end SubexponentialSAT.SqrtLog.RowSelectionProgram.Index

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramParser
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit framed input parsing for streams of signed binary word pairs. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev StreamData := State 8 16

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramSelectFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed framing primitive for the scored-record writer. It consumes the
input bits and prepends the frame of their reversal to the output stack. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgramSelect

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev FrameData := State 3 2

abbrev frameState (v p : Bool) (input output : List Bool) : FrameData :=
  ⟨![v,p,true], ![input,output]⟩

abbrev framePopped : List Bool → List Bool → FrameData
  | [], out => frameState false false [] out
  | b::bs, out => frameState b true bs out

end SubexponentialSAT.SqrtLog.RowSelectionProgramSelect

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeConstruct
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit sparse parity-check constructor

Every choice below is executable: two finite searches, arithmetic index
equivalences, and restriction to the first input columns. The hypotheses of
the local-code and Walsh existence lemmas are discharged by the parameter
bounds. No code or expander is supplied as an assumption to the final rows.
-/

namespace SubexponentialSAT.SqrtLog.SparseCode

open scoped BigOperators

def rowEquiv (m B : ℕ) : Fin (totalRows m B) ≃
    (Cayley.Cube (dimension m B) × Fin (localRows m B)) ⊕
    (Cayley.Cube (dimension m B) × Fin (localRows m B)) :=
  (finCongr (by unfold totalRows; ring)).trans
    (finSumFinEquiv.symm.trans
      (Equiv.sumCongr (edgeEquiv (dimension m B) (localRows m B))
        (edgeEquiv (dimension m B) (localRows m B))))

def columnEmbedding (m B : ℕ) (hm : 0 < m) (hB : 0 < B) :
    Fin m ↪ Cayley.Cube (dimension m B) × Fin (degree m B) :=
  (Fin.castLEEmb (graph_edge_lower hm hB)).trans
    (edgeEquiv (dimension m B) (degree m B)).toEmbedding

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeSupplied
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

def suppliedMatrix (m B : ℕ) (hm : 0 < m) (hB : 0 < B)
    (s : SuppliedShifts m B) (Q : SuppliedLocal m B) :
    CheckMatrix (Fin (totalRows m B)) (Fin m) :=
  fun r c => (Cayley.graph s).matrix Q (rowEquiv m B r) (columnEmbedding m B hm hB c)

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramLookup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed primitive dictionary lookup. Dictionary normalization guarantees
unique keys. All key and coefficient bits are scanned by the existing finite
record program; key width, coefficient width and dictionary length are runtime
data and do not affect the instruction table. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpRecordScan

variable {K C : Type*} [DecidableEq K]

abbrev lookupResult := SubexponentialSAT.Subexp.SelectorProgram.framedResult

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeKeyMapProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

def environment {n : ℕ} (a : Index (Fin n)) (t J : ℕ) : Environment :=
  ⟨encodeIndex a,List.replicate t true,List.replicate J true⟩

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def encoded {n : ℕ} (entries : List (Entry n)) : List Program.ByteRecord :=
  entries.map (fun b => (encodeIndex b.1,b.2))

abbrev accumulated {n : ℕ} (a : Index (Fin n)) (t J : ℕ) :
    List (Entry n) → List Bool → List Bool
  | [], output => output
  | (b,c) :: rest, output => accumulated a t J rest
      (if (a.join b).Kept t J then
        Encoding.frame (encodeIndex (a.join b)) ++ Encoding.frame c ++ output else output)

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

/-! Public native sparse-key mapper. The instruction table is independent of
the keys, clipping limits, coefficient width, and dictionary length. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_TotalOrderBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Shared total-order truncation of nilpotent expansions

The outer variable is a formal marker U. `output` evaluates the canonical
representative after truncation at U = 1. This is an additive operation on
polynomials, not a homomorphism out of the quotient by U^t.
-/
namespace SubexponentialSAT.SqrtLog.TotalOrder

noncomputable section

open scoped BigOperators
open SubexponentialSAT.Truncation SubexponentialSAT.NilpotentDefect

variable {R S α : Type*} [CommSemiring R] [CommSemiring S]

@[simp] theorem map_trunc (f : R →+* S) (t : ℕ) (P : Polynomial R) :
    (trunc t P).map f = trunc t (P.map f) := by
  ext j
  by_cases hj : j < t <;> simp [hj]

end

end SubexponentialSAT.SqrtLog.TotalOrder

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_TotalOrderArray
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit fixed-length arrays and truncated convolution for the shared marker. -/
namespace SubexponentialSAT.SqrtLog.TotalOrder

open scoped BigOperators
open SubexponentialSAT.Truncation

variable {R : Type*} [CommSemiring R]

noncomputable section

@[simp] theorem asPolynomial_toArray (t : ℕ) (P : Polynomial R) :
    asPolynomial (toArray t P) = trunc t P := by
  ext j
  by_cases hj : j < t <;> simp [arrayCoeff, toArray, hj]

@[simp] theorem trunc_asPolynomial {t : ℕ} (a : CoeffArray R t) :
    trunc t (asPolynomial a) = asPolynomial a := by
  ext j
  by_cases hj : j < t <;> simp [arrayCoeff, hj]

end
end SubexponentialSAT.SqrtLog.TotalOrder

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpInputFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual frame and tag readers for the row/input-pair stream. -/

namespace SubexponentialSAT.SubexpInputFrames

open BitProgram StructuredCalls

theorem readTag_execute {S : ℕ} (source : Fin S) (d : State 8 S)
    (bit : Bool) (tail : List Bool) (hsource : d.stacks source = bit :: tail) :
    ∃ e : State 8 S, Eval (readTag source) 1 d e ∧
      e.stacks = Function.update d.stacks source tail ∧ e.regs 7 = bit := by
  let e := (StructuredProgram.Atom.pop source 7 6).eval d
  refine ⟨e, .base (.atom _ _), ?_, ?_⟩
  · simp [e, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, hsource]
  · simp [e, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, hsource, readRegs]

end SubexponentialSAT.SubexpInputFrames

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

def project {r s S : ℕ} (register : Fin r → Fin 16) (stack : Fin s → Fin S)
    (a : Data S) : State r s := ⟨a.regs ∘ register, a.stacks ∘ stack⟩

theorem embed_project {r s S : ℕ} (register : Fin r → Fin 16) (stack : Fin s → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack) (a : Data S) :
    embedState register stack a (project register stack a) = a := by
  apply embedState_eq_of_ports register stack a a _ hr hs
  · intro i; rfl
  · intro i hi; rfl
  · intro i; rfl
  · intro i hi; rfl

/-- This rule consumes an actual subroutine trace. It does not postulate a
semantic-function instruction or an unproved runtime. -/
theorem invoke_eval {r s l S : ℕ} (p : Program r s l)
    (register : Fin r → Fin 16) (stack : Fin s → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (a : Data S) (out : State r s) {t : ℕ}
    (ht : Trace p t ((project register stack a).withPC (some p.entry)) (out.withPC none)) :
    Eval (invoke p register stack) t a (embedState register stack a out) := by
  have h := eval_call_lifted p register stack a hr hs ht
  simpa only [invoke, embed_project register stack hr hs a] using h

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentInputState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical input boundary for assignment-alphabet construction. -/

namespace SubexponentialSAT.Subexp.AssignmentInputProgram

open BitProgram StructuredCalls

def inputState (regs : Fin 16 → Bool) (r Q delta D E : ℕ) (pairs : List Bool) : Data :=
  ⟨regs, fun j => if j = 1 then unary r else if j = 2 then unary Q
    else if j = 3 then unary delta else if j = 4 then unary D
    else if j = 5 then unary E else if j = 45 then pairs else []⟩

end SubexponentialSAT.Subexp.AssignmentInputProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentInputProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical input construction for sequential type assignment

All parameters are unary stack data. The fixed program constructs the one-hot
word alphabet, reads its actual first word, derives its packed view, and builds
the exact seed range and dimensions expected by `AssignmentInitProgram`.
-/

namespace SubexponentialSAT.Subexp.AssignmentInputProgram

open BitProgram StructuredCalls SubexpSetupStorage AssignmentInputCall

theorem copies_unary (n m : ℕ) : BlockCopyProgram.copies n (unary m) = unary (n * m) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [BlockCopyProgram.copies_succ, ih]
      simp [unary, Nat.add_mul, Nat.add_comm]

end SubexponentialSAT.Subexp.AssignmentInputProgram

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
open SubexpKernelControl (Word pushWord operator popTag emitOperator countOne drain )

def rowExpression {R : Type*} [Zero R] [One R] (x : R) (r : Row R) : Algorithm.Expr R :=
  .add (.lit r.delta) (Algorithm.Expr.sum (r.terms.map (termExpression x)))

end SubexponentialSAT.Subexp.UniversalRowProgram

end OAI.Algorithms
end


