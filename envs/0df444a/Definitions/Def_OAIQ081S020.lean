-- Prove2me | Definitions.Def_OAIQ081S020
-- name    : OAIQ081S020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:24:58.450758+00:00
-- url     : https://prove2.me/theorems/422549d7-ecc5-4cd0-bf20-bf46f4598d42
-- title:
--   Definitions bundle OAIQ081S020 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 229 declarations of OpenAI's Lean: 172 definitions, 5 inductive types or structures, 7 instances and 45 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.constantScratch`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.coordinateLoadScratch`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.entryScratch`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.flagStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.innerPort`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.originScratch`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.rowsResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.shiftScratch`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.tableMap`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.targetScratch`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.Store`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.WorkEmpty`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.finishBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.finished`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.initBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.initialized`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.staged`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.workPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.array`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.emitRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.keyMap`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.loopBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.stepBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationMaskProgram.bits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgram.Padding.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.binaryBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRank.rationalNode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplay.rebaseStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Reconstruction.markedDegreeBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor.includeBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor.includeValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Entry.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Entry.prepared`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Local.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.costConstant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar.safe`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Store`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.initializationChanged` and 137 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_ABI`, `SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram`, `SubexponentialSAT_SqrtLogSpace_AttainedSignatures`, `SubexponentialSAT_SqrtLogSpace_BooleanDifferences`, `SubexponentialSAT_SqrtLogSpace_CodeCandidateProgram`, `SubexponentialSAT_SqrtLogSpace_CodeCandidates`, `SubexponentialSAT_SqrtLogSpace_CodeChecks`, `SubexponentialSAT_SqrtLogSpace_CountDFS`, `SubexponentialSAT_SqrtLogSpace_DifferencePairs`, `SubexponentialSAT_SqrtLogSpace_DifferencePairsProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_BinaryClogProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_BinaryCompareProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_CanonicalWordProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_CountModel`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_NegatedCoreProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_ParameterBank`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseAccumulatorProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseCountProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseDFSBoundarySpace`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseDFSProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityPrimitives`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointSparsifyProgram`, `SubexponentialSAT_SqrtLogSpace_EncodingBounds`, `SubexponentialSAT_SqrtLogSpace_HashMassStaged`, `SubexponentialSAT_SqrtLogSpace_SparseCodeProgram`, `SubexponentialSAT_SqrtLogSpace_TruncatedRing`, `SubexponentialSAT_SqrtLogSpace_VisitedTape`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyBranch`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyConstants`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyCoordinate`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyEntry`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyOrigin`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyPreparation`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyScan`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyShift`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyTarget`, `SubexponentialSAT_SqrtLog_PerturbationBetaProgram`, `SubexponentialSAT_SqrtLog_PerturbationBetaProgramFraming`, `SubexponentialSAT_SqrtLog_PerturbationBetaProgramRun`, `SubexponentialSAT_SqrtLog_PerturbationEmitProgram`, `SubexponentialSAT_SqrtLog_PerturbationMaskProgram`, `SubexponentialSAT_SqrtLog_PerturbationProgramPaddingRun`, `SubexponentialSAT_SqrtLog_PolynomialExecutorProgramCost`, `SubexponentialSAT_SqrtLog_ProducedQueryRankProvenance`, `SubexponentialSAT_SqrtLog_ProgramTapeReplay`, `SubexponentialSAT_SqrtLog_ReconstructionDegree`, `SubexponentialSAT_SqrtLog_ReconstructionProgramCofactor`, `SubexponentialSAT_SqrtLog_ReconstructionProgramCofactorOuter`, `SubexponentialSAT_SqrtLog_ReconstructionProgramEntry`, `SubexponentialSAT_SqrtLog_ReconstructionProgramLoaded`, `SubexponentialSAT_SqrtLog_ReconstructionProgramLocal`, `SubexponentialSAT_SqrtLog_ReconstructionProgramPolynomialCost`, `SubexponentialSAT_SqrtLog_ReconstructionProgramScalar`, `SubexponentialSAT_SqrtLog_RowSelectionProgramIndex`, `SubexponentialSAT_SqrtLog_RowSelectionProgramSelectFrame`, `SubexponentialSAT_SqrtLog_RowSelectionProgramStream`, `SubexponentialSAT_SqrtLog_SpectralBinomial`, `SubexponentialSAT_SqrtLog_SquarefreeBasic`, `SubexponentialSAT_SqrtLog_SquarefreeKeyMapProgram`, `SubexponentialSAT_SqrtLog_SquarefreeMaskDecode`, `SubexponentialSAT_SqrtLog_SquarefreeProgramFrame`, `SubexponentialSAT_SqrtLog_SquarefreeScaleProgram`, `SubexponentialSAT_SqrtLog_TotalOrderArray`, `SubexponentialSAT_SqrtLog_TotalOrderPathDegree`, `SubexponentialSAT_SqrtLog_WalshExistenceCore`, `SubexponentialSAT_SubexpCRTOuterFinish`, `SubexponentialSAT_SubexpCRTOuterSweep`, `SubexponentialSAT_SubexpDensePaddingSpec`, `SubexponentialSAT_SubexpNegatedQueryProgram`, `SubexponentialSAT_SubexpPolynomialCost`, `SubexponentialSAT_SubexpResidueInverse`, `SubexponentialSAT_SubexpTautologyProgram`, `SubexponentialSAT_TruncatedInverse`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S042` and `OAIQ081S043`; the statement `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.branch_target_degree`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram_sourceRows_present_model`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.branch_target_degree` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Spectral.centered_normalizedTail_le_of_sq`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_ABI
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed disjoint register and stack banks for the counting machine. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ABI

def leafRegisters : Fin 40 ↪ Fin 80 :=
  (Fin.natAddEmb 32).trans (Fin.castAddEmb 8)

def leafStacks : Fin 896 ↪ Fin 1220 :=
  (Fin.natAddEmb 320).trans (Fin.castAddEmb 4)

def positivityRegisters : Fin 3 ↪ Fin 80 :=
  (Fin.natAddEmb 72).trans (Fin.castAddEmb 5)

def countStack : Fin 1220 := 256

def answerStack : Fin 1220 := 1216

def positivityScratch : Fin 1220 := 1217

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ABI
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# First occurrences of attained keys

The subtype below is a specification of emissions, not a stored family.
The executable scan checks a candidate against its predecessors one at a time.
The key may be an entire integer row-signature; no coordinate projection occurs.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures

variable {N : ℕ} {κ : Type*} (key : Fin N → κ)

abbrev Representative := {i : Fin N // ∀ j, j < i → key j ≠ key i}

def toAttained (i : Representative key) : Set.range key := ⟨key i, i, rfl⟩

theorem toAttained_injective : Function.Injective (toAttained key) := by
  intro i j h
  have he : key i.val = key j.val := congrArg Subtype.val h
  apply Subtype.ext
  rcases lt_trichotomy i.val j.val with hij | hij | hij
  · exact (j.property i.val hij he).elim
  · exact hij
  · exact (i.property j.val hij he.symm).elim

theorem toAttained_surjective : Function.Surjective (toAttained key) := by
  classical
  intro y
  obtain ⟨j, hj⟩ := y.property
  have hex : ∃ i, key i = y.val := ⟨j, hj⟩
  let i := Fin.find (fun i => key i = y.val) hex
  have hkey := Fin.find_spec hex
  refine ⟨⟨i, ?_⟩, Subtype.ext hkey⟩
  intro j hj hji
  exact Fin.find_min hex hj (hji.trans hkey)

theorem toAttained_bijective : Function.Bijective (toAttained key) :=
  ⟨toAttained_injective key, toAttained_surjective key⟩

noncomputable def representativeEquiv : Representative key ≃ Set.range key :=
  Equiv.ofBijective (toAttained key) (toAttained_bijective key)

@[simp] theorem representativeEquiv_value (i : Representative key) :
    (representativeEquiv key i).val = key i := by
  rw [representativeEquiv, Equiv.ofBijective_apply]
  rfl

/-- The mutable duplicate latch has this proof-level recurrence. The actual
program implements it with a bounded word and one Boolean register. -/
def duplicateScan [DecidableEq κ] (key : ℕ → κ) (candidate : ℕ) : ℕ → Bool
  | 0 => false
  | bound + 1 => duplicateScan key candidate bound || decide (key bound = key candidate)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_VisitedTape
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

theorem trace_prefix_exists {α : Type*} {step : α → Option α}
    {a b : α} {steps prefixSteps : ℕ}
    (tr : Computation.Trace step steps a b) (hle : prefixSteps ≤ steps) :
    ∃ intermediate, Computation.Trace step prefixSteps a intermediate := by
  induction tr generalizing prefixSteps with
  | refl a =>
      have hp : prefixSteps = 0 := by omega
      subst prefixSteps
      exact ⟨a, .refl a⟩
  | @cons steps a next final hs ht ih =>
      cases prefixSteps with
      | zero => exact ⟨a, .refl a⟩
      | succ prefixSteps =>
          obtain ⟨intermediate, hp⟩ := ih (prefixSteps := prefixSteps) (by omega)
          exact ⟨intermediate, .cons hs hp⟩


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram
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

def signaturePorts : Fin 15 → Fin 16 := Fin.castAdd 1

namespace Rescan

def signatureRegisters : Fin 8 → Fin 16 := Fin.castAdd 8
def signatureStacks : Fin 16 → Fin 24 := Fin.castAdd 8

def equalityRegisters : Fin 5 → Fin 16 := Fin.castAdd 11
def equalityStacks : Fin 6 → Fin 24 := ![14, 1, 17, 3, 4, 5]

end Rescan

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_BooleanDifferences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Boolean finite differences (ETH, Lemma `boolean-differences`).
The finite sets in this module specify sums; they are not operational enumerators. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.BooleanDifferences

open scoped BigOperators

/-- The original support counting envelope. -/
def supportFamily (n J : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun E => E.card < J)

/-- Valid correction pairs form a subset of the square of the support envelope. -/
def pairFamily (n J : ℕ) : Finset (Finset (Fin n) × Finset (Fin n)) :=
  (supportFamily n J ×ˢ supportFamily n J).filter (fun p => p.2 ⊆ p.1)

@[simp] theorem mem_supportFamily {n J : ℕ} {E : Finset (Fin n)} :
    E ∈ supportFamily n J ↔ E.card < J := by
  simp [supportFamily]

@[simp] theorem mem_pairFamily {n J : ℕ} {E U : Finset (Fin n)} :
    (E, U) ∈ pairFamily n J ↔ E.card < J ∧ U ⊆ E := by
  simp only [pairFamily, Finset.mem_filter, Finset.mem_product, mem_supportFamily]
  exact ⟨fun h => ⟨h.1.1, h.2⟩,
    fun h => ⟨⟨h.1, (Finset.card_le_card h.2).trans_lt h.1⟩, h.2⟩⟩

variable {V R : Type*} [DecidableEq V] [CommRing R]

/-- Substitution of the Boolean characteristic vector of a set. -/
def evalAt (U : Finset V) : MvPolynomial V R →+* R :=
  MvPolynomial.eval (fun v => if v ∈ U then 1 else 0)

/-- The coefficient of the Boolean multilinearization indexed by `E`. -/
noncomputable def difference (E : Finset V) (p : MvPolynomial V R) : R :=
  ∑ U ∈ E.powerset, (-1 : R) ^ (E.card - U.card) * evalAt U p

/-- Boolean assignments retain all ambient variables, including unused ones. -/
def trueSet [Fintype V] (x : V → Bool) : Finset V :=
  Finset.univ.filter (fun i => x i = true)

omit [DecidableEq V] in
@[simp] theorem subset_trueSet [Fintype V] (E : Finset V) (x : V → Bool) :
    E ⊆ trueSet x ↔ ∀ i ∈ E, x i = true := by
  simp [Finset.subset_iff, trueSet]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.BooleanDifferences
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_TruncatedInverse
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

/-- The untruncated finite geometric inverse expression. -/
def rawInverse (B : A[X]) (a : A) (D : ℕ) : A[X] :=
  C a * ∑ j ∈ Finset.range D, (1 - C a * B) ^ j

end SubexponentialSAT.TruncatedInverse

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPolynomialCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Uniform polynomial and CRT costs with growing parameters

These bounds apply to the existing executable coefficient-list algorithms.
Their numerical constants and exponents are absolute: in particular, `Q`, `D`,
the path degree, the extension degree, and coefficient width are not fixed.
Scalar-operation counters and serialized bit lengths are distinguished from
the separate task of proving a Turing-machine simulation.
-/

namespace SubexponentialSAT.SubexpPolynomialCost

open Polynomial
open scoped BigOperators

section InversePreprocessing

variable {A : Type*} [CommRing A]

/-- A finite scalar power loop, with one counted multiplication per step. -/
def scalarPowerWithCost (a : A) : ℕ → A × ℕ
  | 0 => (1, 0)
  | n + 1 =>
      let previous := scalarPowerWithCost a n
      (previous.1 * a, previous.2 + 1)

@[simp] theorem scalarPower_value (a : A) (n : ℕ) :
    (scalarPowerWithCost a n).1 = a ^ n := by
  induction n with
  | zero => simp [scalarPowerWithCost]
  | succ n ih => simp [scalarPowerWithCost, ih, pow_succ]

@[simp] theorem scalarPower_cost (a : A) (n : ℕ) :
    (scalarPowerWithCost a n).2 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [scalarPowerWithCost, ih]

end InversePreprocessing

end SubexponentialSAT.SubexpPolynomialCost

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CodeCandidates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The retained domain of the code search is one word of two-bit scalars.
The tuple counter visits all four digits; the physical converter rejects the
unused digits and produces the original scalar-frame arithmetic format. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidates

/-- The two bits are little endian, as in the supplied scalar encoding. -/
def digitBits (x : Bool × Bool) : List Bool := [x.1, x.2]

def invalidDigit (ternary : Bool) (x : Bool × Bool) : Bool :=
  if ternary then x.1 && x.2 else x.2

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidates
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CodeCandidateProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed-table conversion of one odometer tuple to one arithmetic candidate.
The input contains only the current candidate. The output is reversed scalar
frames, directly suitable for the existing word and matrix callbacks. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidateProgram

open CodeCandidates


/-- Fixed caller ports: dimension, consumed copy, current tuple, copy scratch,
and one-bit rejection latch. The embedding is chosen before any input. -/
structure ScanPorts (S : ℕ) where
  stack : Fin 5 ↪ Fin S

def scanRegisters : Fin 4 ↪ Fin 16 := ⟨Fin.castAdd 12, Fin.castAdd_injective _ _⟩

def scanInitializePorts {S : ℕ} (p : ScanPorts S) : Fin 2 ↪ Fin S :=
  ⟨![p.stack 1, p.stack 2], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [p.stack.injective.eq_iff]⟩


/-- Outer-search ports are dimension, consumed copy, current tuple, and copy
scratch. No saved-witness sentinel is seeded by this initializer. -/
def searchInitializePorts {S : ℕ} (ports : Fin 4 ↪ Fin S) : Fin 2 ↪ Fin S :=
  ⟨![ports 1, ports 2], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [ports.injective.eq_iff]⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidateProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_WalshExistenceCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fully finite exponential-moment sampling. No measure space or randomized
algorithm is involved: all averages below are sums over finite function spaces. -/

namespace SubexponentialSAT.SqrtLog.WalshExistence

open scoped BigOperators

variable {X A : Type*} [Fintype X] [Fintype A]

noncomputable def potential (f : A → X → ℝ) (D : ℕ) (ε : ℝ) (s : Fin D → X) : ℝ :=
  ∑ a, (Real.exp (ε * ∑ i, f a (s i)) + Real.exp (-ε * ∑ i, f a (s i)))

end SubexponentialSAT.SqrtLog.WalshExistence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CodeChecks
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

open OAI.Algorithms.SubexponentialSAT.SqrtLog

def graphStreamStacks : Fin 36 → Fin 40 := Fin.castAdd 4
def localStreamStacks : Fin 24 → Fin 40 := Fin.castAdd 16

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_CountModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Data for the exact-counting statement, corresponding to source lines 45–77.
The primitive execution and space obligations are separate from these data definitions. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse

/-- Canonical least-significant-bit-first binary, with a one-bit representation of zero. -/
def binaryNat (n : ℕ) : List Bool := if n = 0 then [false] else n.bits


@[simp] theorem binaryNat_zero : binaryNat 0 = [false] := rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_CanonicalWordProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Canonical unsigned binary output by a fixed finite word program.
The program reverses its input, removes high zeroes, reverses back, and emits
one false bit in the empty case. All source stack prefixes have a linear local
bound. No algebraic construction is imported to implement normalization. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CanonicalWordProgram

def zeroRegs : Fin 3 → Bool := fun _ => false

def dropZeroes : List Bool → List Bool
  | [] => []
  | false :: xs => dropZeroes xs
  | true :: xs => true :: xs

def nonemptyWord (xs : List Bool) : List Bool := if xs = [] then [false] else xs

def normalized (xs : List Bool) : List Bool := nonemptyWord (dropZeroes xs.reverse).reverse

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CanonicalWordProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseAccumulatorProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! A fixed finite binary accumulator with actual source traces and local prefixSteps bounds. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram.Accumulator

def registers : Fin 3 ↪ Fin 8 where
  toFun i := ⟨i.val, by omega⟩
  inj' := by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin 8 => x.val) h)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram.Accumulator
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseCountProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Appendix A: the mathematical depth-first transition and its count invariant.

The transition below specifies a leaf operation by its exact count. It is not a
primitive implementation of that operation, and no bit-time bound is asserted.
The pending list retains the current node and one sibling per branch on the
active path; completed leaves are discarded immediately.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram

open SAT
open scoped BigOperators

variable {n : ℕ}

/-- A width-`k` set of clauses has polynomial-size explicit syntax. -/
def formulaBound (n k : ℕ) : ℕ :=
  n + 2 + (4 + (8 * n + 8) * k) * ((k + 1) * (2 * n + 1) ^ k)


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseDFSBoundarySpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical storage at the depth-first controller boundary.

Only framed formula bodies occur on the pending stack. The mathematical depth
is a proof index and is not serialized. Both children, the current formula,
the declared-variable word, and the two count words are charged simultaneously.
These bounds apply to the actual fixed frontier and accumulator routines after
injective port relocation. The final DFS must still establish its boundary
invariant and bounds for the concrete selector, splitter, and leaf commands.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSBoundarySpace

def frontierBound (bodyBound depth : ℕ) : ℕ :=
  1 + (2 * bodyBound + 2) * (depth + 2)

/-- Local current, saved-n, pending and scratch ports. -/
def popStack : Fin 4 ↪ Fin 31 where
  toFun := ![13, 25, 24, 23]
  inj' := by decide

/-- Local pending, saved-n, framed children and scratch ports. -/
def pairStack : Fin 5 ↪ Fin 31 where
  toFun := ![24, 25, 26, 27, 0]
  inj' := by decide

/-- Local running total, current leaf count and scratch ports. -/
def countStack : Fin 3 ↪ Fin 31 where
  toFun := ![28, 29, 30]
  inj' := by decide

/-- DFS bookkeeping retains its original ports inside the frozen 1220-stack ABI.
Current formula, threshold, frontier, header and counts lie above its low scratch bank.
View port zero remains scratch, while view port thirteen is the formula. -/
def rootEmbedding : Fin 31 ↪ Fin 1220 where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 265, 14, 15, 16, 17, 18,
    259, 20, 21, 22, 23, 257, 258, 261, 262, 260, 263, 30]
  inj' := by decide

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSBoundarySpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_BinaryCompareProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Minimal actual binary comparison, extracted from SubexpGuardProgram.
Only the concrete Boolean borrow operation and fixed comparison machine are retained.
The source map and hashes are recorded in verification/counting-draft/worker04/extraction.json. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryCompareProgram

open OAI.Algorithms.SubexponentialSAT.BinaryArithmetic

def borrowBit (a b borrow : Bool) : Bool :=
  ((!a) && (b || borrow)) || (b && borrow)

namespace Compare

/-- Borrow propagation with implicit high zero bits. -/
def carry (c : Bool) : List Bool → List Bool → Bool
  | [], [] => c
  | a :: xs, [] => carry (borrowBit a false c) xs []
  | [], b :: ys => carry (borrowBit false b c) [] ys
  | a :: xs, b :: ys => carry (borrowBit a b c) xs ys
termination_by xs ys => xs.length + ys.length

def operandStacks (xs ys : List Bool) (i : Fin 2) : List Bool :=
  if i = 0 then xs else ys

@[simp] theorem operandStacks_left (xs ys : List Bool) : operandStacks xs ys 0 = xs := rfl
@[simp] theorem operandStacks_right (xs ys : List Bool) : operandStacks xs ys 1 = ys := rfl

end Compare


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryCompareProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete record-count and emission primitives extracted from supplied sources.
No sparsification schedule or formula evaluator is imported. Provenance is recorded
in verification/counting-draft/worker04/extraction.json. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityPrimitives

open BinaryArithmetic

namespace Tuple

def workReg (i : Fin 8) : Fin 13 := Fin.castAdd 5 i
def pairPort (left right : Fin 9) (i : Fin 2) : Fin 9 := if i = 0 then left else right

end Tuple

namespace Count

def countReg (i : Fin 2) : Fin 13 := Fin.castAdd 11 i
def countStack (i : Fin 2) : Fin 9 := if i = 0 then 5 else 7

def binaryReg (i : Fin 3) : Fin 13 := Fin.castAdd 10 i
def binaryStack (i : Fin 4) : Fin 9 :=
  if i = 0 then 7 else if i = 1 then 5 else if i = 2 then 6 else 8

def expectedPort (i : Fin 2) : Fin 9 := if i = 0 then 3 else 4

end Count

namespace FrameWriter

def triple {α : Type*} (a b c : α) : Fin 3 → α :=
  fun i => if i = 0 then a else if i = 1 then b else c

@[simp] theorem triple_zero {α : Type*} (a b c : α) : triple a b c 0 = a := rfl
@[simp] theorem triple_one {α : Type*} (a b c : α) : triple a b c 1 = b := rfl
@[simp] theorem triple_two {α : Type*} (a b c : α) : triple a b c 2 = c := rfl

def quadruple {α : Type*} (a b c d : α) : Fin 4 → α :=
  fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d

@[simp] theorem quadruple_zero {α : Type*} (a b c d : α) : quadruple a b c d 0 = a := rfl
@[simp] theorem quadruple_one {α : Type*} (a b c d : α) : quadruple a b c d 1 = b := rfl
@[simp] theorem quadruple_two {α : Type*} (a b c d : α) : quadruple a b c d 2 = c := rfl
@[simp] theorem quadruple_three {α : Type*} (a b c d : α) : quadruple a b c d 3 = d := rfl

def parserRegister : Fin 2 → Fin 3 := Fin.castAdd 1
def parserStack (i : Fin 2) : Fin 4 := if i = 0 then 0 else 3
def parserLabel : Fin 7 → Fin 17 := Fin.castAdd 10


end FrameWriter

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityPrimitives
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete components of the sharp clause/core search from Appendix A.
The guard counts actual framed literals and executes the preserving subset tester.
The complete search and its polynomial resource bound are developed separately below. -/


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram

/-- All masks have fixed length `k`; the finite control table depends only on `k`. -/
def masks : ℕ → List (List Bool)
  | 0 => [[]]
  | k + 1 => (masks k).map (false :: ·) ++ (masks k).map (true :: ·)

@[simp] theorem mem_masks (mask : List Bool) (k : ℕ) : mask ∈ masks k ↔ mask.length = k := by
  induction k generalizing mask with
  | zero => simp [masks]
  | succ k ih =>
    cases mask with
    | nil => simp [masks]
    | cons b mask => cases b <;> simp [masks, ih]

@[simp] theorem masks_length (k : ℕ) : (masks k).length = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [masks, ih, pow_succ, Nat.mul_comm, two_mul]

namespace Selector

def maskStack : Fin 4 → Fin 24 := ![10, 11, 8, 9]

def filterStack : Fin 14 → Fin 24 := ![0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 16, 10, 12, 11]

def sizeStack : Fin 9 → Fin 24 := ![0, 1, 2, 20, 17, 5, 6, 7, 8]

def thresholdStack : Fin 9 → Fin 24 := ![0, 1, 2, 3, 17, 5, 6, 7, 8]

def powerStack : Fin 9 → Fin 24 := ![19, 10, 17, 0, 1, 2, 3, 4, 5]

def eraseWords (ports : List (Fin 24)) (store : Fin 24 → List Bool) : Fin 24 → List Bool :=
  fun i => if i ∈ ports then [] else store i

def passes (k : ℕ) : List (ℕ × ℕ × List Bool) :=
  (List.range (k - 1)).flatMap fun i =>
    (List.range (i + 1)).flatMap fun j =>
      (masks k).map fun mask => (i + 2, i + 1 - j, mask)

def powerCoefficient (exponent : ℕ) : ℕ :=
  100 * (exponent + 1) ^ 2 + 20 * (exponent + 1) * (exponent.bits.length + 1) + 6

def phaseScale (c h : ℕ) (mask : List Bool) : ℕ :=
  2 + mask.length + c.bits.length + h.bits.length + (c - h) + 2

def phaseCoefficient (c h : ℕ) (mask : List Bool) : ℕ :=
  1000 * (c.bits.length + 2) ^ 3 + (powerCoefficient (c - h) + 2 * h.bits.length + 14) +
    3000 * phaseScale c h mask ^ 4 + (10 * phaseScale c h mask + 15)

def selectorCoefficient (k : ℕ) : ℕ :=
  1 + ((passes k).map fun p => phaseCoefficient p.1 p.2.1 p.2.2).sum + 2 * (passes k).length

end Selector

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNegatedQueryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preserving complemented-literal queries

The clause iterator supplies a literal's unary word in reverse order. This
fixed program preserves that query on stack 0 and writes the reversed unary
word for the opposite literal on stack 1. Stacks 2 and 3 are empty workspaces
on entry and return. All costs below count actual finite-program transitions.
-/

namespace SubexponentialSAT.SubexpNegatedQueryProgram

/-- Only the work and result ports are assigned to the unary complementer. -/
def negatePorts (i : Fin 2) : Fin 4 := if i = 0 then 2 else 1

end SubexponentialSAT.SubexpNegatedQueryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTautologyProgram
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

def negateReg (i : Fin 2) : Fin 10 := Fin.castAdd 8 i

def negateStack (i : Fin 4) : Fin 8 :=
  match i.val with
  | 0 => 7
  | 1 => 1
  | 2 => 5
  | _ => 6

end SubexponentialSAT.SubexpTautologyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_NegatedCoreProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete negated singleton generation for the disjoint B child.
The fixed routine consumes a unary literal-record list on stack 0 and prepends
its negated singleton clauses to the encoded formula on stack 2. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.NegatedCoreProgram

def innerStack (i : Fin 4) : Fin 8 :=
  if i = 0 then 0 else if i = 1 then 6 else if i = 2 then 3 else 1

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.NegatedCoreProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointSparsifyProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! List-level outputs for the concrete disjoint splitter.
The declared variable universe is retained by the surrounding controller.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram

open OAI.Algorithms.SubexponentialSAT.SAT

/-- The iterator prepends each generated unit, so the core order is reversed. -/
def negatedUnits {α : Type*} (negate : α → α) (H : List α) : List (List α) :=
  H.reverse.map fun l => [negate l]

/-- The unit builder has eight scratch ports, disjoint from the retained core
and selected family. Its accumulator is the parent formula port. -/
def unitRegister (i : Fin 10) : Fin 15 := Fin.castAdd 5 i

def unitStack : Fin 8 → Fin 16 := ![0, 1, 13, 2, 3, 4, 5, 6]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseDFSProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed finite control for the outer disjoint counting traversal.

The leaf command is an explicit piece of finite code chosen with `k`. Its
layout, reconstruction, input loading and output export are still
separate obligations until the concrete leaf implementation is substituted.
There is no oracle instruction or endpoint theorem in this module.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram

def registers (r : ℕ) (hr : r ≤ 80) : Fin r ↪ Fin 80 := Fin.castLEEmb hr

def selectorStack : Fin 24 ↪ Fin 1220 :=
  (Fin.castLEEmb (by decide : 24 ≤ 31)).trans SparseDFSBoundarySpace.rootEmbedding

def frontierStack : Fin 4 ↪ Fin 1220 :=
  SparseDFSBoundarySpace.popStack.trans SparseDFSBoundarySpace.rootEmbedding

def pairStack : Fin 5 ↪ Fin 1220 :=
  SparseDFSBoundarySpace.pairStack.trans SparseDFSBoundarySpace.rootEmbedding

def countStack : Fin 3 ↪ Fin 1220 :=
  SparseDFSBoundarySpace.countStack.trans SparseDFSBoundarySpace.rootEmbedding

/-- The splitter keeps the threshold outside its entire local footprint. -/
def splitterView : Fin 23 ↪ Fin 31 where
  toFun := ![24, 25, 26, 27, 13, 9, 12, 0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 14, 15, 16, 17, 18]
  inj' := by decide

def splitterStack : Fin 23 ↪ Fin 1220 :=
  splitterView.trans SparseDFSBoundarySpace.rootEmbedding

opaque lowPortsWrapped :
    {ports : List (Fin 1220) //
      ports = (List.finRange 256).map (Fin.castLE (by decide : 256 ≤ 1220))} :=
  ⟨(List.finRange 256).map (Fin.castLE (by decide : 256 ≤ 1220)), rfl⟩

/-- The fixed low-workspace ports, kept opaque to avoid reducing the entire
256-element instruction table during routine typeclass and theorem checking. -/
def lowPorts : List (Fin 1220) := lowPortsWrapped.1


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_EncodingBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Canonical count words and the conversion from encoded length to declared input size. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

@[simp] theorem countWord_zero : countWord 0 = [false] := rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CountDFS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Typed refinement of the concrete streaming frontier.

Depths and derivation trees below are proof indices. The physical pending tape
contains only formula bodies, and every formula keeps the same declared `Fin n`.
The selector and leaf execution contracts must still be supplied by their actual
finite programs; this module does not postulate a final counting service.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement

open SAT SparsePriorityProgram

variable {n : ℕ}

@[simp] theorem binaryNat_eq_countWord (a : ℕ) :
    binaryNat a = OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord a := rfl

open SparseDFSProgram

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DifferencePairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Pruned finite-difference traversal. `none`, `some false`, and `some true`
encode membership in neither set, in `E \ U`, and in `U`, respectively.
`words` specifies visit order; the streaming fold does not construct it. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairs

open scoped BigOperators
open BooleanDifferences

def words : ℕ → ℕ → List (List (Option Bool))
  | _, 0 => []
  | 0, _ + 1 => [[]]
  | n + 1, J + 1 =>
      (words n (J + 1)).map (none :: ·) ++
        (words n J).map (some false :: ·) ++
        (words n J).map (some true :: ·)

@[simp] theorem words_zero (n : ℕ) : words n 0 = [] := by cases n <;> rfl

@[simp] theorem mem_words (n J : ℕ) (w : List (Option Bool)) :
    w ∈ words n J ↔ w.length = n ∧ w.countP Option.isSome < J := by
  induction n generalizing J w with
  | zero =>
      cases J with
      | zero => simp [words]
      | succ J => cases w <;> simp [words]
  | succ n ih =>
      cases J with
      | zero => simp
      | succ J =>
          cases w with
          | nil => simp [words]
          | cons b w =>
              cases b with
              | none => simp [words, ih]
              | some b => cases b <;> simp [words, ih]

def pairCount : ℕ → ℕ → ℕ
  | _, 0 => 0
  | 0, _ + 1 => 1
  | n + 1, J + 1 => pairCount n (J + 1) + 2 * pairCount n J

@[simp] theorem pairCount_zero (n : ℕ) : pairCount n 0 = 0 := by cases n <;> rfl

@[simp] theorem words_length (n J : ℕ) : (words n J).length = pairCount n J := by
  induction n generalizing J with
  | zero => cases J <;> rfl
  | succ n ih =>
      cases J with
      | zero => rfl
      | succ J => simp [words, pairCount, ih]; omega

def encodePair {n : ℕ} (E U : Finset (Fin n)) : List (Option Bool) :=
  List.ofFn (fun i => if i ∈ E then some (decide (i ∈ U)) else none)

def calls : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 1
  | n + 1, J + 1 => 1 + calls n (J + 1) + 2 * calls n J

@[simp] theorem calls_zero (n : ℕ) : calls n 0 = 1 := by cases n <;> rfl

/-- Runtime recursion retains one prefix and invokes its callback immediately.
The three branches share the accumulator; no list of completed pairs is built. -/
def fold {α : Type*} (visit : List (Option Bool) → α → α) :
    ℕ → ℕ → List (Option Bool) → α → α
  | _, 0, _, acc => acc
  | 0, _ + 1, pre, acc => visit pre acc
  | n + 1, J + 1, pre, acc =>
      let acc := fold visit n (J + 1) (pre ++ [none]) acc
      let acc := fold visit n J (pre ++ [some false]) acc
      fold visit n J (pre ++ [some true]) acc

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairs
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DifferencePairsProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed finite control for the pruned pair DFS. Four protected stacks hold
remaining depth, remaining strict budget, and the two current masks. The masks
also encode the DFS phases `00`, `10`, `11`; no completed-pair list is retained.
The callback receives the masks in reverse coordinate order. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram

structure Ports (r s : ℕ) where
  register : Fin 5 ↪ Fin r
  stack : Fin 4 ↪ Fin s

variable {r s : ℕ}

def cost (C n J : ℕ) : ℕ := (C + 46) * (3 * n + 1) * DifferencePairs.pairCount n J + 10

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_BinaryClogProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual floor and ceiling logarithm bit programs, without packing or schedule imports. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Floor

/-- Consume leading zeroes and the first one of a most-significant-first word. -/
def trimTail : List Bool → List Bool
  | [] => []
  | false :: xs => trimTail xs
  | true :: xs => xs

def trimCost : List Bool → ℕ
  | [] => 5
  | false :: xs => trimCost xs + 3
  | true :: _ => 6

/-! ## Concrete input reversal -/

/-! ## Reindex and call the checked binary word-length counter -/

def swapStacks : Equiv.Perm (Fin 3) := Equiv.swap 0 1

def logBound (L : ℕ) : ℕ := L * (8 * L + 16) + 12

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Floor

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Setup

def incrementPorts : Fin 2 → Fin 3 := ![0, 1]


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Setup
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_ParameterBank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed Boolean-stack arithmetic in a 19-word data bank and 13 scratch stacks. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.ParametersProgram

open BinaryArithmetic

abbrev Regs := Fin 8 → Bool
abbrev Words := Fin 19 → List Bool


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.ParametersProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime, self-delimiting natural-index alphabet. The range control is the
existing unary loop, with one delimiter inserted in each emitted payload. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram.Index

def steps : ℕ → ℕ → ℕ
  | _, 0 => 1
  | j, n+1 => 12*j+30 + steps (j+1) n

end SubexponentialSAT.SqrtLog.RowSelectionProgram.Index

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMassStaged
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid physical source assembly precedes all marked queries. The candidate
is prepended to a copied history stream; neither retained word is changed.
The temporary source masters are cleared after the complete natural mass. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged

open SqrtLog

/-- These are exactly the lower ports changed by the original trial staging. -/
def stagedPorts : List (Fin 896) := [700,701,702,707,708,709]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SparseCodeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Sparse rows from the candidates actually selected by the search

The construction below consumes the selected shifts and local matrix explicitly. Its
proofs need their checked Walsh and distance properties, not identity with the old
materialized search's selected candidates. The finite list of final rows is polynomial
size and can be retained; lists of all candidates and all test words cannot.
-/



namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.SqrtLog

/-- The runtime dimension is preserved; every other port here is temporary. -/
def localScanPorts : CodeCandidateProgram.ScanPorts 40 where
  stack := ⟨![21, 27, 24, 23, 25], by decide⟩

def graphScanPorts : CodeCandidateProgram.ScanPorts 40 where
  stack := ⟨![33, 39, 36, 35, 37], by decide⟩

/-- The core workspace is polynomial in the initial retained data and one
candidate's arithmetic budget, independently of how many words are checked. -/
def coreSpace (A dimension callbackCost : ℕ) : ℕ :=
  max (A + 6 * dimension + 1 + callbackCost + 68 * dimension + 24)
    (40 * (A + 6 * dimension + 1) + 7 * (6 * dimension + 1) + 4)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.SqrtLog

def matrixCheckTime (A matrixDimension wordDimension callbackCost streamCost : ℕ) : ℕ :=
  streamCost + 15 * wordDimension + 2 * coreSpace (A + 5 * matrixDimension) wordDimension callbackCost + 19

def matrixCheckSpace (A matrixDimension wordDimension callbackCost : ℕ) : ℕ :=
  max (40 * (A + 5 * matrixDimension) + 15 * wordDimension +
    43 * coreSpace (A + 5 * matrixDimension) wordDimension callbackCost + 18)
    (A + 5 * matrixDimension)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.SqrtLog

def candidateBudget (A matrixDimension wordDimension callbackCost streamCost : ℕ) : ℕ :=
  matrixCheckTime A matrixDimension wordDimension callbackCost streamCost +
    2 * A + 73 * matrixDimension + 23

def candidateSpace (A matrixDimension wordDimension callbackCost : ℕ) : ℕ :=
  max (3 * A + 73 * matrixDimension + 23)
    (matrixCheckSpace A matrixDimension wordDimension callbackCost)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_TotalOrderArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit fixed-length arrays and truncated convolution for the shared marker. -/
namespace SubexponentialSAT.SqrtLog.TotalOrder

open scoped BigOperators

variable {R : Type*} [CommSemiring R]

/-- Exactly t retained coefficients. This is a finite executable function. -/
abbrev CoeffArray (R : Type*) (t : ℕ) := Fin t → R

/-- Out-of-range reads are zero. -/
def arrayCoeff {t : ℕ} (a : CoeffArray R t) (j : ℕ) : R :=
  if hj : j < t then a ⟨j, hj⟩ else 0

@[simp] theorem arrayCoeff_lt {t j : ℕ} (a : CoeffArray R t) (hj : j < t) :
    arrayCoeff a j = a ⟨j, hj⟩ := by simp [arrayCoeff, hj]

@[simp] theorem arrayCoeff_ge {t j : ℕ} (a : CoeffArray R t) (hj : t ≤ j) :
    arrayCoeff a j = 0 := by simp [arrayCoeff, Nat.not_lt.mpr hj]

/-- Each output coefficient is a finite convolution over i+j=k. -/
def mulArray {t : ℕ} (a b : CoeffArray R t) : CoeffArray R t := fun k =>
  ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k.val,
    arrayCoeff a ij.1 * arrayCoeff b ij.2

noncomputable section

/-- Polynomial semantics of the finite array. -/
def asPolynomial {t : ℕ} (a : CoeffArray R t) : Polynomial R :=
  ∑ j ∈ Finset.range t, Polynomial.monomial j (arrayCoeff a j)

@[simp] theorem coeff_asPolynomial {t : ℕ} (a : CoeffArray R t) (j : ℕ) :
    (asPolynomial a).coeff j = arrayCoeff a j := by
  classical
  by_cases hj : j < t
  · simp [asPolynomial, Polynomial.coeff_monomial, hj]
  · simp [asPolynomial, Polynomial.coeff_monomial, hj,
      arrayCoeff]

def toArray (t : ℕ) (P : Polynomial R) : CoeffArray R t := fun j => P.coeff j.val

@[simp] theorem toArray_asPolynomial {t : ℕ} (a : CoeffArray R t) :
    toArray t (asPolynomial a) = a := by
  funext j
  simp [toArray, j.isLt]

end
end SubexponentialSAT.SqrtLog.TotalOrder

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_TruncatedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Dense lifting and Taylor coefficients

`Truncated R n` stores exactly `n` coefficients. Its multiplication is the
existing total-order convolution, and its ring laws follow from the surjective
coefficient projection from `R[X]`. Nesting the construction stores the shared
lifting marker outside the Taylor variable. The final marker readout is additive.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog.TotalOrder

/-- A dense canonical representative modulo the indicated power of the variable. -/
@[ext] structure Truncated (R : Type*) (n : ℕ) where
  coeff : Fin n → R

namespace Truncated

variable {R : Type*} {n : ℕ}

instance instZero [Zero R] : Zero (Truncated R n) := ⟨⟨fun _ => 0⟩⟩
instance instOneOfZero [Zero R] [One R] : One (Truncated R n) :=
  ⟨⟨fun j => if j.val = 0 then 1 else 0⟩⟩
instance instAdd [Add R] : Add (Truncated R n) := ⟨fun a b => ⟨fun j => a.coeff j + b.coeff j⟩⟩
instance instSMulNat [SMul ℕ R] : SMul ℕ (Truncated R n) := ⟨fun k a => ⟨fun j => k • a.coeff j⟩⟩
instance instNatCastOfZero [Zero R] [NatCast R] : NatCast (Truncated R n) :=
  ⟨fun k => ⟨fun j => if j.val = 0 then k else 0⟩⟩
instance instMulOfCommSemiring [CommSemiring R] : Mul (Truncated R n) :=
  ⟨fun a b => ⟨mulArray a.coeff b.coeff⟩⟩
instance instPowNatOfCommSemiring [CommSemiring R] : Pow (Truncated R n) ℕ := ⟨fun a k => npowRec k a⟩

@[simp] theorem coeff_zero [Zero R] (j : Fin n) : (0 : Truncated R n).coeff j = 0 := rfl
@[simp] theorem coeff_one [Zero R] [One R] (j : Fin n) :
    (1 : Truncated R n).coeff j = if j.val = 0 then 1 else 0 := rfl
@[simp] theorem coeff_add [Add R] (a b : Truncated R n) (j : Fin n) :
    (a + b).coeff j = a.coeff j + b.coeff j := rfl
@[simp] theorem coeff_nsmul [SMul ℕ R] (k : ℕ) (a : Truncated R n) (j : Fin n) :
    (k • a).coeff j = k • a.coeff j := rfl
@[simp] theorem coeff_natCast [Zero R] [NatCast R] (k : ℕ) (j : Fin n) :
    (k : Truncated R n).coeff j = if j.val = 0 then (k : R) else 0 := rfl

section Semiring

variable [CommSemiring R]

/-- Explicit bounded convolution, with out-of-range reads equal to zero. -/
theorem coeff_mul (a b : Truncated R n) (j : Fin n) :
    (a * b).coeff j = ∑ uv ∈ Finset.HasAntidiagonal.antidiagonal j.val,
      arrayCoeff a.coeff uv.1 * arrayCoeff b.coeff uv.2 := rfl

end Semiring

end Truncated

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeBasic
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

def boolValue (x : V → Bool) (v : V) : R := if x v then 1 else 0

end
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed frame emitter. The source is a reversed payload. It is consumed
and the forward framed payload is prepended to the destination. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program

def emitPairs : List Bool → List Bool → List Bool
  | [], out => out
  | b :: bs, out => emitPairs bs (true :: b :: out)

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationEmitProgram
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
open SubexponentialSAT

/-- Swapping the key helper's mask port protects the caller's beta on220. -/
def keyMap : Equiv.Perm (Fin 256) := Equiv.swap 214 220
def emitRegisters (i : Fin 3) : Fin 16 := i.castAdd 13
def stepBudget (j n W : ℕ) : ℕ := 27*W+20*(j+n)+81

end SubexponentialSAT.SqrtLog.PerturbationEmitProgram


namespace SubexponentialSAT.SqrtLog.PerturbationEmitProgram
open SubexponentialSAT

def array (cs : List (List Bool)) : List Bool := cs.flatten

def loopBudget (j n W N : ℕ) : ℕ := N*(stepBudget (j+N) n W+2)+2

end SubexponentialSAT.SqrtLog.PerturbationEmitProgram


namespace SubexponentialSAT.SqrtLog.PerturbationEmitProgram
open SubexponentialSAT

def budget (J n W : ℕ) : ℕ := 9*J+16*W+loopBudget 1 n W J+29

end SubexponentialSAT.SqrtLog.PerturbationEmitProgram


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationMaskProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed native constructor for original-coordinate singleton masks.
Masters212/218 are retained; output214 and scratch120/221/222/223 are the
only touched stacks. No table of masks or semantic mask oracle is supplied. -/
namespace SubexponentialSAT.SqrtLog.PerturbationMaskProgram
open SubexponentialSAT

def bits (n j : ℕ) : List Bool :=
  List.replicate j false ++ true :: List.replicate (n-j-1) false

@[simp] theorem bits_length (n j : ℕ) (hj : j < n) : (bits n j).length=n := by
  simp only [bits,List.length_append,List.length_replicate,List.length_cons]
  omega

end SubexponentialSAT.SqrtLog.PerturbationMaskProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyOrigin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Emit the computed beta at the actual all-zero sparse key. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT

def originScratch : List (Fin 256) := [120,214,221,222,223,224,226,227,228]

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native high-variable dispatch from original-coordinate mask/assignment
masters. The runtime index is233, and both source masters are retained. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT

def flagStacks : Fin 2 → Fin 256 := ![222,223]


end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpResidueInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable inversion by finite-field powering and nilpotent correction

The algorithm uses only scalar additions and multiplications, with explicit
finite loops. It constructs the entire inverse-difference table needed by CRT.
Its counters are ring-operation counts, not an assertion of machine time.
-/

namespace SubexponentialSAT.SubexpResidueInverse

open scoped BigOperators

section Algorithm

variable {A : Type*} [CommRing A]

/-- A shared Horner recurrence for the finite geometric sum. -/
def geometricHornerWithCost (z : A) : ℕ → A × ℕ
  | 0 => (0, 0)
  | n + 1 =>
      let previous := geometricHornerWithCost z n
      (z * previous.1 + 1, previous.2 + 2)

@[simp] theorem geometricHorner_cost (z : A) (n : ℕ) :
    (geometricHornerWithCost z n).2 = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [geometricHornerWithCost, ih]; omega

/-- Power to `q-2`, then correct the nilpotent defect. Negation is implemented
as multiplication by the fixed constant `-1`, and is included in the count. -/
def inverseWithCost (q μ : ℕ) (a : A) : A × ℕ :=
  let b := SubexpPolynomialCost.scalarPowerWithCost a (q - 2)
  let ab := a * b.1
  let negab := (-1 : A) * ab
  let z := negab + 1
  let g := geometricHornerWithCost z μ
  (b.1 * g.1, b.2 + 3 + g.2 + 1)

@[simp] theorem inverseWithCost_cost_eq (q μ : ℕ) (a : A) :
    (inverseWithCost q μ a).2 = (q - 2) + 2 * μ + 4 := by
  simp only [inverseWithCost, SubexpPolynomialCost.scalarPower_cost, geometricHorner_cost]
  omega

end Algorithm

end SubexponentialSAT.SubexpResidueInverse

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationProgramPaddingRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PerturbationProgram.Padding
open SubexponentialSAT

def budget (N D W : ℕ) : ℕ := 9*(N*W)+7 + (N*(260*(D+1)*(W+1)+2)+2)

end SubexponentialSAT.SqrtLog.PerturbationProgram.Padding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid construction of the polynomial Horner point and seed. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT

def constantScratch : List (Fin 256) := [100,101,102,107,108,120,239,245,247,254]

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native composition from a complete scalar coefficient row to its shifted
jet. Padding and both runtime counters are executed, rather than supplied. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT
open PerturbationProgram

def shiftScratch : List (Fin 256) :=
  [100,101,102,107,108,120,240,241,244,245,246,248,250,251,252,253]

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationBetaProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native beta evaluation.  The caller supplies actual coefficient arrays,
not evaluated row values.  Masters205..212 are preserved;220 is the result.
Work230/231/232 holds the framed row scan, choice scan and reverse buffer. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram

open SubexponentialSAT

abbrev Store := Fin 256 → List Bool

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyCoordinate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Per-coordinate physical composition. Original ambient variable IDs remain
unchanged throughout row loading, singleton support construction and emission. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT

def coordinateLoadScratch : List (Fin 256) := [120,214,219,221,222,223,232,245,246]

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyEntry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Frame an actual completed incidence dictionary under its original variable
ID. The table accumulator is229; all coefficient-emitter work ports are free. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT

def tableMap : Equiv.Perm (Fin 256) := Equiv.swap 217 229

def entryScratch : List (Fin 256) := [120,222,223,224,226,227,228,245]

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native traversal of the actual runtime-framed row list. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT

def rowsResult {C : Type*} (step : ℕ → C → List Bool → List Bool) :
    ℕ → List C → List Bool → List Bool
  | _, [], acc => acc
  | j, c::cs, acc => rowsResult step (j+1) cs (step j c acc)


end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Dynamic target-jet cache installation. Full source-degree metadata at210
is untouched while the arithmetic count is temporarily changed to213. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT

def targetScratch : List (Fin 256) :=
  [100,101,102,107,108,120,236,237,238,239,245,247,254]

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationBetaProgramFraming
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid preserving copies of every beta master and explicit scratch cleanup. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram
open SubexponentialSAT

def initialized (s : Store) : Store :=
  Function.update (Function.update (Function.update (Function.update (Function.update s
    230 (s 205)) 231 (s 206)) 220 (s 207)) 247 (s 209)) 250 (s 211)

def initBudget (s : Store) : ℕ :=
  7*(s 205).length+7*(s 206).length+7*(s 207).length+
    7*(s 209).length+7*(s 211).length+25

def finished (s : Store) : Store :=
  Function.update (Function.update (Function.update (Function.update s 230 []) 231 []) 247 []) 250 []

def finishBudget (s : Store) : ℕ :=
  2*(s 230).length+2*(s 231).length+2*(s 247).length+2*(s 250).length+12

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationBetaProgramRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed native beta scan from preserved row/choice masters. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram
open SubexponentialSAT

def workPorts : List (Fin 256) := [220,230,231,232,240,241,244,245,246,247,248,250,251,252]
def WorkEmpty (s : Store) : Prop := ∀ i∈workPorts,s i=[]

def staged (s : Store) : Store :=
  Function.update (Function.update s 247 (s 209)) 250 (s 211)

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Executable incidence preparation. The inner worker has no arithmetic,
mask, beta, shifted-polynomial or dictionary oracle. Source generation is
composed as a fixed command in the outer768-stack frame. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT

def innerPort (i : Fin 256) : Fin 768 := ⟨340 + i.val, by omega⟩

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpDensePaddingSpec
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

def padCells {C : Type*} (zero : C) : ℕ → List C → List C
  | 0, _ => []
  | n + 1, [] => zero :: padCells zero n []
  | n + 1, a :: as => a :: padCells zero n as

@[simp] theorem padCells_nil {C : Type*} (zero : C) (n : ℕ) :
    padCells zero n [] = List.replicate n zero := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa only [padCells, List.replicate_succ] using (congrArg (List.cons zero) ih)

@[simp] theorem padCells_length {C : Type*} (zero : C) (n : ℕ) (xs : List C) :
    (padCells zero n xs).length = n := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => cases xs <;> simp [padCells, ih]

end SubexponentialSAT.SubexpDensePaddingSpec

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source-sensitive costs and validity of the generic coefficient-array
interpreter, independently of its native arithmetic implementation. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT

def binaryBound (K W : ℕ) : ℕ := K + 20*(W+W) + 8*W + 69

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Arithmetic callbacks on a fixed stream ABI. The remaining record stream is
preserved byte-for-byte across each real signed-arithmetic call. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

def combine (multiply : Bool) (a b : ℤ) : ℤ := if multiply then a*b else a+b

def wordGrowth (multiply : Bool) (a b : ℕ) : ℕ :=
  if multiply then 2*(a+b)+6 else a+b+2

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SpectralBinomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exponential concentration for the exact binomial swap spectrum.
All distribution parameters are explicit; no arity parameter is fixed. -/

namespace SubexponentialSAT.SqrtLog.Spectral

open scoped BigOperators

def binomialMean (θ : ℝ) (q : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ w ∈ Finset.range (q + 1),
    (q.choose w : ℝ) * (1 - θ) ^ (q - w) * θ ^ w * f w

end SubexponentialSAT.SqrtLog.Spectral

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryRankProvenance
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

/-- Distinct nonzero rational nodes suffice for this integer rank proof.
They are proof data and cause no change to the executed finite-ring code. -/
def rationalNode (Q : ℕ) (i : Fin Q) : ℚ := (i.val:ℚ)+1

end SubexponentialSAT.SqrtLog.ProducedQueryRank

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProgramTapeReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact-time replay under replacement of syntactically untouched tapes. -/
namespace SubexponentialSAT.SqrtLog.ProgramTapeReplay
open SubexponentialSAT

variable {r s l : ℕ}

def rebaseStacks (H : Fin s → Prop) [DecidablePred H]
    (frame data : Fin s → List Bool) : Fin s → List Bool :=
  fun i => if H i then frame i else data i

end SubexponentialSAT.SqrtLog.ProgramTapeReplay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Integer selection of a sufficient Hasse-jet order. -/

namespace SubexponentialSAT.SqrtLog.Reconstruction

/-- The marked-query allowance is explicit and does not multiply precision
by the number of hash factors. -/
def markedDegreeBound (width rowDegree hashes precision : ℕ) : ℕ :=
  width * rowDegree * (2 * hashes + 3 * (precision - 1) + 1)

end SubexponentialSAT.SqrtLog.Reconstruction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramCofactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native scalar cofactor construction for the Hermite value at zero. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor

open SubexponentialSAT

def includeBudget (K W J : ℕ) : ℕ := (J + 1) * (K + 8 * W + 11) + 63 * W + 7 * J + 70

def includeValue {C : Type*} (mul : C → C → C) (minusOne : C) (J : ℕ) (a c : C) : C :=
  (fun x => mul x (mul c minusOne))^[J] a


end SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCRTOuterSweep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Ordered execution of the concrete outer CRT tape loop. The only remaining
premise is an actual execution of its arithmetic middle command on the exact
loaded state; all loading, index updates, traversal guards, and transport costs
are discharged here. This premise is instantiated by the concrete CRT services.
-/

namespace SubexponentialSAT.SubexpCRTOuterProgram

/-- Physical per-node cost, excluding the arithmetic middle command. The
index copy contributes nine steps per already processed node. -/
def transportCost (nodeWidth jetWidth index : ℕ) : ℕ :=
  32 * nodeWidth + 9 * index + 16 * jetWidth + 51

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCRTOuterFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Final cleanup and complete tape-loop costs for scalar reconstruction.
The arithmetic-middle premise below is an actual execution of a fixed command;
its concrete implementation is assembled separately from the CRT services. -/

namespace SubexponentialSAT.SubexpCRTOuterProgram

open scoped BigOperators

def cleanupBudget (W J Q D : ℕ) : ℕ :=
  2 * W + 4 * Q * W + 2 * Q + 2 * D + 2 * J + 24

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramCofactorOuter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter

open SubexponentialSAT SubexpCRTOuterProgram

def budget (N K W J : ℕ) : ℕ :=
  N * (Cofactor.includeBudget K W J + 25 * W + 28) + 13 * W + 24

end SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramEntry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical preparation of the low scalar caches used by dense polynomial
addition. The high copies remain available to all native ring services. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Entry

open SubexponentialSAT SubexpCRTOuterProgram

def prepared (s : Fin 320 → List Bool) : Fin 320 → List Bool :=
  Function.update (Function.update s 5 (s 194)) 10 (s 202)

def budget (modulusBits widthTokens : ℕ) : ℕ := 7 * modulusBits + 7 * widthTokens + 10

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Entry

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid cache setup and framing for the lower local Hermite-CRT routine. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Local

open SubexponentialSAT SubexpCRTOuterProgram

def budget (zeroBits order K : ℕ) : ℕ := K + 9 * zeroBits + 9 * order + 17

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Local

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framed outer calls to the native scalar ring arithmetic. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar

open SubexponentialSAT SubexpCRTOuterProgram

def safe (p : Fin 320) : Prop := p ≠ 240 ∧ p ≠ 241 ∧ p ≠ 244 ∧ p ≠ 318 ∧ p ≠ 319

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramLoaded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framing lemmas for the exact states reached by the physical node sweep. -/

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram

open SubexponentialSAT SubexpCRTOuterProgram

abbrev Store := Fin 320 → List Bool

def sweepChanged : List (Fin 320) := [213,216,225,257,258,259,260,261,266]
def initializationChanged : List (Fin 320) := [104,261,268,277,214,257,266]

end SubexponentialSAT.SqrtLog.ReconstructionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramPolynomialCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A uniform polynomial bound on the complete primitive CRT program. The
residue-field cardinality is a runtime dimension, as are all tape widths. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Native

def costConstant : ℕ := 10000*1000001^3+1000000

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramSelectFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed framing primitive for the scored-record writer. It consumes the
input bits and prepends the frame of their reversal to the output stack. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgramSelect

def frameOutput (bits out : List Bool) : List Bool :=
  bits.reverse.flatMap (fun b => [true,b]) ++ out

end SubexponentialSAT.SqrtLog.RowSelectionProgramSelect

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeKeyMapProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

structure Store where
  source : List Bool := []
  leftKey : List Bool := []
  tMaster : List Bool := []
  jMaster : List Bool := []
  output : List Bool := []
  keyRev : List Bool := []
  coeffRev : List Bool := []
  tmp : List Bool := []
  rightKey : List Bool := []
  leftCopy : List Bool := []
  joinedRev : List Bool := []
  clipKey : List Bool := []
  tCopy : List Bool := []
  jCopy : List Bool := []
  clipTmp : List Bool := []

def tapes (s : Store) : Fin 15 → List Bool :=
  ![s.source,s.leftKey,s.tMaster,s.jMaster,s.output,s.keyRev,s.coeffRev,s.tmp,
    s.rightKey,s.leftCopy,s.joinedRev,s.clipKey,s.tCopy,s.jCopy,s.clipTmp]

structure Environment where
  leftKey : List Bool
  tMaster : List Bool
  jMaster : List Bool

def idle (e : Environment) (source output : List Bool) : Store :=
  {source := source, leftKey := e.leftKey, tMaster := e.tMaster,
    jMaster := e.jMaster, output := output}

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

def prepared (e : Environment) (key coeff tail output : List Bool) : Store :=
  {idle e tail output with rightKey := key, leftCopy := e.leftKey, coeffRev := coeff.reverse}

def joined (e : Environment) (key coeff tail output : List Bool) : Store :=
  {idle e tail output with joinedRev := key.reverse, coeffRev := coeff.reverse}

def clipReady (e : Environment) (key coeff tail output : List Bool) : Store :=
  {joined e key coeff tail output with clipKey := key, tCopy := e.tMaster, jCopy := e.jMaster}

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

/-! Public native sparse-key mapper. The instruction table is independent of
the keys, clipping limits, coefficient width, and dictionary length. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeMaskDecode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The fixed-length support-mask encoding and its executable inverse.
Words shorter than n are padded by false; longer words are truncated.
On length-n words these operations are mutually inverse. -/

namespace SubexponentialSAT.SqrtLog.Squarefree

def decodeMask (n : ℕ) (xs : List Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => xs[i.val]?.getD false = true)

@[simp] theorem mem_decodeMask (n : ℕ) (xs : List Bool) (i : Fin n) :
    i ∈ decodeMask n xs ↔ xs[i.val]?.getD false = true := by
  simp [decodeMask]

end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeScaleProgram
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

/-! Moves stage. -/

/-! Emit stage. -/

/-! Native stage. -/

/-! Loop stage. -/

/-! Cost stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

variable {K : Type*}

def keyBits {C : Type*} (key : K → List Bool) : List (K × C) → ℕ
  | [] => 0
  | a :: entries => (key a.1).length + keyBits key entries

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Semantics stage. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_TotalOrderPathDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The same additive bound for ordinary polynomial degree, e.g. the CRT path T. -/
namespace SubexponentialSAT.SqrtLog.TotalOrder

noncomputable section
open scoped BigOperators

variable {R α : Type*} [CommSemiring R]

/-- The U^j coefficient has degree at most a+b*j in the input variables. -/
def PathDegreeBound (a b : ℕ) (P : Polynomial (Polynomial R)) : Prop :=
  ∀ j, (P.coeff j).natDegree ≤ a + b * j

end
end SubexponentialSAT.SqrtLog.TotalOrder

end OAI.Algorithms
end


