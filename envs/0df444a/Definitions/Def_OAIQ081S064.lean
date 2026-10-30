-- Prove2me | Definitions.Def_OAIQ081S064
-- name    : OAIQ081S064
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:49:40.649935+00:00
-- url     : https://prove2.me/theorems/750e3301-73a1-457b-8808-425e2faffb89
-- title:
--   Definitions bundle OAIQ081S064 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 291 declarations of OpenAI's Lean: 203 definitions, 20 inductive types or structures, 3 instances and 65 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandRegisterFrames.baseWrites`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandRegisterFrames.programWrites`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandRegisterFrames.writes`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters.powerTwoProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.BodyTrace`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.CallbackSpec`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.Cursor`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.backed`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.backtrack`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.body`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.descend`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.descended`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.entered`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.finishLevel`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.finished`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.initialized`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.nextOutside`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.popped`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.pruned`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.returned`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.stopped`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.testedOutside`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Floor.logProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Floor.swappedLengthProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCompletedTree.Forest`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCompletedTree.potential`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranch.childA`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranch.childB`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.resultB`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.NegatedCoreProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.NegatedCoreProgram.copied`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.NegatedCoreProgram.copyQuery`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.NegatedCoreProgram.copyQueryProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.NegatedCoreProgram.innerEmit`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.NegatedCoreProgram.innerProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.NegatedCoreProgram.innerResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.NegatedCoreProgram.ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.NegatedCoreProgram.seed` and 183 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_CommandRegisterFrames`, `SubexponentialSAT_SqrtLogSpace_CountDFS`, `SubexponentialSAT_SqrtLogSpace_Counters`, `SubexponentialSAT_SqrtLogSpace_DifferencePairsProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_BinaryClogProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_CountModel`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSCompletedTree`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_NegatedCoreProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseCharging`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseCountProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseFrontierProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriority`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityPrimitives`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseSelectorRefinement`, `SubexponentialSAT_SqrtLogSpace_DisjointSparsify`, `SubexponentialSAT_SqrtLogSpace_DisjointSparsifyProgram`, `SubexponentialSAT_SqrtLogSpace_EncodingBounds`, `SubexponentialSAT_SqrtLogSpace_FactorAssignmentLoop`, `SubexponentialSAT_SqrtLogSpace_FactorAssignmentProgram`, `SubexponentialSAT_SqrtLogSpace_FactorEnvironment`, `SubexponentialSAT_SqrtLogSpace_FactorTableSpace`, `SubexponentialSAT_SqrtLogSpace_FiniteFallback`, `SubexponentialSAT_SqrtLogSpace_HashCandidateProgram`, `SubexponentialSAT_SqrtLogSpace_HashGreedyCNF`, `SubexponentialSAT_SqrtLogSpace_HashGreedyExecution`, `SubexponentialSAT_SqrtLogSpace_HashGreedyRound`, `SubexponentialSAT_SqrtLogSpace_HashMassAdapter`, `SubexponentialSAT_SqrtLogSpace_HashQueryInputBounds`, `SubexponentialSAT_SqrtLogSpace_HashTrialStage`, `SubexponentialSAT_SqrtLogSpace_HeadEvaluation`, `SubexponentialSAT_SqrtLogSpace_HeadSpecializationProgram`, `SubexponentialSAT_SqrtLogSpace_NativeCode`, `SubexponentialSAT_SqrtLogSpace_NativeCodeAssembly`, `SubexponentialSAT_SqrtLogSpace_NativeFrontend`, `SubexponentialSAT_SqrtLogSpace_NativeLayoutLoad`, `SubexponentialSAT_SqrtLogSpace_NativeLeafRun`, `SubexponentialSAT_SqrtLogSpace_NativeOuter`, `SubexponentialSAT_SqrtLogSpace_NativeOuterBudgets`, `SubexponentialSAT_SqrtLogSpace_NativeQueryPreparation`, `SubexponentialSAT_SqrtLogSpace_NativeTerminal`, `SubexponentialSAT_SqrtLogSpace_NodeAppendSpace`, `SubexponentialSAT_SqrtLogSpace_NodeReadoutSpace`, `SubexponentialSAT_SqrtLogSpace_QueryNodeFinish`, `SubexponentialSAT_SqrtLogSpace_QueryProgram`, `SubexponentialSAT_SqrtLogSpace_QueryStreamProgram`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleProgram`, `SubexponentialSAT_SqrtLogSpace_SparseCodeSearch`, `SubexponentialSAT_SqrtLogSpace_TruncatedRingProgram`, `SubexponentialSAT_SubexpChunkRecordMap`, `SubexponentialSAT_SubexpClauseRowProgram`, `SubexponentialSAT_SubexpConvolutionExecution`, `SubexponentialSAT_SubexpConvolutionOuter`, `SubexponentialSAT_SubexpConvolutionRows`, `SubexponentialSAT_SubexpNegatedQueryProgram`, `SubexponentialSAT_SubexpNormalizationCorrectness`, `SubexponentialSAT_SubexpNormalizeProgram`, `SubexponentialSAT_SubexpTautologyFilterProgram`, `SubexponentialSAT_SubexpTautologyProgram`, `SubexponentialSAT_Subexp_GlobalBasisMetadata`, `SubexponentialSAT_Subexp_MatrixAnchorGuardProgram`, `SubexponentialSAT_Subexp_MatrixAnchorReadProgram`, `SubexponentialSAT_Subexp_MatrixAnchorTypes`, `SubexponentialSAT_Subexp_MatrixColorReadProgram`, `SubexponentialSAT_Subexp_MatrixEntryKernel`, `SubexponentialSAT_Subexp_MatrixEntryScalar`, `SubexponentialSAT_Subexp_MatrixInputAccess`, `SubexponentialSAT_Subexp_MatrixInputTypes`, `SubexponentialSAT_Subexp_MatrixPositionProgram`, `SubexponentialSAT_Subexp_MatrixScanProgram`, `SubexponentialSAT_Subexp_MatrixScanSemantics`, `SubexponentialSAT_Subexp_MatrixScanStepProgram`, `SubexponentialSAT_Subexp_MatrixSupport`, `SubexponentialSAT_Subexp_MismatchPlanProgram`, `SubexponentialSAT_Subexp_UniversalRowGather`, `SubexponentialSAT_Subexp_UniversalRowGuard`, `SubexponentialSAT_Subexp_UniversalRowMismatchProgram`, `SubexponentialSAT_Subexp_UniversalRowMismatchTypes`, `SubexponentialSAT_Subexp_UniversalRowSource`, `SubexponentialSAT_Subexp_UniversalRowTermFraming`, `SubexponentialSAT_SunflowerBranch`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S023`, `OAIQ081S024`, `OAIQ081S025`, `OAIQ081S026`, `OAIQ081S028`, `OAIQ081S029`, `OAIQ081S030`, `OAIQ081S031`, `OAIQ081S032`, `OAIQ081S035`, `OAIQ081S036`, `OAIQ081S037`, `OAIQ081S039`, `OAIQ081S040`, `OAIQ081S042` and `OAIQ081S043` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S081` and `OAIQ081S098`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsSpace.program_stack_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCompletedTree.completed_visits_reciprocal`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSNative.remaining_bytes_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.resultB_length_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.canonical_normalized_body_length`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBankFrame.lookup_lifted`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.row_meaning`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.scanCounts_bounds_of_anchor`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.scanFormula_eq_scalarEntry`, `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationCorrectness.normalizedBody_length_le` and `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchTypes.filter_eval`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCompletedTree.completed_visits_reciprocal`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSNative.remaining_bytes_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.canonical_normalized_body_length`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm.scalarEntry_cast`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.scanCounts_bounds_of_anchor` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.scanFormula_eq_scalarEntry`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S023
import Definitions.Def_OAIQ081S024
import Definitions.Def_OAIQ081S025
import Definitions.Def_OAIQ081S026
import Definitions.Def_OAIQ081S028
import Definitions.Def_OAIQ081S029
import Definitions.Def_OAIQ081S030
import Definitions.Def_OAIQ081S031
import Definitions.Def_OAIQ081S032
import Definitions.Def_OAIQ081S035
import Definitions.Def_OAIQ081S036
import Definitions.Def_OAIQ081S037
import Definitions.Def_OAIQ081S039
import Definitions.Def_OAIQ081S040
import Definitions.Def_OAIQ081S042
import Definitions.Def_OAIQ081S043

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CommandRegisterFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Register frames derived from the actual finite instruction tables and
structured command syntax. These footprints describe code, not an assumed
semantic behavior of a callback. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandRegisterFrames

open OAI BitProgram ProgramLogic

/-- All register destinations in a concrete finite instruction table. -/
def programWrites {r s l : ℕ} (p : Program r s l) : Finset (Fin r) :=
  Finset.univ.biUnion (fun label => registerWrites (p.code label))

@[simp] theorem mem_programWrites {r s l : ℕ} (p : Program r s l) (i : Fin r) :
    i ∈ programWrites p ↔ ∃ label, i ∈ registerWrites (p.code label) := by
  simp [programWrites]

/-- Base-command footprint uses the original concrete instruction for atoms. -/
def baseWrites {r s : ℕ} : StructuredProgram.Cmd r s → Finset (Fin r)
  | .skip => ∅
  | .atom atom => registerWrites (atom.instr (0 : Fin 1))
  | .seq first second => baseWrites first ∪ baseWrites second
  | .ite _ yes no => baseWrites yes ∪ baseWrites no
  | .while _ body => baseWrites body

/-- Calls contribute their actual finite table; guards only read registers. -/
def writes {r s : ℕ} : StructuredCalls.Cmd r s → Finset (Fin r)
  | .base c => baseWrites c
  | .call p => programWrites p
  | .seq first second => writes first ∪ writes second
  | .ite _ yes no => writes yes ∪ writes no
  | .while _ body => writes body

@[simp] theorem not_mem_programWrites {r s l : ℕ} (p : Program r s l) (i : Fin r) :
    i ∉ programWrites p ↔ ∀ label, i ∉ registerWrites (p.code label) := by
  simp only [mem_programWrites, not_exists]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandRegisterFrames
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

theorem antichain_absorb (F : CNF V) : Antichain (absorb F) := by
  intro C hC D hD hCD
  exact absorb_antichain hD hC hCD

end SubexponentialSAT.SunflowerBranch

namespace SubexponentialSAT.SunflowerBranch

open SubexponentialSAT.SAT
universe u
variable {V : Type u} [DecidableEq V]

omit [DecidableEq V] in
/-- Tautology-freeness is inherited by every subclause. -/
theorem not_tautology_of_subset {C D : Clause V} (hCD : C ⊆ D)
    (hD : ¬ D.IsTautology) : ¬ C.IsTautology := by
  rintro ⟨l, hl, hn⟩
  exact hD ⟨l, hCD hl, hCD hn⟩

end SubexponentialSAT.SunflowerBranch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_CountModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Data for the exact-counting statement, corresponding to source lines 45–77.
The primitive execution and space obligations are separate from these data definitions. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse

/-- Raw clauses retain order and repetitions on all declared variables. -/
abbrev RawCNF (n : ℕ) := ExecCNF.Formula (SAT.Literal (Fin n))

/-- Count every assignment on the declared ambient variable type. -/
def rawCount {n : ℕ} (F : RawCNF n) : ℕ := SAT.count (ExecCNF.formulaSet F)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse
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

def childA (F : CNF V) (c : ℕ) (H : Clause V) : CNF V :=
  absorb (insert H (F \ selected F c H))

def childB (F : CNF V) (c : ℕ) (H : Clause V) : CNF V :=
  absorb (((F \ selected F c H) ∪ petals F c H) ∪ negatedCoreUnits H)

theorem core_mem_childA {F : CNF V} {c : ℕ} {H : Clause V}
    (hF : SunflowerBranch.Antichain F) (hsel : (selected F c H).Nonempty)
    (hproper : H.card < c) : H ∈ childA F c H := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_insert_self _ _, ?_⟩
  rintro ⟨E, hE, hEH⟩
  rcases Finset.mem_insert.mp hE with rfl | hE
  · exact (Finset.ssubset_iff_subset_ne.mp hEH).2 rfl
  · exact no_old_subset_core hF hsel hproper (Finset.mem_sdiff.mp hE).1
      (Finset.ssubset_iff_subset_ne.mp hEH).1

theorem unit_not_subset_petal {F : CNF V} {c : ℕ} {H P U : Clause V}
    (hnt : ∀ C ∈ F, ¬ C.IsTautology) (hP : P ∈ petals F c H)
    (hU : U ∈ negatedCoreUnits H) : ¬ U ⊆ P := by
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hU
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hP
  intro hsub
  apply hnt C (selected_subset F c H hC)
  exact ⟨l, (mem_selected.mp hC).2.2 hl,
    (Finset.mem_sdiff.mp (hsub (Finset.mem_singleton_self _))).1⟩

theorem petals_subset_childB {F : CNF V} {c : ℕ} {H : Clause V}
    (hF : SunflowerBranch.Antichain F) (hH : H.Nonempty)
    (hnt : ∀ C ∈ F, ¬ C.IsTautology) : petals F c H ⊆ childB F c H := by
  intro P hP
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_union_left _ (Finset.mem_union_right _ hP), ?_⟩
  rintro ⟨E, hE, hEP⟩
  obtain ⟨hEPsub, hEPne⟩ := Finset.ssubset_iff_subset_ne.mp hEP
  rcases Finset.mem_union.mp hE with hE | hE
  · rcases Finset.mem_union.mp hE with hE | hE
    · exact no_old_subset_petal hF hH hP (Finset.mem_sdiff.mp hE).1 hEPsub
    · exact hEPne (Finset.eq_of_subset_of_card_le hEPsub
        (by rw [petal_card hP, petal_card hE]))
  · exact unit_not_subset_petal hnt hP hE hEPsub

theorem units_subset_childB {F : CNF V} {c : ℕ} {H : Clause V}
    (hF : SunflowerBranch.Antichain F) (hsel : (selected F c H).Nonempty)
    (hproper : H.card < c) : negatedCoreUnits H ⊆ childB F c H := by
  intro U hU
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_union_right _ hU, ?_⟩
  rintro ⟨E, hE, hEU⟩
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hU
  have hne := rawB_clause_nonempty hF hsel hproper hE
  rw [Finset.eq_empty_of_ssubset_singleton hEU] at hne
  exact Finset.not_nonempty_empty hne

theorem insertedB_subset_childB {F : CNF V} {c : ℕ} {H : Clause V}
    (hF : SunflowerBranch.Antichain F) (hsel : (selected F c H).Nonempty)
    (hH : H.Nonempty) (hproper : H.card < c)
    (hnt : ∀ C ∈ F, ¬ C.IsTautology) : insertedB F c H ⊆ childB F c H := by
  intro C hC
  rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hC).1 with hC | hC
  · exact petals_subset_childB hF hH hnt hC
  · exact units_subset_childB hF hsel hproper hC

theorem childA_subset (F : CNF V) (c : ℕ) (H : Clause V) :
    childA F c H ⊆ F ∪ {H} := by
  intro C hC
  rcases Finset.mem_insert.mp (absorb_subset _ hC) with rfl | hC
  · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hC).1

theorem childB_subset (F : CNF V) (c : ℕ) (H : Clause V) :
    childB F c H ⊆ F ∪ insertedB F c H := by
  intro C hC
  by_cases hCF : C ∈ F
  · exact Finset.mem_union_left _ hCF
  · apply Finset.mem_union_right
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, hCF⟩
    rcases Finset.mem_union.mp (absorb_subset _ hC) with hC | hC
    · rcases Finset.mem_union.mp hC with hC | hC
      · exact False.elim (hCF (Finset.mem_sdiff.mp hC).1)
      · exact Finset.mem_union_left _ hC
    · exact Finset.mem_union_right _ hC

theorem removed_childA_contains_core {F : CNF V} {c : ℕ} {H C : Clause V}
    (hF : SunflowerBranch.Antichain F) (hproper : H.card < c)
    (hC : C ∈ F) (hremoved : C ∉ childA F c H) : H ⊂ C := by
  by_cases hsel : C ∈ selected F c H
  · exact core_strict_subset hsel hproper
  · have hraw : C ∈ insert H (F \ selected F c H) :=
      Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hC, hsel⟩)
    have hex : ∃ E ∈ insert H (F \ selected F c H), E ⊂ C := by
      by_contra h
      exact hremoved (Finset.mem_filter.mpr ⟨hraw, h⟩)
    obtain ⟨E, hE, hEC⟩ := hex
    rcases Finset.mem_insert.mp hE with rfl | hE
    · exact hEC
    · exact False.elim ((Finset.ssubset_iff_subset_ne.mp hEC).2
        (hF E (Finset.mem_sdiff.mp hE).1 C hC
          (Finset.ssubset_iff_subset_ne.mp hEC).1))

theorem removed_childB_contains_inserted {F : CNF V} {c : ℕ} {H C : Clause V}
    (hF : SunflowerBranch.Antichain F) (hH : H.Nonempty)
    (hC : C ∈ F) (hremoved : C ∉ childB F c H) :
    ∃ P ∈ insertedB F c H, P ⊂ C := by
  by_cases hsel : C ∈ selected F c H
  · exact ⟨C \ H, petals_subset_insertedB hF hH
      (Finset.mem_image.mpr ⟨C, hsel, rfl⟩), petal_strict_subset hsel hH⟩
  · have hraw : C ∈ ((F \ selected F c H) ∪ petals F c H) ∪ negatedCoreUnits H :=
      Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hC, hsel⟩))
    have hex : ∃ E ∈ ((F \ selected F c H) ∪ petals F c H) ∪ negatedCoreUnits H,
        E ⊂ C := by
      by_contra h
      exact hremoved (Finset.mem_filter.mpr ⟨hraw, h⟩)
    obtain ⟨E, hE, hEC⟩ := hex
    have hEF : E ∉ F := by
      intro hEF
      exact (Finset.ssubset_iff_subset_ne.mp hEC).2
        (hF E hEF C hC (Finset.ssubset_iff_subset_ne.mp hEC).1)
    refine ⟨E, Finset.mem_sdiff.mpr ⟨?_, hEF⟩, hEC⟩
    rcases Finset.mem_union.mp hE with hE | hE
    · rcases Finset.mem_union.mp hE with hE | hE
      · exact False.elim (hEF (Finset.mem_sdiff.mp hE).1)
      · exact Finset.mem_union_left _ hE
    · exact Finset.mem_union_right _ hE

theorem childA_antichain (F : CNF V) (c : ℕ) (H : Clause V) :
    SunflowerBranch.Antichain (childA F c H) := SunflowerBranch.antichain_absorb _

theorem childB_antichain (F : CNF V) (c : ℕ) (H : Clause V) :
    SunflowerBranch.Antichain (childB F c H) := SunflowerBranch.antichain_absorb _

theorem childA_not_tautological {F : CNF V} {c : ℕ} {H : Clause V}
    (hnt : ∀ C ∈ F, ¬ C.IsTautology) (hsel : (selected F c H).Nonempty) :
    ∀ C ∈ childA F c H, ¬ C.IsTautology := by
  intro C hC
  rcases Finset.mem_insert.mp (absorb_subset _ hC) with hCH | hC
  · subst C
    obtain ⟨D, hD⟩ := hsel
    exact SunflowerBranch.not_tautology_of_subset (mem_selected.mp hD).2.2
      (hnt D (selected_subset F c H hD))
  · exact hnt C (Finset.mem_sdiff.mp hC).1

theorem childB_not_tautological {F : CNF V} {c : ℕ} {H : Clause V}
    (hnt : ∀ C ∈ F, ¬ C.IsTautology) :
    ∀ C ∈ childB F c H, ¬ C.IsTautology := by
  intro C hC
  rcases Finset.mem_union.mp (absorb_subset _ hC) with hC | hC
  · rcases Finset.mem_union.mp hC with hC | hC
    · exact hnt C (Finset.mem_sdiff.mp hC).1
    · obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
      exact SunflowerBranch.not_tautology_of_subset Finset.sdiff_subset
        (hnt D (selected_subset F c H hD))
  · obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hC
    rintro ⟨a, ha, hna⟩
    have ha' := Finset.mem_singleton.mp ha
    have hna' := Finset.mem_singleton.mp hna
    have h := congrArg Literal.positive (ha' ▸ hna')
    cases l with
    | mk v p => cases p <;> cases h

theorem childA_widthAtMost {F : CNF V} {c k : ℕ} {H : Clause V}
    (hwidth : WidthAtMost k F) (hsel : (selected F c H).Nonempty)
    (hproper : H.card < c) : WidthAtMost k (childA F c H) := by
  intro C hC
  rcases Finset.mem_union.mp (childA_subset F c H hC) with hC | hC
  · exact hwidth C hC
  · have hCH := Finset.mem_singleton.mp hC
    obtain ⟨D, hD⟩ := hsel
    have hck : c ≤ k := (mem_selected.mp hD).2.1 ▸ hwidth D (selected_subset F c H hD)
    rw [hCH]
    exact hproper.le.trans hck

theorem childB_widthAtMost {F : CNF V} {c k : ℕ} {H : Clause V}
    (hwidth : WidthAtMost k F) (hsel : (selected F c H).Nonempty)
    (hH : H.Nonempty) (hproper : H.card < c) : WidthAtMost k (childB F c H) := by
  intro C hC
  rcases Finset.mem_union.mp (childB_subset F c H hC) with hC | hC
  · exact hwidth C hC
  · obtain ⟨D, hD⟩ := hsel
    have hck : c ≤ k := (mem_selected.mp hD).2.1 ▸ hwidth D (selected_subset F c H hD)
    exact (insertedB_width_lt hH hproper hC).le.trans hck

open scoped BigOperators

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranch
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriority
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Appendix A: smallest-width, largest-core selection and marked degrees. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriority

open OAI.Algorithms.SubexponentialSAT.SAT DisjointBranch
open scoped BigOperators

variable {n : ℕ}

/-- Number of width-`c` clauses containing a literal core. -/
def degree {V : Type*} [DecidableEq V] (F : CNF V) (c : ℕ) (H : Clause V) : ℕ :=
  (selected F c H).card

def orderedClauses (F : CNF (Fin n)) : List (Clause (Fin n)) :=
  let r := fun C D : Clause (Fin n) => Encoding.clauseNumbers C ≤ Encoding.clauseNumbers D
  letI : IsTrans _ r := ⟨fun _ _ _ => le_trans⟩
  letI : Std.Total r := ⟨fun _ _ => le_total _ _⟩
  letI : Std.Antisymm r :=
    ⟨fun _ _ h h' => Encoding.clauseNumbers_injective (le_antisymm h h')⟩
  F.sort r

@[simp] theorem mem_orderedClauses (F : CNF (Fin n)) (C : Clause (Fin n)) :
    C ∈ orderedClauses F ↔ C ∈ F := by simp [orderedClauses]

@[simp] theorem length_orderedClauses (F : CNF (Fin n)) :
    (orderedClauses F).length = F.card := by simp [orderedClauses]

/-- Enumerate clause/core pairs, never tuples of parameter-dependent size. -/
def candidates (F : CNF (Fin n)) : List (ℕ × Clause (Fin n)) :=
  (orderedClauses F).flatMap fun C =>
    (orderedClauses C.powerset).map fun H => (C.card, H)

@[simp] theorem mem_candidates (F : CNF (Fin n)) (c : ℕ) (H : Clause (Fin n)) :
    (c, H) ∈ candidates F ↔ ∃ C ∈ F, C.card = c ∧ H ⊆ C := by
  simp only [candidates, List.mem_flatMap, List.mem_map, mem_orderedClauses,
    Finset.mem_powerset, Prod.mk.injEq]
  constructor
  · rintro ⟨C, hC, K, hK, hcard, rfl⟩
    exact ⟨C, hC, hcard, hK⟩
  · rintro ⟨C, hC, hcard, hH⟩
    exact ⟨C, hC, H, hH, hcard, rfl⟩

/-- The threshold is tested by exact natural arithmetic. -/
def violatingCandidates (F : CNF (Fin n)) (M : ℕ) : List (ℕ × Clause (Fin n)) :=
  (candidates F).filter fun p =>
    decide (0 < p.2.card ∧ p.2.card < p.1 ∧ M ^ (p.1 - p.2.card) ≤ degree F p.1 p.2)

/-- The lexicographic key orders smaller widths first and larger cores first. -/
def select (F : CNF (Fin n)) (M : ℕ) : Option (ℕ × Clause (Fin n)) :=
  (violatingCandidates F M).argmin fun p =>
    (toLex (p.1, OrderDual.toDual p.2.card) : ℕ ×ₗ ℕᵒᵈ)

@[simp] theorem mem_violatingCandidates (F : CNF (Fin n)) (M c : ℕ)
    (H : Clause (Fin n)) :
    (c, H) ∈ violatingCandidates F M ↔
      (∃ C ∈ F, C.card = c ∧ H ⊆ C) ∧ 0 < H.card ∧ H.card < c ∧
        M ^ (c - H.card) ≤ degree F c H := by
  simp [violatingCandidates]

/-- The local consequences of the source priority, independent of deterministic tie order. -/
structure Priority (F : CNF (Fin n)) (M c : ℕ) (H : Clause (Fin n)) : Prop where
  exists_clause : ∃ C ∈ F, C.card = c ∧ H ⊆ C
  core_nonempty : 0 < H.card
  core_proper : H.card < c
  threshold : M ^ (c - H.card) ≤ degree F c H
  minimum : ∀ {j : ℕ} (S : Clause (Fin n)), 0 < S.card → S.card < j → j < c →
    degree F j S < M ^ (j - S.card)
  maximum : ∀ S : Clause (Fin n), H.card < S.card → S.card < c →
    degree F c S < M ^ (c - S.card)

theorem Priority.spec {F : CNF (Fin n)} {M c : ℕ} {H : Clause (Fin n)}
    (h : Priority F M c H) :
    (∃ C ∈ F, C.card = c ∧ H ⊆ C) ∧ 0 < H.card ∧ H.card < c ∧
      M ^ (c - H.card) ≤ degree F c H :=
  ⟨h.exists_clause, h.core_nonempty, h.core_proper, h.threshold⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriority
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseCharging
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Appendix A, insertion recurrence and the resulting path budgets. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCharging

open scoped BigOperators

section SelectedTrace

open RemovalCharging DisjointBranch

variable {n T : ℕ}

theorem path_invariants (F : ℕ → SAT.CNF (Fin n)) (c : ℕ → ℕ)
    (H : ℕ → SAT.Clause (Fin n)) (b : ℕ → Bool) (M k : ℕ)
    (hselect : ∀ t < T, SparsePriority.Priority (F t) M (c t) (H t))
    (hnext : ∀ t < T, F (t + 1) =
      if b t then childB (F t) (c t) (H t) else childA (F t) (c t) (H t))
    (hanti : SunflowerBranch.Antichain (F 0))
    (hnt : ∀ C ∈ F 0, ¬ C.IsTautology) (hwidth : SAT.WidthAtMost k (F 0)) :
    ∀ t ≤ T, SunflowerBranch.Antichain (F t) ∧
      (∀ C ∈ F t, ¬ C.IsTautology) ∧ SAT.WidthAtMost k (F t) := by
  intro t ht
  induction t with
  | zero => exact ⟨hanti, hnt, hwidth⟩
  | succ t ih =>
    have htT : t < T := by omega
    obtain ⟨_, hn, hw⟩ := ih (by omega)
    have hs := (hselect t htT).spec
    have hsel : (selected (F t) (c t) (H t)).Nonempty := by
      obtain ⟨C, hCF, hCc, hHC⟩ := hs.1
      exact ⟨C, mem_selected.mpr ⟨hCF, hCc, hHC⟩⟩
    rw [hnext t htT]
    cases hb : b t
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨childA_antichain _ _ _, childA_not_tautological hn hsel,
        childA_widthAtMost hw hsel hs.2.2.1⟩
    · simp only [↓reduceIte]
      exact ⟨childB_antichain _ _ _, childB_not_tautological hn,
        childB_widthAtMost hw hsel (Finset.card_pos.mp hs.2.1) hs.2.2.1⟩

/-- The concrete replacement trace induced by a selected formula path. -/
def selectedTrace (F : ℕ → SAT.CNF (Fin n)) (c : ℕ → ℕ)
    (H : ℕ → SAT.Clause (Fin n)) (b : ℕ → Bool) (M k : ℕ)
    (hselect : ∀ t < T, SparsePriority.Priority (F t) M (c t) (H t))
    (hnext : ∀ t < T, F (t + 1) =
      if b t then childB (F t) (c t) (H t) else childA (F t) (c t) (H t))
    (hanti : SunflowerBranch.Antichain (F 0))
    (hnt : ∀ C ∈ F 0, ¬ C.IsTautology) (hwidth : SAT.WidthAtMost k (F 0)) :
    Trace (SAT.Literal (Fin n)) T where
  formula := F
  inserted := fun t => if b t then insertedB (F t) (c t) (H t) else {H t}
  next_subset := by
    intro t ht
    rw [hnext t ht]
    cases hb : b t <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact childA_subset _ _ _
    · exact childB_subset _ _ _
  inserted_live := by
    intro t ht
    have hinv := path_invariants F c H b M k hselect hnext hanti hnt hwidth t (by omega)
    have hs := (hselect t ht).spec
    have hsel : (selected (F t) (c t) (H t)).Nonempty := by
      obtain ⟨C, hCF, hCc, hHC⟩ := hs.1
      exact ⟨C, mem_selected.mpr ⟨hCF, hCc, hHC⟩⟩
    rw [hnext t ht]
    cases hb : b t <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact Finset.singleton_subset_iff.mpr (core_mem_childA hinv.1 hsel hs.2.2.1)
    · exact insertedB_subset_childB hinv.1 hsel (Finset.card_pos.mp hs.2.1)
        hs.2.2.1 hinv.2.1
  fresh := by
    intro t ht
    have hinv := path_invariants F c H b M k hselect hnext hanti hnt hwidth t (by omega)
    have hs := (hselect t ht).spec
    cases hb : b t <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · apply Finset.disjoint_singleton_right.mpr
      apply core_new hinv.1 _ hs.2.2.1
      obtain ⟨C, hCF, hCc, hHC⟩ := hs.1
      exact ⟨C, mem_selected.mpr ⟨hCF, hCc, hHC⟩⟩
    · exact insertedB_disjoint _ _ _
  inserted_nonempty := by
    intro t ht Q hQ
    have hs := (hselect t ht).spec
    cases hb : b t <;> simp only [hb, Bool.false_eq_true, ↓reduceIte] at hQ
    · have hQH := Finset.mem_singleton.mp hQ
      rw [hQH]
      exact Finset.card_pos.mp hs.2.1
    · exact insertedB_nonempty hs.2.2.1 hQ
  removed_subset := by
    intro t ht C hC hgone
    have hinv := path_invariants F c H b M k hselect hnext hanti hnt hwidth t (by omega)
    have hs := (hselect t ht).spec
    rw [hnext t ht] at hgone
    cases hb : b t <;> simp only [hb, Bool.false_eq_true, ↓reduceIte] at hgone ⊢
    · exact ⟨H t, Finset.mem_singleton_self _,
        removed_childA_contains_core hinv.1 hs.2.2.1 hC hgone⟩
    · exact removed_childB_contains_inserted hinv.1 (Finset.card_pos.mp hs.2.1) hC hgone

inductive SelectedPath (M : ℕ) : SAT.CNF (Fin n) → List Bool → SAT.CNF (Fin n) → Prop
  | nil (F : SAT.CNF (Fin n)) : SelectedPath M F [] F
  | step {F G : SAT.CNF (Fin n)} {p : List Bool} {c : ℕ} {H : SAT.Clause (Fin n)}
      (b : Bool) (hselect : SparsePriority.Priority F M c H)
      (tail : SelectedPath M (if b then childB F c H else childA F c H) p G) :
      SelectedPath M F (b :: p) G

end SelectedTrace

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCharging
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete syntax routines for CNF normalization

This module begins the machine implementation of normalization with the
complement-query operation used in tautology testing. `negateProgram` is one
fixed finite instruction table. It scans a unary literal code in pairs and
emits the code with its polarity flipped. Unbounded data stays on the stacks.

The theorems count actual `BitProgram.step` transitions. Full formula
deduplication, tautology filtering, and absorption are separate obligations;
this routine is not presented as the completed normalization algorithm.
-/

namespace SubexponentialSAT.SubexpNormalizeProgram

open BitProgram
open ParserProgram (cfg)

/-- A unary code `2*v+b` is transformed into `2*v+(1-b)`. Stack 0 is
input, stack 1 is output, and both Boolean registers are cleared on return.
The output accumulator is preserved as a suffix. -/
abbrev negateProgram : Program 2 2 15 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code q := match q.val with
    | 0 => .set 0 false 1
    | 1 => .push 1 0 2
    | 2 => .pop 0 0 1 3
    | 3 => .branch 1 4 12
    | 4 => .branch 0 5 10
    | 5 => .pop 0 0 1 6
    | 6 => .branch 1 7 12
    | 7 => .branch 0 8 12
    | 8 => .push 1 0 9
    | 9 => .push 1 0 2
    | 10 => .set 0 true 11
    | 11 => .push 1 0 12
    | 12 => .set 0 false 13
    | 13 => .set 1 false 14
    | _ => .halt

/-! ## Actual record-filter output step

The predicate's result occupies register 2. The following fixed callback
consumes the reversed record on stack 3, prepends its framed representation to
stack 2 exactly when selected, and resets the iterator's flags. Its two other
stacks are preserved. Computing the selection bit is a separate operation.
-/

/-! ## A complete record-order reversal pass

Prepending accepted records reverses their order. This second, unconditional
pass restores the order required by `List.filter` and the executable
sparsifier. It reverses the records, never the bits within a record.
-/

/-! ## Exact-order contract for the full normalization filter

The selection callback in the following theorem is a fixed structured
program with measured executions. No procedure is manufactured from the
mathematical predicate. Once that callback is supplied, the theorem tracks
the output of the actual generic record iterator, including record order.
-/

end SubexponentialSAT.SubexpNormalizeProgram

end OAI.Algorithms
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

/-- Consume the current forward body and prepend its escaped record. -/
def push : Cmd 3 4 :=
  .seq (transfer 0 3) (.call SubexpNormalizeProgram.emitRecordProgram)

/-- Initialize the one-root frontier with its physical empty-list sentinel. -/
def initFrontier : Cmd 3 4 :=
  .seq (.base (.seq (.atom (.set 0 false)) (.atom (.push 2 0)))) push

def readerPorts : RecordPrograms.Ports 3 4 :=
  ⟨0, 1, 2, 2, 3, by decide, by decide, by decide, by decide⟩

/-- The head is known to exist: remove its list tag, parse its frame, then
restore forward order on the empty current-body port. -/
def pop : Cmd 3 4 :=
  .seq (.base (.atom (.pop 2 0 1)))
    (.seq (RecordPrograms.reader readerPorts) (transfer 3 0))

/-- A public pop operation tests the sentinel itself. Empty work is a no-op
on every stack, rather than a removal of the final delimiter. -/
def popIfPresent : Cmd 3 4 := .seq test (.ite 2 pop (.base .skip))

def initFrontierProgram : Program 3 4 (size initFrontier + 1) := compiled initFrontier 0 2

def popIfPresentProgram : Program 3 4 (size popIfPresent + 1) := compiled popIfPresent 2 0

/-- The splitter may already return framed children. This fixed command
consumes B then A and never touches the saved declared-variable word. -/
def pushPair : Cmd 4 5 :=
  .seq (.call (ExecWorklistProgram.copyAt 3 0))
    (.call (ExecWorklistProgram.copyAt 2 0))

def pushPairProgram : Program 4 5 (size pushPair + 1) := compiled pushPair 2 0

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseFrontierProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseCountProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

open SAT DisjointBranch
open scoped BigOperators

variable {n : ℕ}

structure Entry (n : ℕ) where
  formula : CNF (Fin n)
  depth : ℕ

structure State (n : ℕ) where
  pending : List (Entry n)
  total : ℕ

def initial (F : CNF (Fin n)) : State n := ⟨[⟨F, 0⟩], 0⟩

def mass (s : State n) : ℕ :=
  s.total + (s.pending.map fun e => count e.formula).sum

@[simp] theorem mass_initial (F : CNF (Fin n)) : mass (initial F) = count F := by
  simp [mass, initial]

/-- The count/frontier invariant does not depend on tie breaking. A physical
selector must separately certify sparsity and the sharp priority conditions. -/
inductive Transition : State n → State n → Prop
  | idle (total : ℕ) : Transition ⟨[], total⟩ ⟨[], total⟩
  | leaf (node : Entry n) (rest : List (Entry n)) (total : ℕ) :
      Transition ⟨node :: rest, total⟩ ⟨rest, total + count node.formula⟩
  | branch (node : Entry n) (rest : List (Entry n)) (total c : ℕ) (H : Clause (Fin n)) :
      Transition ⟨node :: rest, total⟩
        ⟨⟨childA node.formula c H, node.depth + 1⟩ ::
          ⟨childB node.formula c H, node.depth + 1⟩ :: rest, total⟩

inductive Transitions : ℕ → State n → State n → Prop
  | refl (s : State n) : Transitions 0 s s
  | cons {s u t : State n} {steps : ℕ} : Transition s u →
      Transitions steps u t → Transitions (steps + 1) s t

def potential (s : State n) : ℕ :=
  (s.pending.map fun e => 3 ^ SunflowerBranch.literalMass e.formula).sum

/-- The physical serialized search may use any fixed tie order satisfying the
source priority. This proof-only tree imposes no runtime storage obligation. -/
inductive PriorityDerivation (M : ℕ) : CNF (Fin n) → BranchTree.Tree → Prop
  | leaf {F} : SparsePriority.select F M = none → PriorityDerivation M F .leaf
  | branch {F c H A B} : SparsePriority.Priority F M c H →
      PriorityDerivation M (childA F c H) A → PriorityDerivation M (childB F c H) B →
      PriorityDerivation M F (.branch A B)

/-- After the current node, sibling depths decrease strictly. -/
inductive Ordered : List (Entry n) → Prop
  | nil : Ordered []
  | cons (head : Entry n) (tail : List (Entry n))
      (strict : tail.Pairwise (fun a b => b.depth < a.depth))
      (bound : ∀ e ∈ tail, e.depth ≤ head.depth) : Ordered (head :: tail)

/-- This is the actual callback body encoding, in its retained raw clause order. -/
def encodeBody (F : RawCNF n) : List Bool :=
  Encoding.encodeList (Encoding.encodeList Encoding.encodeNat)
    (F.map (List.map Encoding.literalCode))


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram
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

def clear (port : Fin 9) : Cmd 13 9 := .call (StackRoutines.clearProgram port 0 1)

end Tuple

namespace Count

open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityPrimitives.Tuple
  (copy clear )

def countProgram := ProgramLinking.liftProgram SubexpSunflowerProgram.CountRecords.program
  countReg countStack

def reset : Cmd 13 9 :=
  .seq (RecordPrograms.atom (.set 0 false))
    (.seq (RecordPrograms.atom (.set 1 false)) (RecordPrograms.atom (.set 2 false)))

def numericEq (expected : Fin 2) : Cmd 13 9 :=
  .seq (less 6 (expectedPort expected))
    (.seq (RecordPrograms.atom (.copy 12 0))
      (.seq (less (expectedPort expected) 6)
        (.seq (RecordPrograms.atom (.bor 4 12 0)) (RecordPrograms.atom (.bnot 4 4)))))

end Count

namespace FrameWriter

def cfg4 {l : ℕ} (pc : Option (Fin l)) (value present operation : Bool)
    (code depth operands scratch : List Bool) : Cfg 3 4 l :=
  ⟨pc, triple value present operation, quadruple code depth operands scratch⟩

/-- The first seven labels are the actual relocated frame parser. The remaining
labels rebuild the escaped payload from its reverse and add the list cons tag. -/
def literalService : Program 3 4 17 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code := Fin.addCases (motive := fun _ : Fin (7 + 10) => Instr 3 4 17)
    (fun pc : Fin 7 => ProgramLinking.relocateInstr parserRegister parserStack parserLabel
      (some 7) (ParserProgram.frameProgram.code pc))
    (fun pc : Fin 10 => match pc.val with
      | 0 => .set 0 false 8
      | 1 => .push 2 0 9
      | 2 => .pop 3 0 1 10
      | 3 => .branch 1 11 14
      | 4 => .push 2 0 12
      | 5 => .set 0 true 13
      | 6 => .push 2 0 9
      | 7 => .set 0 true 15
      | 8 => .push 2 0 16
      | _ => .halt)

@[simp] theorem literalService_code7 : literalService.code 7 = .set 0 false 8 := rfl
@[simp] theorem literalService_code8 : literalService.code 8 = .push 2 0 9 := rfl
@[simp] theorem literalService_code9 : literalService.code 9 = .pop 3 0 1 10 := rfl
@[simp] theorem literalService_code10 : literalService.code 10 = .branch 1 11 14 := rfl
@[simp] theorem literalService_code11 : literalService.code 11 = .push 2 0 12 := rfl
@[simp] theorem literalService_code12 : literalService.code 12 = .set 0 true 13 := rfl
@[simp] theorem literalService_code13 : literalService.code 13 = .push 2 0 9 := rfl
@[simp] theorem literalService_code14 : literalService.code 14 = .set 0 true 15 := rfl
@[simp] theorem literalService_code15 : literalService.code 15 = .push 2 0 16 := rfl
@[simp] theorem literalService_code16 : literalService.code 16 = .halt := rfl


end FrameWriter

namespace Filter

def filterState (value present selected : Bool)
    (source work output payload : List Bool) : StructuredProgram.State 3 4 :=
  ⟨FrameWriter.triple value present selected,
    FrameWriter.quadruple source work output payload⟩

/-- Enter the proved frame writer directly at its fixed encoding entry. -/
def emitRecordProgram : Program 3 4 17 :=
  { FrameWriter.literalService with inputStack := 3, entry := 7 }

def discardRecordProgram : Program 3 4 3 := StackRoutines.clearProgram 3 0 1

def emitIfSelected : StructuredCalls.Cmd 3 4 :=
  .seq (.ite 2 (.call emitRecordProgram) (.call discardRecordProgram))
    (.base resetFilterFlags)

def emitIfSelectedProgram := StructuredCalls.compiled emitIfSelected 3 2

@[simp] theorem unread_false (records : List (List Bool)) (suffix : List Bool) :
    RecordPrograms.unread (fun _ => false) records suffix = suffix := by
  induction records with
  | nil => rfl
  | cons bits records ih => simpa [RecordPrograms.unread] using ih

structure FilterEffect {r s : ℕ} (output : Fin s) (keep : List Bool → Bool)
    (bits : List Bool) (before after : StructuredProgram.State r s) : Prop where
  output_eq : after.stacks output =
    if keep bits then true :: (Encoding.frame bits ++ before.stacks output)
    else before.stacks output


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

namespace Filter

def result (F : Formula) (H : Clause) (width : List Bool) : Formula :=
  F.filter fun C => decide (C.length = BinaryArithmetic.toNat width) && ExecCNF.subset H C

@[simp] theorem flags_self (regs : Regs) : flags regs (regs 13) (regs 14) (regs 15) = regs := by
  funext i
  by_cases h13 : i = 13 <;> by_cases h14 : i = 14 <;> by_cases h15 : i = 15 <;>
    simp_all [flags]

def cost (H : Clause) (width bits : List Bool) : ℕ :=
  500 * ((clauseCode H).length + bits.length + width.length + 1) ^ 2


end Filter

namespace Selector

def ports : RecordPrograms.Ports 24 24 where
  tag := 21
  present := 22
  found := 23
  source := 14
  payload := 15
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def parameterInitBound (exponent : ℕ) (size base family : List Bool) : ℕ :=
  (2 * size.length + 1) +
    (PowerPrograms.runtimeBound base exponent.bits + 4 * exponent.bits.length + 4) +
    (7 * family.length + 5)

end Selector

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNegatedQueryProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

open BitProgram StructuredCalls
open ParserProgram (pair)

abbrev copyQuery : Program 2 4 8 := StackRoutines.copyProgram 0 2 3 0 1
abbrev reverseWork : Program 2 4 10 := StackRoutines.reverseProgram 2 1 3 0 1
abbrev reverseResult : Program 2 4 10 := StackRoutines.reverseProgram 1 2 3 0 1

abbrev negateWork : Program 2 4 15 :=
  ProgramLinking.liftProgram SubexpNormalizeProgram.negateProgram id negatePorts

/-- The syntax, register count, stack count, and label count are independent
of the encoded literal's value. -/
abbrev command : Cmd 2 4 :=
  .seq (.call copyQuery)
    (.seq (.call reverseWork) (.seq (.call negateWork) (.call reverseResult)))

abbrev program := compiled command 0 1

end SubexponentialSAT.SubexpNegatedQueryProgram

end OAI.Algorithms
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

def negateQueryProgram := ProgramLinking.liftProgram
  SubexpNegatedQueryProgram.program negateReg negateStack

abbrev negateQuery : Cmd 10 8 := .call negateQueryProgram

/-- The current literal uses stack 7, so stack 4 is the copying scratch port. -/
abbrev copyClauseProgram : Program 10 8 8 := StackRoutines.copyProgram 2 3 4 0 1

abbrev copyClause : Cmd 10 8 := .call copyClauseProgram

def oppositePresent (C : List ℕ) (bits : List Bool) : Bool :=
  match Encoding.readNat bits with
  | none => false
  | some (c, rest) => rest.isEmpty && ExecCNF.contains (SubexpFrontend.negateCode c) C

@[simp] theorem oppositePresent_encodeNat (C : List ℕ) (c : ℕ) :
    oppositePresent C (Encoding.encodeNat c) =
      ExecCNF.contains (SubexpFrontend.negateCode c) C := by
  simp [oppositePresent]

def ports : RecordPrograms.Ports 10 8 where
  tag := 7
  present := 8
  found := 9
  source := 0
  payload := 7
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

/-- Copy the input clause once, before the destructive outer scan. -/
abbrev initializeProgram : Program 10 8 8 := StackRoutines.copyProgram 0 2 4 0 1

abbrev initializeCmd : Cmd 10 8 := .call initializeProgram

end SubexponentialSAT.SubexpTautologyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTautologyFilterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual tautological-clause filtering

The outer record loop runs the checked clause-tautology machine on each clause,
emits exactly the clauses that it rejects as tautologies, and restores their
original list order. The Boolean predicates below specify this concrete code;
they are not instructions available to the machine.
-/

namespace SubexponentialSAT.SubexpTautologyFilterProgram

open BitProgram StructuredCalls

abbrev transferProgram (source target : Fin 11) : Program 13 11 4 :=
  StackRoutines.transferProgram source target 0 1

abbrev transfer (source target : Fin 11) : Cmd 13 11 := .call (transferProgram source target)

abbrev clearProgram (port : Fin 11) : Program 13 11 3 := StackRoutines.clearProgram port 0 1

abbrev clear (port : Fin 11) : Cmd 13 11 := .call (clearProgram port)

def ports : RecordPrograms.Ports 13 11 where
  tag := 10
  present := 11
  found := 12
  source := 0
  payload := 1
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

abbrev pushFalse (stack : Fin 11) : Cmd 13 11 :=
  .seq (RecordPrograms.atom (.set 0 false)) (RecordPrograms.atom (.push stack 0))

end SubexponentialSAT.SubexpTautologyFilterProgram

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

abbrev Data := State 10 8
abbrev ports := ExecLiteralDedupProgram.ports

def units (H : List ℕ) : List (List ℕ) :=
  H.reverse.map fun c => [SubexpFrontend.negateCode c]

def copyQueryProgram : Program 10 8 8 := StackRoutines.copyProgram 1 7 6 0 1
def copyQuery : Cmd 10 8 := .call copyQueryProgram
def copied (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks 1 7 d.stacks⟩

def seed : Cmd 10 8 := .seq (RecordPrograms.atom (.set 0 false))
  (RecordPrograms.atom (.push 3 0))

def seeded (d : Data) : Data :=
  ⟨Function.update d.regs 0 false, Function.update d.stacks 3 (false :: d.stacks 3)⟩

def innerProgram := ProgramLinking.liftProgram SubexpNormalizeProgram.emitRecordProgram
  ExecLiteralDedupProgram.emitReg innerStack
def innerEmit : Cmd 10 8 := .call innerProgram

def innerResult (bits : List Bool) (d : Data) : Data :=
  ⟨Function.update (Function.update d.regs 7 true) 8 false,
    Function.update (Function.update d.stacks 1 []) 3
      (true :: (Encoding.frame bits ++ d.stacks 3))⟩

def transferClauseProgram : Program 10 8 4 := StackRoutines.transferProgram 3 1 0 1
def transferClause : Cmd 10 8 := .call transferClauseProgram
def transferred (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks 3 1 d.stacks⟩

def select : Cmd 10 8 := RecordPrograms.atom (.set 9 true)
def selected (d : Data) : Data := ⟨Function.update d.regs 9 true, d.stacks⟩

def unitCode (bits : List Bool) : List Bool :=
  match Encoding.readNat bits with
  | none => []
  | some (c, _) => clauseCode [SubexpFrontend.negateCode c]

@[simp] theorem unitCode_encodeNat (c : ℕ) :
    unitCode (Encoding.encodeNat c) = clauseCode [SubexpFrontend.negateCode c] := by
  simp [unitCode]

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

/-- Units are inserted before the petal routine's actual absorption pass. -/
def resultB {α : Type*} [DecidableEq α] (negate : α → α)
    (F selected : List (List α)) (H : List α) : List (List α) :=
  ExecPetalChildProgram.result (negatedUnits negate H ++ F) selected H

open BitProgram StructuredCalls

open ExecBranchControllerSupport

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_EncodingBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Canonical count words and the conversion from encoded length to declared input size. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

@[simp] theorem count_empty (n : ℕ) : SAT.count (∅ : SAT.CNF (Fin n)) = 2 ^ n := by
  simp [SAT.count, SAT.satisfyingAssignments, SAT.Assignment]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CountDFS
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

open SAT SparsePriorityProgram BitProgram StructuredCalls

variable {n : ℕ}

structure Node (n : ℕ) where
  formula : RawCNF n
  depth : ℕ

structure Frontier (n : ℕ) where
  pending : List (Node n)
  total : ℕ

def Node.model (node : Node n) : SparseCountProgram.Entry n :=
  ⟨ExecCNF.formulaSet node.formula, node.depth⟩

def Frontier.model (s : Frontier n) : SparseCountProgram.State n :=
  ⟨s.pending.map Node.model, s.total⟩

def pendingBytes (pending : List (Node n)) : List Bool :=
  Encoding.encodeList (fun node => SparseCountProgram.encodeBody node.formula) pending

@[simp] theorem pendingBytes_nil : pendingBytes ([] : List (Node n)) = [false] := rfl

@[simp] theorem pendingBytes_cons (node : Node n) (rest : List (Node n)) :
    pendingBytes (node :: rest) =
      ExecWorklistProgram.record (SparseCountProgram.encodeBody node.formula) ++
        pendingBytes rest := by
  simp [pendingBytes, Encoding.encodeList, ExecWorklistProgram.record]

/-- Normalized syntax invariants are retained even though encountered clause
order differs from the canonical finite-set encoding. -/
structure Valid (k : ℕ) (F : RawCNF n) : Prop where
  literal_nodup : ∀ C ∈ F, C.Nodup
  clause_nodup : (F.map ExecCNF.clauseSet).Nodup
  width : ∀ C ∈ F, C.length ≤ k
  antichain : SunflowerBranch.Antichain (ExecCNF.formulaSet F)
  not_tautological : ∀ C ∈ ExecCNF.formulaSet F, ¬ SAT.Clause.IsTautology C

def childA (F : RawCNF n) (c : ℕ) (H : List (Literal (Fin n))) : RawCNF n :=
  ExecCoreChildProgram.result F (selectedRaw F c H) H

def childB (F : RawCNF n) (c : ℕ) (H : List (Literal (Fin n))) : RawCNF n :=
  DisjointBranchProgram.resultB Literal.negate F (selectedRaw F c H) H

/-- Every raw step names the actual disjoint list outputs. Leaf exact counts
here specify the semantic transition, and do not compute a runtime callback. -/
inductive Transition (k M : ℕ) : Frontier n → Frontier n → Prop
  | leaf (node : Node n) (rest : List (Node n)) (total : ℕ) :
      SparsePriority.select (ExecCNF.formulaSet node.formula) M = none →
      Transition k M ⟨node :: rest, total⟩ ⟨rest, total + rawCount node.formula⟩
  | branch (node : Node n) (rest : List (Node n)) (total c : ℕ)
      (H : List (Literal (Fin n))) : Valid k node.formula →
      RawPriority k node.formula M c H →
      Transition k M ⟨node :: rest, total⟩
        ⟨⟨childA node.formula c H, node.depth + 1⟩ ::
          ⟨childB node.formula c H, node.depth + 1⟩ :: rest, total⟩

inductive Transitions (k M : ℕ) : ℕ → Frontier n → Frontier n → Prop
  | refl (s : Frontier n) : Transitions k M 0 s s
  | cons {s t u : Frontier n} {visits : ℕ} : Transition k M s t →
      Transitions k M visits t u → Transitions k M (visits + 1) s u

/-- This proof-only tree follows the actual encountered-order children. -/
inductive Derivation (k M : ℕ) : RawCNF n → BranchTree.Tree → Prop
  | leaf {F} : SparsePriority.select (ExecCNF.formulaSet F) M = none → Derivation k M F .leaf
  | branch {F c H A B} : Valid k F → RawPriority k F M c H →
      Derivation k M (childA F c H) A → Derivation k M (childB F c H) B →
      Derivation k M F (.branch A B)

open SparseDFSProgram

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_Counters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters

open BitProgram CounterPrograms CounterForPrograms

/-- Consume a length witness and construct the binary fuel `2^h` by pushing
one zero per witness bit. The finite control never stores `h` or `2^h`. -/
def powerTwoProgram : Program 3 2 7 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code q := match q.val with
    | 0 => .set 0 true 1
    | 1 => .push 1 0 2
    | 2 => .pop 0 0 1 3
    | 3 => .branch 1 4 6
    | 4 => .set 0 false 5
    | 5 => .push 1 0 2
    | _ => .halt

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters
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

def entered (p : Ports r s) (e u : Bool) (d : State r s) : State r s :=
  (Atom.set (p.register 0) true).eval (pushed p 3 u (pushed p 2 e d))

@[simp] theorem entered_depth (p : Ports r s) (e u : Bool) (d : State r s) :
    (entered p e u d).stacks (p.stack 0) = d.stacks (p.stack 0) := by
  simp [entered, pushed, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
    BitProgram.execInstr]

@[simp] theorem entered_budget (p : Ports r s) (e u : Bool) (d : State r s) :
    (entered p e u d).stacks (p.stack 1) = d.stacks (p.stack 1) := by
  simp [entered, pushed, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
    BitProgram.execInstr]

@[simp] theorem entered_outer (p : Ports r s) (e u : Bool) (d : State r s) :
    (entered p e u d).stacks (p.stack 2) = e :: d.stacks (p.stack 2) := by
  simp [entered, pushed, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
    BitProgram.execInstr]

@[simp] theorem entered_inner (p : Ports r s) (e u : Bool) (d : State r s) :
    (entered p e u d).stacks (p.stack 3) = u :: d.stacks (p.stack 3) := by
  simp [entered, pushed, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
    BitProgram.execInstr]

@[simp] theorem entered_descending (p : Ports r s) (e u : Bool) (d : State r s) :
    (entered p e u d).regs (p.register 0) = true := by
  simp [entered, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
    BitProgram.execInstr]

@[simp] theorem entered_active (p : Ports r s) (e u : Bool) (d : State r s) :
    (entered p e u d).regs (p.register 1) = d.regs (p.register 1) := by
  simp [entered, pushed, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
    BitProgram.execInstr]

def finishLevel (p : Ports r s) : Cmd r s := pushBit p 0 true

def nextOutside (p : Ports r s) : Cmd r s :=
  .seq
    (atoms [.pop (p.stack 1) (p.register 2) (p.register 3),
      .peek (p.stack 1) (p.register 2) (p.register 3)])
    (.ite (p.register 3) (enter p true false)
      (.seq (pushBit p 1 true) (finishLevel p)))

def backtrack (p : Ports r s) : Cmd r s :=
  .seq (atoms [.pop (p.stack 2) (p.register 4) (p.register 3)])
    (.ite (p.register 3)
      (.seq (atoms [.pop (p.stack 3) (p.register 2) (p.register 3)])
        (.ite (p.register 4)
          (.ite (p.register 2)
            (.seq (pushBit p 1 true) (finishLevel p)) (enter p true true))
          (nextOutside p)))
      (atoms [.set (p.register 1) false]))

def descend (p : Ports r s) (callback : Cmd r s) : Cmd r s :=
  .seq (atoms [.pop (p.stack 0) (p.register 2) (p.register 3)])
    (.ite (p.register 3) (enter p false false)
      (.seq callback (atoms [.set (p.register 0) false, .set (p.register 1) true])))

def body (p : Ports r s) (callback : Cmd r s) : Cmd r s :=
  .ite (p.register 0) (descend p callback) (backtrack p)

def command (p : Ports r s) (callback : Cmd r s) : Cmd r s :=
  .seq (atoms [.peek (p.stack 1) (p.register 2) (p.register 3),
    .copy (p.register 1) (p.register 3), .set (p.register 0) true])
    (.while (p.register 1) (body p callback))

def program (p : Ports r s) (callback : Cmd r s) :=
  compiled (command p callback) (p.stack 0) (p.stack 2)

def popped (p : Ports r s) (i : Fin 4) (v : Fin 5) (d : State r s) : State r s :=
  (Atom.pop (p.stack i) (p.register v) (p.register 3)).eval d

def descended (p : Ports r s) (d : State r s) : State r s :=
  entered p false false (popped p 0 2 d)

def returned (p : Ports r s) (d : State r s) : State r s :=
  (Atom.set (p.register 1) true).eval ((Atom.set (p.register 0) false).eval d)

@[simp] theorem returned_stacks (p : Ports r s) (d : State r s) :
    (returned p d).stacks = d.stacks := rfl

@[simp] theorem returned_descending (p : Ports r s) (d : State r s) :
    (returned p d).regs (p.register 0) = false := by
  simp [returned, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
    BitProgram.execInstr]

@[simp] theorem returned_active (p : Ports r s) (d : State r s) :
    (returned p d).regs (p.register 1) = true := by
  simp [returned, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
    BitProgram.execInstr]

def backed (p : Ports r s) (d : State r s) : State r s :=
  popped p 3 2 (popped p 2 4 d)

def finished (p : Ports r s) (d : State r s) : State r s :=
  pushed p 0 true (pushed p 1 true (backed p d))

def testedOutside (p : Ports r s) (d : State r s) : State r s :=
  (Atom.peek (p.stack 1) (p.register 2) (p.register 3)).eval
    (popped p 1 2 (backed p d))

def pruned (p : Ports r s) (d : State r s) : State r s :=
  pushed p 0 true (pushed p 1 true (testedOutside p d))

def stopped (p : Ports r s) (d : State r s) : State r s :=
  (Atom.set (p.register 1) false).eval (popped p 2 4 d)

structure Cursor (p : Ports r s) (n J : ℕ) (pre : List (Option Bool))
    (down : Bool) (d : State r s) : Prop where
  depth : d.stacks (p.stack 0) = List.replicate n true
  budget : d.stacks (p.stack 1) = List.replicate J true
  outer : d.stacks (p.stack 2) = (pre.map Option.isSome).reverse
  inner : d.stacks (p.stack 3) = (pre.map (fun a => a.getD false)).reverse
  descending : d.regs (p.register 0) = down
  active : d.regs (p.register 1) = true

inductive BodyTrace (p : Ports r s) (callback : Cmd r s) : ℕ → State r s → State r s → Prop
  | refl (a) : BodyTrace p callback 0 a a
  | cons {n m a b c} : a.regs (p.register 1) = true → Eval (body p callback) n a b →
      BodyTrace p callback m b c → BodyTrace p callback (n + m + 1) a c

@[simp] theorem pushed_frame (p : Ports r s) (i : Fin 4) (b : Bool) (d : State r s)
    (o : Fin s) (ho : o ≠ p.stack i) : (pushed p i b d).stacks o = d.stacks o := by
  simp [pushed, ho]

@[simp] theorem popped_frame (p : Ports r s) (i : Fin 4) (v : Fin 5) (d : State r s)
    (o : Fin s) (ho : o ≠ p.stack i) : (popped p i v d).stacks o = d.stacks o := by
  simp [popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
    BitProgram.execInstr, ho]

@[simp] theorem entered_frame (p : Ports r s) (e u : Bool) (d : State r s)
    (o : Fin s) (h2 : o ≠ p.stack 2) (h3 : o ≠ p.stack 3) :
    (entered p e u d).stacks o = d.stacks o := by
  simp [entered, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
    BitProgram.execInstr, h2, h3]

@[simp] theorem testedOutside_stacks (p : Ports r s) (d : State r s) :
    (testedOutside p d).stacks = (popped p 1 2 (backed p d)).stacks := rfl

structure CallbackSpec (p : Ports r s) (callback : Cmd r s) (output : Fin s)
    (visit : List (Option Bool) → List Bool → List Bool) (C N : ℕ)
    (I : State r s → Prop) : Prop where
  stable : ∀ d e, (∀ o, (∀ i, o ≠ p.stack i) → e.stacks o = d.stacks o) → I d → I e
  run : ∀ J pre d, pre.length = N → Cursor p 0 (J + 1) pre true d → I d →
    ∃ t e, t ≤ C ∧ Eval callback t (popped p 0 2 d) e ∧
      (∀ i, e.stacks (p.stack i) = d.stacks (p.stack i)) ∧
      e.stacks output = visit pre (d.stacks output) ∧ I e

def initialized (p : Ports r s) (d : State r s) : State r s :=
  (Atom.set (p.register 0) true).eval
    ((Atom.copy (p.register 1) (p.register 3)).eval
      ((Atom.peek (p.stack 1) (p.register 2) (p.register 3)).eval d))

@[simp] theorem initialized_stacks (p : Ports r s) (d : State r s) :
    (initialized p d).stacks = d.stacks := rfl

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

/-! ## Concrete input reversal -/

/-! ## Reindex and call the checked binary word-length counter -/

def swappedLengthProgram : Program 3 3 14 :=
  ProgramLinking.liftProgram lengthProgram id swapStacks

def logProgram : Program 3 3 24 := ProgramLinking.link prepareLogProgram swappedLengthProgram

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Floor
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

inductive Forest (k M : ℕ) : List (Node n) → List BranchTree.Tree → Prop
  | nil : Forest k M [] []
  | cons {node nodes tree trees} : Derivation k M node.formula tree →
      Forest k M nodes trees → Forest k M (node :: nodes) (tree :: trees)

/-- A terminating proof measure, never a retained binary machine counter. -/
def potential (s : Frontier n) : ℕ := SparseCountProgram.potential s.model

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCompletedTree
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseSelectorRefinement
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual root selector call and its typed Appendix A certificates.
The success and terminal conclusions, return instruction, and every-prefix
storage estimate all describe the same concrete execution. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseSelectorRefinement

open BitProgram StructuredCalls SparseDFSProgram SparsePriorityProgram

variable {n : ℕ}

def literalWord (l : SAT.Literal (Fin n)) : List Bool :=
  Encoding.encodeNat (Encoding.literalCode l)

def inputVolume (F : RawCNF n) (base : List Bool) : ℕ :=
  (SparseCountProgram.encodeBody F).length + base.length + 1

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseSelectorRefinement
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

open BitProgram StructuredCalls SubexpScanPrimitives


def Metadata.coveredFlag : Metadata → Bool
  | .covered .. => true
  | .leftover .. => false

@[simp] theorem reset_reset (regs : Regs) : reset (reset regs) = reset regs :=
  StackRoutines.readRegs_reset regs 0 1 none

def parseCost : Metadata → ℕ
  | .covered block typeCode => 9 * block.length + 9 * typeCode.length + 20
  | .leftover rank => 9 * rank.length + 13

end SubexponentialSAT.Subexp.GlobalBasisMetadata

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionRows
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The triangular convolution controller charges actual fixed-width reads,
copies, and cell writes. The local pair contract is a contract for a fixed
finite command and is instantiated by the concrete quartic/jet service. -/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls

variable {C : Type*}

structure RowData (C : Type*) where
  work : Buffers
  values : List C
  pending : List C

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionOuter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The outer triangular loop of the fixed convolution controller. Each row
copies the preserved right-hand array, consumes one left coefficient, and
executes only the still-relevant output positions. -/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls

variable {C : Type*}

def outerAfter (w : Buffers) (leftTail accumulator fuelTail : List Bool) : Buffers :=
  Function.update (Function.update (Function.update (Function.update w 0 leftTail)
    2 accumulator) 4 (false :: w 4)) 5 fuelTail

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual finite-program execution of the padded triangular convolution.
The generic local pair contract is instantiated separately by the concrete
quartic multiplier and persistent-cell update service. -/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls

variable {C : Type*}

def finishedBuffers (w : Buffers) (result : List Bool) : Buffers :=
  Function.update (Function.update (Function.update (Function.update w 0 []) 2 result) 4 []) 5 []

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Restricted support of the multicolor interpolation matrices

The multicolor register permutations and the products of (1 - J_l) / 2 are constructed
explicitly.  The support conclusion is derived from their sublist expansion.
-/

namespace SubexponentialSAT.Subexp.MatrixSupport

open SubexponentialSAT.MulticolorTypes
open scoped BigOperators

variable {r Q Δ : ℕ}

section Operators

variable {K : Type*} [Field K]

/-- Eigenvalue obtained by multiplying the position eigenvalues and evaluating
the elementary symmetric polynomial on (1 - sign) / 2. -/
noncomputable def matrixEigenvalue (t : Fin Q) (R : ℕ)
    (c : ℕ → K) (sign : Fin Q → K) : K :=
  (∏ l ∈ activePositions t, sign l) *
    ∑ j ∈ Finset.range R, c j *
      ∑ A ∈ (activePositions t).powersetCard j, ∏ l ∈ A, (1 - sign l) / 2

end Operators

end SubexponentialSAT.Subexp.MatrixSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixEntryKernel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Scalar kernels of the actual multicolor matrix

The tensor coordinates below describe entries of the existing swap/projector
operator. They do not introduce a new matrix chosen only for its rank or support.
-/

namespace SubexponentialSAT.Subexp.MatrixEntryKernel

open SubexponentialSAT.MulticolorTypes
open scoped BigOperators

variable {r Q Δ : ℕ}

section Field

variable {K : Type*} [Field K]

def factor (i : Fin Δ) (s : Finset (Fin Q))
    (u y : UniversalType r Q Δ) (l : Fin Q) : K :=
  if l ∈ s then plain i u y l - flipped i u y l else plain i u y l

noncomputable def partialKernel (i : Fin Δ) (s : Finset (Fin Q))
    (u y : UniversalType r Q Δ) : K :=
  background i u y * ∏ l, factor i s u y l

end Field

end SubexponentialSAT.Subexp.MatrixEntryKernel

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixEntryScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A scalar generating polynomial for the actual matrix entries

The coefficient of degree j equals 2^j times the j-th elementary projector
kernel. Consequently normalized coefficients need only scalar polynomial
arithmetic, with no enumeration of subsets in the eventual implementation.
-/

namespace SubexponentialSAT.Subexp.MatrixEntryKernel

open SubexponentialSAT.MulticolorTypes Polynomial
open scoped BigOperators

variable {r Q Δ : ℕ} {K : Type*} [Field K]

noncomputable def kernelPolynomial (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) : K[X] :=
  C (background i u y * plain i u y t) *
    ∏ l ∈ MatrixSupport.activePositions t,
      (C (flipped i u y l) + C (flipped i u y l - plain i u y l) * X)

end SubexponentialSAT.Subexp.MatrixEntryKernel

/-! The scalar kernel has only three nonzero local factors: 1, -X, and 1+X. -/

namespace SubexponentialSAT.Subexp.MatrixEntryKernel

open SubexponentialSAT.MulticolorTypes Polynomial
open scoped BigOperators

variable {r Q Δ : ℕ} {K : Type*} [Field K]

/-- The physical counter may test all Q coordinates without masking t. -/
def AllCompatible (i : Fin Δ) (u y : UniversalType r Q Δ) : Prop :=
  SpectatorsAgree i u y ∧
    ∀ l, pair i u l = pair i y l ∨ (u.slot i l, u.head l) = pair i y l

instance allCompatibleDecidable (i : Fin Δ) (u y : UniversalType r Q Δ) :
    Decidable (AllCompatible i u y) := by
  unfold AllCompatible SpectatorsAgree
  infer_instance

def allUnchanged (i : Fin Δ) (u y : UniversalType r Q Δ) : Finset (Fin Q) :=
  Finset.univ.filter fun l => u.head l ≠ u.slot i l ∧ pair i u l = pair i y l

def allTransposed (i : Fin Δ) (u y : UniversalType r Q Δ) : Finset (Fin Q) :=
  Finset.univ.filter fun l => u.head l ≠ u.slot i l ∧ (u.slot i l, u.head l) = pair i y l

end SubexponentialSAT.Subexp.MatrixEntryKernel

/-!
# Exact binomial formula for the implemented multicolor matrix

This connects scalar additions and sign changes to the very same matrix
used in the support and rank proofs. The only normalization hypothesis is
that the field has characteristic different from two.
-/

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

abbrev Data := State 8 32

def counted (a : Data) (n : ℕ) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update a.stacks 17 []) 14 (Encoding.encodeNat n)⟩

end SubexponentialSAT.Subexp.UniversalRowGuard

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowGather
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Reading actual scalar and difference-row data for universal rows

All tables are packed runtime arrays. The selected index is unary data on
stack 16. The three fixed reads preserve their source tables and index and
produce the correction scalar, inverse node, and complete difference row.
-/

namespace SubexponentialSAT.Subexp.UniversalRowGather

open BitProgram StructuredCalls StackRoutines

abbrev Data := State 8 32

end SubexponentialSAT.Subexp.UniversalRowGather

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

abbrev Data := State 8 32

end SubexponentialSAT.Subexp.UniversalRowTermFraming

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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
open SubexpSymbolicCost SubexpRowInterpolation SubexpRepresentedRows
open UniversalRowProgram

variable {C E : Type*} {Q : ℕ}

def rowData {V G : Type*} [Fintype V] [DecidableEq V] [DecidableEq G]
    (ops : RingProgram C) (cache : NodeCache C Q)
    (v : V) (head : V → Fin Q → G) (σ : Fin Q → G) (R : ℕ)
    (d : V → Fin Q → C) (y : V) : Row C :=
  ⟨if v = y then ops.oneRun.1 else ops.zeroRun.1,
    if y ∈ correctionColumns head σ R then
      (selected (mismatchPositions head σ y)).map
        (termData ops cache (mismatchPositions head σ y) (d y))
    else []⟩

def mapRow {A : Type*} (f : C → A) (x : Row C) : Row A :=
  ⟨f x.delta, x.terms.map (mapTerm f)⟩

end SubexponentialSAT.Subexp.UniversalRowSource

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

abbrev Data := State 8 29

end SubexponentialSAT.Subexp.MatrixInputAccess

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

open BitProgram StructuredCalls StackRoutines ArrayPrograms

abbrev Data := State 8 23

abbrev copiedWidth (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, copyStacks 21 10 a.stacks⟩

abbrev taken (a : Data) (src : Fin 23) (segment rest : List Bool) : Data :=
  ⟨readRegs a.regs 0 1 none, countedTransferStacks 10 src 4 segment rest a.stacks⟩

abbrev restored (a : Data) (dst : Fin 23) : Data :=
  ⟨readRegs a.regs 0 1 none, transferStacks 4 dst a.stacks⟩

abbrev pulled (a : Data) (src dst : Fin 23) (segment rest : List Bool) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update a.stacks src rest) dst segment⟩

abbrev fourPulled (a : Data) (words rests : Fin 4 → List Bool) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update
        a.stacks 13 (words 0)) 14 (words 1)) 15 (words 2)) 16 (words 3))
      17 (rests 0)) 18 (rests 1)) 19 (rests 2)) 20 (rests 3)⟩

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

abbrev Data := State 8 17

end SubexponentialSAT.Subexp.MatrixPositionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixScanStepProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One physical scan iteration: read four equal-width color records,
classify their same/swapped relation, and clear the consumed color buffers. -/

namespace SubexponentialSAT.Subexp.MatrixScanStepProgram

open BitProgram StructuredCalls StackRoutines

abbrev Data := State 8 23

end SubexponentialSAT.Subexp.MatrixScanStepProgram

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

abbrev Data := State 8 23

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

def compatible (w : ColorRow) : Bool := same w || swapped w

end SubexponentialSAT.Subexp.MatrixScanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixInputTypes
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The concrete extractor on canonical one-hot type encodings. -/

namespace SubexponentialSAT.Subexp.MatrixInputTypes

open BitProgram StructuredCalls MulticolorTypes ReadPlan MatrixInputProgram

variable {r Q Δ : ℕ}

def slotRows (u : UniversalType r Q Δ) : List (List Bool) :=
  List.ofFn (fun j => encodeWord (u.slot j))

def before (i : Fin Δ) (u : UniversalType r Q Δ) : List (List Bool) :=
  (slotRows u).take i.val

def after (i : Fin Δ) (u : UniversalType r Q Δ) : List (List Bool) :=
  (slotRows u).drop (i.val + 1)

def normalizedType (common : Word r Q) (i : Fin Δ) (u : UniversalType r Q Δ) :
    UniversalType r Q Δ := ⟨common, Function.update u.slot i common⟩

end SubexponentialSAT.Subexp.MatrixInputTypes

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

abbrev Data := State 10 42

end SubexponentialSAT.Subexp.MatrixAnchorGuardProgram

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

abbrev Data := State 10 42

end SubexponentialSAT.Subexp.MatrixAnchorReadProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixAnchorTypes
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Canonical one-hot color reads for the explicit joint-membership guard. -/

namespace SubexponentialSAT.Subexp.MatrixAnchorReadProgram

open BitProgram StructuredCalls StackRoutines MulticolorTypes

variable {r Q Δ : ℕ}

def wordRows (w : Word r Q) : List (List Bool) := List.ofFn fun t => colorWord (w t)

end SubexponentialSAT.Subexp.MatrixAnchorReadProgram

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

abbrev Data := State 8 16

end SubexponentialSAT.Subexp.MismatchPlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowMismatchProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Generate all positions on tape, then retain the mismatches.  The output
is in descending position order, as required by the prepend-based row loops. -/

namespace SubexponentialSAT.Subexp.UniversalRowMismatchProgram

open BitProgram StructuredCalls StackRoutines
open MismatchPlanProgram (indexRecords mismatch)

abbrev Data := State 10 17

end SubexponentialSAT.Subexp.UniversalRowMismatchProgram

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

abbrev Data := State 10 49

end SubexponentialSAT.Subexp.UniversalRowMismatchTypes

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadEvaluation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Restricted sums over the actual Boolean heads. All products are formed in
one coefficient ring before any additive coefficient readout. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluation
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open scoped BigOperators

variable {V R : Type*} [DecidableEq V]

def specializeEntries (U : Finset V) : List (Squarefree.Index V × R) →
    List (Squarefree.Index V × R)
  | [] => []
  | (a,c)::xs => if a.vars ⊆ U then (⟨a.u,a.z,∅⟩,c)::specializeEntries U xs
      else specializeEntries U xs

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSpecializationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Immediate Boolean specialization using the actual dictionary scanner. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Subset
open OAI BitProgram StructuredProgram

def program := compiled command 0 2

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Subset

/-! The dictionary framing, key rewrite and record traversal follow the actual
MomentsProjectionProgramNative implementation. The replacement comparator tests
support inclusion, so this scan implements evaluation at a Boolean correction
assignment. Numeric-key collisions are intentionally left for normalization. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Specialization
open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog MomentsProjectionProgram

def scanSubset : Cmd 5 10 := .call
  (ProgramLinking.liftProgram Subset.program id subsetPorts)
def compare : Cmd 5 10 := .seq scanSubset (transfer 6 1)

def selected (query : List Bool) : List Entry → List Entry
  | [] => []
  | e::es => if Subset.below e.mask query = true then e.erased::selected query es
      else selected query es


open Squarefree

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Specialization
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_TruncatedRingProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Native arithmetic after immediate Boolean specialization

The existing finite sparse-product program is used with empty formal support.
Its keys still carry the ambient input coordinate type; this does not compress
the declared variables. There are at most `u * J` retained entries, including
zero cutoffs. Polynomial local time therefore bounds all its source prefixes,
including the table, inputs, output, normalization copies and arithmetic scratch.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram

open scoped BigOperators
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram BitProgram

/- The two fields coincide with LeafProgram.NativeSemantics.Good. The
arithmetic layer states them transparently to avoid importing the factor
interpreter. Conversion in either direction supplies `valid` and `nodup`.
The proof bodies below are the original finite-program validity arguments. -/

variable {V R : Type*} [DecidableEq V] [CommRing R]

/-- A common explicit polynomial majorant for every local arithmetic service.
`N` counts unnormalized specialized records; it need not be at most `u * J`. -/
def localBudget (n B d u J N : ℕ) : ℕ :=
  normalizationBudget n B d u J N + additionBudget n B d u J +
    scalingBudget n B d u J + productBudget n B d u J +
    MomentsReadoutProgram.uniformReadoutBudget B d n u J (n + u + J) (u * J)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
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

def ports : RecordPrograms.Ports 40 896 :=
  ⟨13, 14, 15, 150, 149, by decide, by decide, by decide, by decide⟩

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

def loopBudget (C : ℕ) (ids : List ℕ) : ℕ :=
  RecordPrograms.budget (fun _ => C) (records ids)+3

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorEnvironment
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The seven fixed persistent cache words are physically copied into the
native arithmetic environment. Cleanup clears those seven copies; both
commands frame all other stacks, including the query buffers. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEnvironment

open OAI BitProgram StructuredCalls
open SubexpSetupStorage SqrtLog.MomentsProgram

def bootstrap16 : Cmd 16 896 := copyMany 159 pairs

def bootstrap : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram (compiled bootstrap16 194 5) registerMap id)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEnvironment
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

/-- The fixed command pays entry clearing, relocated staging, its ambient
unary table loop, relocated export and final halt. -/
def commandBudget (B n K L : ℕ) : ℕ :=
  entryPorts.length * (2 * B + 3) + (133 * B + 98) + tableBudget n K L +
    (687 * middleBound B n L + 1026) + 1

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FiniteFallback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Generic finite scanner selectively adapted from the reviewed canceled source
`CountingDraft/FiniteWordScanner.lean`; no obsolete endpoint or rate is imported.

Fixed finite control for bounded input prefixes and complete binary output words.
The transition table is chosen before any runtime input. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.Scanner



open BitProgram

variable {qCount : ℕ}

def program (L : ℕ) (start : Fin qCount) (next : Fin qCount → Bool → Fin qCount)
    (out : Fin qCount → List Bool) (hout : ∀ q, (out q).length ≤ L) :
    Program 2 1 (labelCount (qCount := qCount) L) where
  inputStack := 0
  outputStack := 0
  entry := addr L start 0 (by omega)
  code label :=
    let q := (decode L label).1
    let i := (decode L label).2.val
    if i = 0 then .pop 0 0 1 (addr L q 1 (by omega))
    else if i = 1 then .branch 1 (addr L q 2 (by omega)) (addr L q 3 (by omega))
    else if i = 2 then .branch 0
      (addr L (next q true) 0 (by omega)) (addr L (next q false) 0 (by omega))
    else if h : i < 2 * (out q).length + 3 then
      if (i - 3) % 2 = 0 then
        .set 0 ((out q).reverse[(i - 3) / 2]?.getD false)
          (addr L q (i + 1) (by have := hout q; omega))
      else .push 0 0 (addr L q (i + 1) (by have := hout q; omega))
    else if hdone : i = 2 * (out q).length + 3 then
      .set 0 false (addr L q (i + 1) (by have := hout q; omega))
    else .halt

def cfg (L : ℕ) (q : Fin qCount) (i : ℕ) (hi : i < 2 * L + 5)
    (value present : Bool) (word : List Bool) : Cfg 2 1 (labelCount (qCount := qCount) L) :=
  ⟨some (addr L q i hi), regs value present, fun _ => word⟩


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.Scanner

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback

open BitProgram Scanner
open scoped BigOperators

def literalPairEquiv (n : ℕ) : (Fin n × Bool) ≃ SAT.Literal (Fin n) where
  toFun p := ⟨p.1, p.2⟩
  invFun l := (l.variable, l.positive)
  left_inv _ := rfl
  right_inv _ := rfl

instance literalFintype (n : ℕ) : Fintype (SAT.Literal (Fin n)) :=
  Fintype.ofEquiv (Fin n × Bool) (literalPairEquiv n)

/-- The finite domain is fixed by the cutoff, before the input. Ambient variables
are part of the domain and therefore contribute their full free-variable factor. -/
def SmallFormula (B : ℕ) := (n : Fin (B + 1)) × SAT.CNF (Fin n.val)

instance smallFormulaFintype (B : ℕ) : Fintype (SmallFormula B) := by
  unfold SmallFormula
  infer_instance

def smallEncode {B : ℕ} (F : SmallFormula B) : List Bool := Encoding.encodeCNF F.2

noncomputable def inputBound (B : ℕ) : ℕ := finiteOutputBound (smallEncode (B := B))

/-- Finite precomputation forms part of the fixed finite transition table. It is
not an input-dependent runtime loop or a unit-cost semantic query. -/
noncomputable def tableCount (B : ℕ) (word : List Bool) : ℕ :=
  ∑ F : SmallFormula B, if smallEncode F = word then SAT.count F.2 else 0

noncomputable def outputTable (B : ℕ) : Option (BoundedWord (inputBound B)) → List Bool
  | none => [false]
  | some word => countWord (tableCount B word.val)

noncomputable def countProgram (B : ℕ) :=
  let e := Fintype.equivFin (Option (BoundedWord (inputBound B)))
  program (finiteOutputBound (outputTable B))
    (e (some ⟨[], Nat.zero_le _⟩))
    (fun q bit => e (boundedNext (inputBound B) (e.symm q) bit))
    (fun q => outputTable B (e.symm q))
    (fun q => length_le_finiteOutputBound (outputTable B) (e.symm q))

open StructuredCalls

def cutoffScanner (B : ℕ) :=
  Scanner.program 1 (⟨0, by omega⟩ : Fin (B + 2)) (cutoffNext B) (cutoffOut B)
    (by intro q; rfl)


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashCandidateProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog

namespace ZeroCounter

open OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

def pairs (n : ℕ) (tail : List Bool) : List Bool :=
  escaped (List.replicate n false) ++ tail

@[simp] theorem pairs_zero (tail : List Bool) : pairs 0 tail = tail := rfl

@[simp] theorem pairs_succ (n : ℕ) (tail : List Bool) :
    pairs (n + 1) tail = true :: false :: pairs n tail := by
  simp [pairs, List.replicate_succ]

end ZeroCounter

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyRound
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete streamed greedy rounds. The query seam below consists of actual
executions of the fixed attempt command; it must be instantiated by the native
exact-query implementation before an endpoint theorem can use these results. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound

open BitProgram StructuredCalls SqrtLog
open HashGreedyProgram HashGreedyProgram.NativeRound

/-- Proof-level name for the deterministic cached minimum. The finite machine
uses its binary counter and two entries, not this mathematical recursion. -/
def chosenEntry (entry : List (List Bool) → ℕ → BinaryArgmin.Entry)
    (C : ℕ) (rows : List (List Bool)) : BinaryArgmin.Entry :=
  (HashGreedy.scan BinaryArgmin.value (entry rows) (2 ^ C - 1)).1

def nextRows (entry : List (List Bool) → ℕ → BinaryArgmin.Entry)
    (C : ℕ) (rows : List (List Bool)) : List (List Bool) :=
  (chosenEntry entry C rows).payload :: rows

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyCNF
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The concrete streamed selector uses the original ternary row semantics.
Its exact scores and normalized reference coverage discharge the greedy
contraction hypotheses. These statements concern the deterministic history
refined by the native run; native query and resource closure remain separate. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF

open SqrtLog
open scoped BigOperators

noncomputable section

def decode (m : ℕ) : List Bool → HashSelect.Row m :=
  HashFamilyPayload.decodeVariableRow m (HashCandidates.digitWidth m)

def rowAccept {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (payload : List Bool) : SAT.Assignment (Fin n) → Bool :=
  HashSelect.cnfRowAccept clauses (decode m payload)

/-- Reference indices retain the original tuple multiplicities. -/
def reference {m depth c : ℕ} (hcount : (3 * m) ^ depth = c + 1)
    (i : Fin (c + 1)) : List Bool :=
  HashFamilyPayload.encode (HashCandidates.digitWidth m)
    (HashFamily.enumerate m depth (Fin.cast hcount.symm i))

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMassAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual marked-clause collector generalized to the frozen 40/896 leaf
bank. Its parser and adder are the original measured finite programs. All
marked queries are executed; their integer results are added before argmin.
The temporary query execution premise must be discharged by the concrete
optional-mark evaluator, including its high-assignment loop and cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram

def recordPorts : RecordPrograms.Ports 40 896 where
  tag := 16
  present := 17
  found := 18
  source := 320
  payload := 321
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide


open LeafOuterProgram

open scoped BigOperators


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter
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

def trialPorts : RecordPrograms.Ports 40 896 :=
  ⟨0,1,2,702,701,by decide,by decide,by decide,by decide⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual candidate attempt is the fixed normalizer, all-clause mass
collector, and paid fixed-width padding. The only remaining query execution
premise is the concrete per-mark evaluator, including its exact caller frame. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyExecution

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashGreedyProgram HashGreedyProgram.NativeRound HashMassAdapter

/-- Mathematical readback of the actual unary reference records. -/
noncomputable def referenceCount {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (rows : List (List Bool)) (bits : List Bool) : ℕ :=
  match Encoding.readNat bits with
  | some (index, []) => if h : index < m then
      markedCount (HashGreedyCNF.rowAccept clauses) rows
        (fun e x => !(clauses e).eval x) ⟨index,h⟩ else 0
  | _ => 0

@[simp] theorem referenceCount_encode {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (rows : List (List Bool)) (e : Fin m) :
    referenceCount clauses rows (Encoding.encodeNat e.val) =
      markedCount (HashGreedyCNF.rowAccept clauses) rows
        (fun e x => !(clauses e).eval x) e := by
  simp [referenceCount, e.isLt]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyExecution
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpClauseRowProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# An actual clause-row program

The input clause uses `Encoding.encodeList Encoding.encodeNat`. The stored
assignment is an explicit word of the declared length, one bit per variable.
The program parses each literal, decodes its unary index and polarity, performs
a preserving indexed read, and accumulates the disjunction. No semantic test is
an instruction. All auxiliary ports and all input requirements are explicit.
-/

namespace SubexponentialSAT.SubexpClauseRowProgram

open BitProgram StructuredCalls

def data (v pr sign acc : Bool) (assignment output index width source payload : List Bool) :
    State 4 10 := ⟨regs v pr sign acc, tapes assignment output index width source payload⟩

namespace LiteralDecoder

def cfg (pc : Option (Fin 8)) (v pr sign acc : Bool)
    (assignment output index width source payload : List Bool) : Cfg 4 10 8 :=
  (data v pr sign acc assignment output index width source payload).withPC pc

end LiteralDecoder


end SubexponentialSAT.SubexpClauseRowProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpChunkRecordMap
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual map from literal records to chunk records

The input is the canonical encoded list of literal codes and a preserved binary
chunk width. Each parsed record passes through the actual index decoder,
counter, division program, and record writer. The accumulator is reversed, as
required by the separately checked record-reversal and stable-deduplication
passes. No semantic map is installed as a machine instruction.
-/

namespace SubexponentialSAT.SubexpChunkRecordMap

open BitProgram StructuredCalls

abbrev Data := State 11 22

def Canonical (bits : List Bool) : Prop := ∃ code, bits = Encoding.encodeNat code

end SubexponentialSAT.SubexpChunkRecordMap

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashQueryInputBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical input bounds for all attained greedy histories and every trial,
including losing candidates. All bounds concern literal retained words and
raw slots. No execution-time or successful-query bound is used. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryInputBounds

open BitProgram StructuredCalls SqrtLog
open HashGreedyProgram HashGreedyCNF

/-- One finite sum collects concrete numeric parameters and a physical
master-word allowance. Its definition contains no search or query time. -/
def commonCap (n m B wordBound : ℕ) : ℕ :=
  n + m + SparseCode.totalRows m B + SparseCode.degreeBound m B +
    SparseCode.distanceDenom m B + HashCandidates.digitWidth m + HashSelect.loopCap n m + wordBound + 1

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryInputBounds
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SparseCodeSearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch

open BitProgram StructuredCalls CodeCandidateProgram


open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram CodeChecks

def localTime (A t D d : ℕ) : ℕ :=
  timeBudget (t * D) (boundary A (t * D))
    (candidateBudget (boundary A (t * D)) (t * D) D (callbackBudget t D d) (localStreamBudget t D d))
    (candidateSpace (boundary A (t * D)) (t * D) D (callbackBudget t D d))

def graphTime (A D r qlen Dlen : ℕ) : ℕ :=
  timeBudget (D * r) (boundary A (D * r))
    (candidateBudget (boundary A (D * r)) (D * r) r (graphCallbackBudget D r qlen Dlen)
      (graphStreamBudget D r qlen Dlen))
    (candidateSpace (boundary A (D * r)) (D * r) r (graphCallbackBudget D r qlen Dlen))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed physical stages for the streamed local-code and graph-code searches.
The retained search state is confined to the lower48 leaf stacks; selected
matrices are saved outside that bank before its paid cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode

open BitProgram StructuredCalls
open SqrtLog SqrtLog.LeafOuterProgram SqrtLog.CodeSearchProgram


def graphStageTime (A m occurrence qlen Dlen : ℕ) : ℕ :=
  5 * (9 * A + 8) + 3 +
    (SparseCodeSearch.graphTime A (SparseCode.degree m occurrence)
      (SparseCode.dimension m occurrence) qlen Dlen + 1 +
      (105 * SparseCodeSearch.boundary A
        (SparseCode.degree m occurrence * SparseCode.dimension m occurrence) + 155))


def localStageTime (A m occurrence : ℕ) : ℕ :=
  4 * (9 * A + 8) + 3 +
    (SparseCodeSearch.localTime A (SparseCode.localRows m occurrence) (SparseCode.degree m occurrence)
      (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) + 1 +
      (105 * SparseCodeSearch.boundary A
        (SparseCode.localRows m occurrence * SparseCode.degree m occurrence) + 155))

def searchesTime (A m occurrence qlen Dlen : ℕ) : ℕ :=
  graphStageTime A m occurrence qlen Dlen + localStageTime (graphBoundary A m occurrence) m occurrence

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeCodeAssembly
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram SubexpSetupStorage

def afterTime (A m occurrence qlen : ℕ) (dword mword width : List Bool) : ℕ :=
  NativeCode.searchesTime A m occurrence qlen dword.length +
    serializerTime (SparseCode.dimension m occurrence) (SparseCode.degree m occurrence)
      (SparseCode.localRows m occurrence) (NativeCode.searchBoundary A m occurrence)
      dword mword width

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizationCorrectness
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!+# Canonical-input correctness of the encoded normalizer

The program consumes the body left by the separate header parser. The output
is exactly the typed sparsifier's ordered normalized input. The declared
variable universe is retained, so unused coordinates require no renaming.
-/

namespace SubexponentialSAT.SubexpNormalizationCorrectness

open BitProgram
open SubexpNormalizationProgram (formulaCode )

def normalizedFormula {n : ℕ} (F : SAT.CNF (Fin n)) : ExecSparsifyWorklist.Formula n :=
  ExecSparsifyWorklist.normalizedInput (ExecQuantitativeSparsify.formulaList F)

def normalizedBody {n : ℕ} (F : SAT.CNF (Fin n)) : List Bool :=
  ExecQuantitativeSparsify.encodeRawFormula (normalizedFormula F)

end SubexponentialSAT.SubexpNormalizationCorrectness

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeFrontend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls

def frontendBound {n : ℕ} (F : SAT.CNF (Fin n)) : ℕ :=
  14 * Encoding.formulaBitLength F + 4 * n + 11 * (Encoding.encodeCNFBody F).length + 27 +
    FrontendProgram.initializeBound n + 3300 * ((Encoding.encodeCNFBody F).length + 1) ^ 2


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLayoutLoad
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid node-start loading of the parked source bank. Only the original
layout copy program is called; no head enumeration is imported or executed. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLayoutLoad

open OAI BitProgram StructuredCalls SubexpSetupStorage SqrtLog
open LeafProgram LeafHeadSetupProgram

def clearPorts : List (Fin 896) :=
  [684,660,665] ++ LayoutMasters.lowPorts.map stackMap

theorem mem_low_clear (i : Fin 14) : stackMap (LayoutMasters.low i) ∈ clearPorts := by
  apply List.mem_append_right
  apply List.mem_map.mpr
  exact ⟨LayoutMasters.low i,List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩,rfl⟩

theorem not_mem_high_clear (i : Fin 14) : stackMap (LayoutMasters.high i) ∉ clearPorts := by
  intro h
  rcases List.mem_append.mp h with h|h
  · simp only [List.mem_cons,List.mem_nil_iff,or_false] at h
    rcases h with h|h|h <;> have hv := congrArg Fin.val h <;>
      simp only [stackMap,LayoutMasters.high,Fin.val_castAdd,Fin.coe_ofNat_eq_mod] at hv <;> omega
  · obtain ⟨j,hj,hj'⟩ := List.mem_map.mp h
    obtain ⟨k,_,hk⟩ := List.mem_map.mp hj
    subst j
    have hv := congrArg Fin.val hj'
    change 128+k.val=730+i.val at hv
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLayoutLoad
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeTerminal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual outer-CNF terminal handling. The ambient unary header is retained;
an empty formula emits its full count 2^n, and an empty clause emits zero. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal

open BitProgram StructuredCalls
open scoped BigOperators

def clauseRecords {n : ℕ} (F : List (List (SAT.Literal (Fin n)))) : List (List Bool) :=
  F.map (Encoding.encodeList ExecSunflowerCodeTransport.literalWord)

@[simp] theorem clauseRecords_nil_iff {n : ℕ} (F : List (List (SAT.Literal (Fin n)))) :
    clauseRecords F = [] ↔ F = [] := by simp [clauseRecords]


open DisjointReuse.DFSVisit

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete leaf control: prepared code history, all physically staged greedy
rounds, and a separate history-only exact count. The query execution proofs
remain explicit development seams until the native query bodies instantiate them. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashGreedyProgram HashGreedyProgram.NativeRound HashGreedyRound
open HashMassAdapter HashGreedyExecution

/-- One retained cap supplies every numerical hypothesis of ready_rounds.
It depends on physical input words and ordinary scalar dimensions, not time. -/
def commonBound (n m B wordBound : ℕ) : ℕ :=
  16 * (HashQueryInputBounds.commonCap n m B wordBound) ^ 3

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeOuter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed outer instruction sequence composes actual parameter setup,
disjoint counting DFS, and full-word positivity. The existing concrete-leaf
contract remains an explicit development obligation, not a final endpoint. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls DisjointReuse

def dfsTime (k n bodyLength thresholdLength leafTime bound visits : ℕ) : ℕ :=
  8 * bodyLength + 16 +
    (visits * (DFSVisit.visitTime k n (SparseCountProgram.formulaBound n k)
      thresholdLength leafTime bound + 1) + 1) + (2 * bound + 7 * n + 18)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeQueryPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete query packing and arithmetic preparation. Numeric and physical
input caps are kept separate from the subsequent exponential node traversal.
Every arithmetic object is returned by its actual native producer. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query CostAssembly.Polynomial

theorem setupEnvelope_polynomial (Cp dp Ca da : ℕ) :
    CostAssembly.Polynomial.Ordinary (setupEnvelope Cp dp Ca da) := by
  have hP : Ordinary (fun S => Cp * (790 * (S + 1)) ^ dp) :=
      ordinary_mul (ordinary_const Cp) (ordinary_pow
        (ordinary_mul (ordinary_const 790) (ordinary_add ordinary_id (ordinary_const 1))) dp)
  have hA := ordinary_add ordinary_id hP
  have hB := ordinary_mul (ordinary_const Ca)
      (ordinary_pow (ordinary_add hA (ordinary_const 1)) da)
  exact ordinary_add (ordinary_add hA hB) (ordinary_const 1)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NodeReadoutSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual node-array readout after all finite-difference pairs. The fixed
cleanup pays for transient lower words and clears the old output. Preserved
masters supply the coefficient zero vector and both truncation bounds. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

def budget (n B d u J incoming : ℕ) : ℕ :=
  41 * (2 * incoming + 3) +
    MomentsReadoutProgram.uniformReadoutBudget B d n u J (n + u + J) (u * J) + 1

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NodeAppendSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeAppendSpace
open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

def budget (n B d u J incoming : ℕ) : ℕ :=
  29 * incoming + 27 + NodeReadoutSpace.budget n B d u J incoming +
    6 * (incoming + J * (d * B)) + 9

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeAppendSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryNodeFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual node readout and loop continuation. The emitted coefficient stream
retains its order. Node temporaries are physically reclaimed before refreshing
the outer guard, and every completed node restores one fixed boundary bound. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

def budget (n wordWidth d u J incoming : ℕ) : ℕ :=
  NodeAppendSpace.budget n wordWidth d u J incoming + 4 * incoming + 10

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete bit primitives for streamed finite-difference queries. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram

open OAI BitProgram
open scoped BigOperators

/-- Scan the actual bits, accumulating their XOR in register 2. -/
def parityProgram : Program 3 1 4 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code := ![.pop 0 0 1 1, .branch 1 2 3, .bxor 2 2 0 0, .halt]

def parityStart (regs : Fin 3 → Bool) (bits : List Bool) : Cfg 3 1 4 :=
  ⟨some 0, regs, fun _ => bits⟩

def parityFinish (b : Bool) : Cfg 3 1 4 :=
  ⟨none, ![false, false, b], fun _ => []⟩

open StructuredCalls

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Fixed-control interpreter for streaming signature tuples

The input-dependent depth is represented by an encoded stack of suspended
frames. `probe` tests one candidate against earlier assignments. A rejected
candidate advances at its current depth; only a fresh signature descends.
Thus this control table never traverses raw assignment tuples.

The subroutines are concrete finite commands, and all execution theorems use
their actual measured evaluations. Instantiating their frame, signature, and
counter invariants remains a separate native-program obligation.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram

open BitProgram StructuredCalls

/-- Consume the current generator payload and prepend its escaped reverse to
the suspended-frame stack. The verified parser recovers the original order. -/
def pushFrameProgram : Program 2 2 8 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code q := match q.val with
    | 0 => .set 0 false 1
    | 1 => .push 1 0 2
    | 2 => .pop 0 0 1 3
    | 3 => .branch 1 4 7
    | 4 => .push 1 0 5
    | 5 => .set 0 true 6
    | 6 => .push 1 0 2
    | _ => .halt

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryStreamProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed streaming query runs the actual pair DFS, attained-signature
DFS, two-pass visitor, node readout and canonical count reconstruction. Its
finite command tables have no callback or evaluator parameters. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram

open OAI BitProgram StructuredCalls
open SignatureTupleProgram SignatureTupleNative
noncomputable section

/-- The four persistent pair words are separate from the tuple and arithmetic
banks. The callback is permitted to overwrite all five controller registers. -/
def pairPorts : DifferencePairsProgram.Ports 40 896 where
  register := Fin.castAddEmb 35
  stack := {
    toFun := fun i => ⟨832+i.val,by have := i.isLt; omega⟩
    inj' := by
      intro i j h
      apply Fin.ext
      have hv := congrArg Fin.val h
      change 832+i.val=832+j.val at hv
      omega }

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeOuterBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The exact large-entry arithmetic join: paid canonical frontend, fixed
cutoff test, actual setup, disjoint DFS, full-word positivity and factor-seven
primitive compilation. These numerical bounds introduce no run contract. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeOuterBudgets
open OAI BitProgram StructuredCalls SqrtLog.Statement DisjointReuse

/-- The exact upper bound obtained by composing the measured source phases
and then applying the actual guarded compiler's factor seven. -/
def entryTime (k n L body threshold leafTime inputBound bound visits setupSteps : ℕ) : ℕ :=
  7*(4000*(L+1)^2+10*n+29+setupSteps+
    Native.dfsTime k n body threshold leafTime bound visits+
    12*Native.outerBoundary inputBound bound n+14+1)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeOuterBudgets
end


