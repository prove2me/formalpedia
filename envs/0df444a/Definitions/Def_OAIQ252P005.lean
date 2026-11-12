-- Prove2me | Definitions.Def_OAIQ252P005
-- name    : OAIQ252P005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T07:34:00.703758+00:00
-- url     : https://prove2.me/theorems/73ed7019-688b-4b1d-b5ec-90df9c53ff43
-- title:
--   Definitions bundle OAIQ252P005 of the split of OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 858 declarations of OpenAI's Lean: 317 definitions, 1 inductive type or structure, 4 instances and 536 theorems. The definitions and types are `OAI.PerfectCompleteness.GeometricPrefixSplit.depthEquiv`, `OAI.PerfectCompleteness.NormalizationEmitMachine.emitSign`, `OAI.PerfectCompleteness.NormalizationWords.literalBits`, `OAI.PerfectCompleteness.OutputAnnihilator.bad`, `OAI.PerfectCompleteness.ProjectionPosterior.bernoulli`, `OAI.PerfectCompleteness.RestrictionRowsLaw.fromRows`, `OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear`, `OAI.PerfectCompleteness.RestrictionRowsLaw.selectLinear`, `OAI.PerfectCompleteness.RestrictionRowsLaw.selectedRowsLinear`, `OAI.PerfectCompleteness.SignedCostEnvelope.bodyBound`, `OAI.PerfectCompleteness.SignedCostEnvelope.endpointBound`, `OAI.PerfectCompleteness.SourceAmplification.repetitionLength`, `OAI.PerfectCompleteness.SourceOccurrenceIndexMachine.instruction`, `OAI.PerfectCompleteness.SourceOddLists.repetitionLength`, `OAI.PerfectCompleteness.TargetFinalizeMachine.Labels`, `OAI.PerfectCompleteness.TargetFinalizeMachine.WorkLabel`, `OAI.PerfectCompleteness.TargetFinalizeMachine.headerTapes`, `OAI.PerfectCompleteness.TargetHeaderMachine.headerInTime`, `OAI.PerfectCompleteness.TargetHeaderMachine.instruction`, `OAI.PerfectCompleteness.TargetTapeEnvelope.bound`, `OAI.PerfectCompleteness.TensorProjectedSlice.totalMatrix`, `OAI.PerfectCompleteness.TupleInitializationMachine.initializeInTime`, `OAI.PerfectCompleteness.TupleInitializationMachine.instruction`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerInputTapes`, `OAI.UniqueGamesTheorem.Foundations.Complexity.GraphCounterModel.clockInTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.GraphCounterModel.headerInTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.GraphCounterModel.machine`, `OAI.UniqueGamesTheorem.Foundations.Complexity.GraphCounterModel.program`, `OAI.UniqueGamesTheorem.Foundations.Complexity.GraphCounterPrefix.rawOutput`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineAffineLookup.finalTapes`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineAffineLookup.steps`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineAppendAt.appendTapes`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineAppendAt.firstTapes`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineAppendAt.secondTapes`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCanonicalOutput.Label`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCanonicalOutput.cleanupEntry`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCanonicalOutput.cleanupLabel`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCanonicalOutput.resetLabel`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCeilingPower.Tape.enumList`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCloudCount.Alphabet` and 278 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `PerfectCompleteness_Algebra_TensorBucketEvaluationLemmas`, `PerfectCompleteness_Construction_FactoredFunctionsLemmas`, `PerfectCompleteness_Decoding_CollisionAveragingLemmas`, `PerfectCompleteness_Foundations_GeometricPrefixSplit`, `PerfectCompleteness_Foundations_HierarchicalFrozenTablesLemmas`, `PerfectCompleteness_Foundations_NormalizationLemmas`, `PerfectCompleteness_Foundations_OutputAnnihilator`, `PerfectCompleteness_Foundations_SignedCostEnvelope`, `PerfectCompleteness_Foundations_SourceOddListsLemmas`, `PerfectCompleteness_Machines_ExactTargetOdometer`, `PerfectCompleteness_Machines_NormalizationEmitMachine`, `PerfectCompleteness_Machines_NormalizationReadMachine`, `PerfectCompleteness_Machines_SourceOccurrenceIndexMachine`, `PerfectCompleteness_Machines_SourceOccurrenceLoopMachine`, `PerfectCompleteness_Machines_TargetFinalizeMachine`, `PerfectCompleteness_Machines_TargetHeaderMachine`, `PerfectCompleteness_Machines_TargetTapeEnvelope`, `PerfectCompleteness_Machines_TupleInitializationMachine`, `PerfectCompleteness_Reduction_TargetFinalizeBound`, `PerfectCompleteness_Repetition_SourceAmplification`, `PerfectCompleteness_Sampling_RestrictionRowsLaw`, `UniqueGames_Foundations_ValueLemmas`, `UniqueGames_Machines_FinalCNFLoopLemmas`, `UniqueGames_Machines_FinalCNFMachineLemmas`, `UniqueGames_Machines_GraphCounterFinish`, `UniqueGames_Machines_GraphCounterModel`, `UniqueGames_Machines_GraphCounterStartLemmas`, `UniqueGames_Machines_MachineAppendAt`, `UniqueGames_Machines_MachineCanonicalOutputLemmas`, `UniqueGames_Machines_MachineCeilingPower`, `UniqueGames_Machines_MachineCloudCount`, `UniqueGames_Machines_MachineCloudPadding`, `UniqueGames_Machines_MachineCloudPrefix`, `UniqueGames_Machines_MachineCloudRankLemmas`, `UniqueGames_Machines_MachineCompositionLemmas`, `UniqueGames_Machines_MachineControlLemmas`, `UniqueGames_Machines_MachineDrainManyLemmas`, `UniqueGames_Machines_MachineExpanderFamilyBoundsLemmas`, `UniqueGames_Machines_MachineExpanderFamilyTapes`, `UniqueGames_Machines_MachineExpanderFamilyTransferLemmas`, `UniqueGames_Machines_MachineExpanderRowCleanup`, `UniqueGames_Machines_MachineExpanderRowDivision`, `UniqueGames_Machines_MachineExpanderTableProgramLemmas`, `UniqueGames_Machines_MachineFixedDivMod`, `UniqueGames_Machines_MachineInitialHeaders`, `UniqueGames_Machines_MachineLazyCodec`, `UniqueGames_Machines_MachineLazyRows`, `UniqueGames_Machines_MachineLemmas`, `UniqueGames_Machines_MachineLogCounter`, `UniqueGames_Machines_MachineLookupCore`, `UniqueGames_Machines_MachineLookupDiscard`, `UniqueGames_Machines_MachineLookupLemmas`, `UniqueGames_Machines_MachineOverlayRows`, `UniqueGames_Machines_MachinePaddedOverlay`, `UniqueGames_Machines_MachinePaddingRowsLemmas`, `UniqueGames_Machines_MachinePortReindex`, `UniqueGames_Machines_MachineProductGatherBoundsLemmas`, `UniqueGames_Machines_MachineRegularDummyRow`, `UniqueGames_Machines_MachineRegularInternalRow`, `UniqueGames_Machines_MachineRegularMetadata`, `UniqueGames_Machines_MachineRegularOriginalBodyBounds`, `UniqueGames_Machines_MachineRegularOwnerBody`, `UniqueGames_Machines_MachineRegularOwnerBodyBounds`, `UniqueGames_Machines_MachineRegularTable`, `UniqueGames_Machines_MachineRegularVertexBlock`, `UniqueGames_Machines_MachineRepeat`, `UniqueGames_Machines_MachineSubroutineLemmas`, `UniqueGames_Machines_MachineTransducerCopy`, `UniqueGames_Machines_MachineTupleOdometer`, `UniqueGames_Machines_MachineUnaryAffineAt`, `UniqueGames_Machines_MachineUnaryEqualityBit`, `UniqueGames_Machines_MachineUnaryLessAtLemmas`, `UniqueGames_Machines_MachineVertexPadding`, `UniqueGames_Machines_PoweringMachineFinish`, `UniqueGames_Machines_PoweringMachineLoop`, `UniqueGames_Machines_PoweringMachineRow`, `UniqueGames_Machines_PoweringMachineVertex`, `UniqueGames_Machines_PoweringPolynomialBudgetLemmas`, `UniqueGames_PCP_Addresses`, `UniqueGames_PCP_AlphabetGraphLemmas`, `UniqueGames_PCP_AlphabetReductionLemmas`, `UniqueGames_PCP_AlphabetRetractionLemmas`, `UniqueGames_PCP_AlphabetTableBoundsLemmas`, `UniqueGames_PCP_AmplificationIteration`, `UniqueGames_PCP_AssignmentTester`, `UniqueGames_PCP_Body`, `UniqueGames_PCP_ClauseVerifierLemmas`, `UniqueGames_PCP_CleanupLemmas`, `UniqueGames_PCP_CloudRoundingLemmas`, `UniqueGames_PCP_CodeComposition`, `UniqueGames_PCP_CompareLoop`, `UniqueGames_PCP_EmitRows`, `UniqueGames_PCP_Emitter`, `UniqueGames_PCP_ExpanderRowControlLemmas`, `UniqueGames_PCP_ExpanderTables`, `UniqueGames_PCP_ExpandersLemmas`, `UniqueGames_PCP_FinalBooleanVerifier`, `UniqueGames_PCP_FinalConstantsLemmas`, `UniqueGames_PCP_GenericGraphTables`, `UniqueGames_PCP_GraphTables`, `UniqueGames_PCP_InitialGraphLemmas`, `UniqueGames_PCP_InputLemmas`, `UniqueGames_PCP_LoopInitializationLemmas`, `UniqueGames_PCP_NameCompaction`, `UniqueGames_PCP_OverlayLemmas`, `UniqueGames_PCP_PoweringLabelsLemmas`, `UniqueGames_PCP_PoweringOpinionTables`, `UniqueGames_PCP_PoweringOpinionsLemmas`, `UniqueGames_PCP_PoweringPortReindexLemmas`, `UniqueGames_PCP_PoweringTableLayout`, `UniqueGames_PCP_PoweringTableSemanticsLemmas`, `UniqueGames_PCP_Preprocessing`, `UniqueGames_PCP_PreprocessingLazyWords`, `UniqueGames_PCP_PreprocessingPaddingOffsets`, `UniqueGames_PCP_PreprocessingPaddingWords`, `UniqueGames_PCP_PreprocessingRegularLoopWordsLemmas`, `UniqueGames_PCP_PreprocessingRegularSoundness`, `UniqueGames_PCP_PreprocessingTableSpectral`, `UniqueGames_PCP_PreprocessingTablesLemmas`, `UniqueGames_PCP_RawInitialMachineFinish`, `UniqueGames_PCP_RawInitialMachineLoopData`, `UniqueGames_PCP_RawInitialMachinePhases`, `UniqueGames_PCP_RawInitialMachineRows`, `UniqueGames_PCP_RawInitialMachineStart`, `UniqueGames_PCP_RawInitialTablesLemmas`, `UniqueGames_PCP_RuntimeModel`, `UniqueGames_PCP_Setup`, `UniqueGames_PCP_SourceMachine`, `UniqueGames_PCP_VertexPadding`, `UniqueGames_PCP_ZigzagGraphsLemmas`, `UniqueGames_Reduction_MachineTransducer`.
--
--   **Imports.** It imports the published bundle `Def_PerfectCompleteness`; the bundles `OAIQ252P000`, `OAIQ252P001` and `OAIQ252P002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ252P009`, `OAIQ252P010` and `OAIQ252P011`.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Computability.Encoding
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Disjoint
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Std
import Definitions.Def_PerfectCompleteness
import Definitions.Def_OAIQ252P000
import Definitions.Def_OAIQ252P001
import Definitions.Def_OAIQ252P002

section
-- module Solutions.OAIQ252_PC.Compat
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_ValueLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Question-dependent stochastic responses are derandomized by sampling complete
answer tables independently before the questions. The table law, marginal law,
and mixture identity are proved from finite products and sums. No derandomization
principle is assumed as a hypothesis or axiom.
-/

namespace UniqueGamesTheorem.Foundations.Games
open scoped BigOperators
noncomputable section

namespace FiniteDistribution
variable {Ω Γ Q A : Type*} [Fintype Ω] [Fintype Γ] [Fintype Q] [Fintype A]

/-- Independently sample one response for each possible private question. -/
def table [DecidableEq Q] (responses : Q → FiniteDistribution A) :
    FiniteDistribution (Q → A) := by
  classical
  exact
    { weight := fun answers => ∏ q, (responses q).weight (answers q)
      nonnegative := fun answers => Finset.prod_nonneg fun q _ =>
        (responses q).nonnegative (answers q)
      normalized := by
        rw [← Fintype.prod_sum]
        simp only [FiniteDistribution.normalized, Finset.prod_const_one] }

end FiniteDistribution

end
end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineControlLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Static renaming of labels and finite internal states. This does not execute
a data-copying phase and preserves every actual transition exactly. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineControl

open Turing.TM2

variable {K Λ Λ' σ σ' : Type} {Γ : K → Type}

variable [DecidableEq K]

def program (labels : Λ ≃ Λ') (states : σ ≃ σ') (source : Λ → Stmt Γ Λ σ) :
    Λ' → Stmt Γ Λ' σ' := fun l => statement labels states (source (labels.symm l))

/-- The renamed program is conjugate to the original transition function,
including the halted configuration. -/
theorem step_simulation (labels : Λ ≃ Λ') (states : σ ≃ σ')
    (source : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) :
    step (program labels states source) (configuration labels states c) =
      (step source c).map (configuration labels states) := by
  cases c with
  | mk l state tapes =>
    cases l with
    | none => rfl
    | some l =>
      change some (stepAux (statement labels states (source (labels.symm (labels l))))
        (states state) tapes) = _
      rw [Equiv.symm_apply_apply, stepAux_simulation]
      rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineControl

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineCompositionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.MachineAlphabetTransport

open Turing.TM2

variable {K Λ σ : Type} {Γ Δ : K → Type}

variable [DecidableEq K]

theorem step_simulation (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ) (start : Cfg Γ Λ σ) :
    step (program h source) (configuration h start) =
      (step source start).map (configuration h) := by
  cases h
  simp only [program_rfl, configuration_rfl, map_configuration_rfl]

/-- Exact conjugacy of every finite trace, including a `none` endpoint. -/
theorem trace_transport (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    (n : Nat) (start : Option (Cfg Γ Λ σ)) :
    (MachineComposition.advance (step (program h source)))^[n]
      (start.map (configuration h)) =
      ((MachineComposition.advance (step source))^[n] start).map (configuration h) := by
  cases h
  simp only [program_rfl, map_configuration_rfl]

theorem successfulTrace (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    (n : Nat) (start finish : Cfg Γ Λ σ)
    (trace : (MachineComposition.advance (step source))^[n] (some start) = some finish) :
    (MachineComposition.advance (step (program h source)))^[n]
      (some (configuration h start)) = some (configuration h finish) := by
  have transported := trace_transport h source n (some start)
  simpa only [Option.map_some, trace] using transported

end UniqueGamesTheorem.Foundations.Complexity.MachineAlphabetTransport

end

section

/-!
# Exact register-equivalence transport for finite-stack programs

The instruction translation reuses `MachineControl.statement` with unchanged
labels. An explicit register equivalence changes neither tapes nor labels.
The transition function, every iterated trace, and runtime witnesses are
transported in exactly the same number of transitions, including failed or
halted traces. No simulation premise is assumed.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineStateEquiv

open Turing.TM2

variable {K Λ σ τ : Type} {Γ : K → Type}

variable [DecidableEq K]

theorem stepAux_transport_symm (e : σ ≃ τ) (q : Stmt Γ Λ σ) (state : τ)
    (tapes : ∀ k, List (Γ k)) :
    stepAux (statement e q) state tapes =
      configuration e (stepAux q (e.symm state) tapes) := by
  simpa only [Equiv.apply_symm_apply] using
    stepAux_transport e q (e.symm state) tapes

end UniqueGamesTheorem.Foundations.Complexity.MachineStateEquiv

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineSubroutineLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.MachineSubroutine

open Turing

variable {K Λ Λ' σ : Type} {Γ : K → Type}

variable [DecidableEq K]

theorem trace (labels : Λ → Λ') (exit : Option Λ')
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' σ)
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    (steps : Nat) (a b : TM2.Cfg Γ Λ σ)
    (run : (MachineComposition.advance (TM2.step source))^[steps] (some a) = some b) :
    (MachineComposition.advance (TM2.step target))^[steps]
      (some (configuration labels exit a)) = some (configuration labels exit b) :=
  MachineComposition.liftSuccessfulTrace (TM2.step source) (TM2.step target)
    (configuration labels exit) (step_simulation labels exit source target atLabels) steps a b run

def execution (labels : Λ → Λ') (exit : Option Λ')
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' σ)
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    {a b : TM2.Cfg Γ Λ σ} {budget : Nat}
    (run : StateTransition.EvalsToInTime (TM2.step source) a (some b) budget) :
    StateTransition.EvalsToInTime (TM2.step target)
      (configuration labels exit a) (some (configuration labels exit b)) budget :=
  MachineComposition.liftExecutionInTime (TM2.step source) (TM2.step target)
    (configuration labels exit) (step_simulation labels exit source target atLabels) run

end UniqueGamesTheorem.Foundations.Complexity.MachineSubroutine

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity

def formulaEncoding : Computability.Encoding Target.Formula Bool where
  encode := formulaBits
  decode := decodeFormulaBits
  decode_encode := decodeFormulaBits_encoded

open Target

end UniqueGamesTheorem.Foundations.Complexity

end

section

/-!
Pure list specification for destructive zero-based unary table lookup.
These are serialization identities and bit-count bounds, not TM2 runtime
certificates. The connection to actual transitions is in `MachineLookup`.
-/
namespace UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec

/-- Literal split at the selected word. -/
theorem encoded_selected_split (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    encodeWords values = encodeWords (values.take i) ++ encodeWord value ++
      encodeWords (values.drop (i + 1)) := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, hv⟩
  have hs : values = values.take i ++ value :: values.drop (i + 1) := by
    calc
      values = values.take i ++ values.drop i := (List.take_append_drop i values).symm
      _ = _ := by rw [List.drop_eq_getElem_cons hi, hv]
  simpa only [encodeWords_append, encodeWords, List.append_assoc] using
    congrArg encodeWords hs

/-- This counts the bits through the selected word, capped at the whole table
when the index is invalid. It is not a machine step count. -/
def scannedBits (values : List Nat) (i : Nat) : Nat :=
  (encodeWords (values.take (i + 1))).length

theorem encoded_prefix_length_le (values : List Nat) (i : Nat) :
    (encodeWords (values.take i)).length ≤ (encodeWords values).length := by
  have hs : encodeWords (values.take i) ++ encodeWords (values.drop i) =
      encodeWords values := by
    rw [← encodeWords_append, List.take_append_drop]
  have hl := congrArg List.length hs
  simp only [List.length_append] at hl
  omega

theorem scannedBits_le (values : List Nat) (i : Nat) :
    scannedBits values i ≤ (encodeWords values).length :=
  encoded_prefix_length_le values (i + 1)

theorem scannedBits_of_some (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    scannedBits values i = (encodeWords (values.take i)).length + value + 1 := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, hv⟩
  simp [scannedBits, List.take_succ_eq_append_getElem hi, hv, encodeWords,
    Nat.add_assoc]

theorem selected_scan_length_le (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    (encodeWords (values.take i)).length + value + 1 ≤
      (encodeWords values).length := by
  rw [← scannedBits_of_some values i value h]
  exact scannedBits_le values i

theorem output_length_le (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    (encodeWord value).length ≤ (encodeWords values).length := by
  have hs := selected_scan_length_le values i value h
  rw [encodeWord_length]
  omega

theorem index_length_le (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    (encodeWord i).length ≤ (encodeWords values).length := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, _⟩
  have hp : i ≤ (encodeWords (values.take i)).length := by
    simp only [encodeWords_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
    omega
  have hs := selected_scan_length_le values i value h
  rw [encodeWord_length]
  omega

/-! Bounds on the proposed lookup recurrence. A separate machine proof must
identify these counts with actual transition traces. -/

/-- A uniform bound, including indices beyond the end of the table. -/
theorem steps_le_encoded_length_strong (values : List Nat) (i : Nat) :
    steps values i ≤ (encodeWords values).length + 2 * i + 2 := by
  induction values generalizing i with
  | nil => simp [steps, encodeWords]
  | cons n ns ih =>
    cases i with
    | zero =>
      simp only [steps, encodeWords, List.length_append, encodeWord_length]
      omega
    | succ i =>
      have ht := ih i
      simp only [steps, encodeWords, List.length_append, encodeWord_length]
      omega

/-- Successful lookup uses exactly the consumed table prefix, one guard per
skipped word, and the two final control steps. -/
theorem steps_eq_scannedBits_of_lt (values : List Nat) (i : Nat)
    (h : i < values.length) :
    steps values i = scannedBits values i + i + 2 := by
  induction values generalizing i with
  | nil => simp at h
  | cons n ns ih =>
    cases i with
    | zero => simp [steps, scannedBits, encodeWords, Nat.add_assoc]
    | succ i =>
      have ht := ih i (by simpa using h)
      simp only [scannedBits] at ht
      simp only [steps, scannedBits, List.take_succ_cons, encodeWords,
        List.length_append, encodeWord_length]
      omega

theorem steps_eq_scannedBits_of_some (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    steps values i = scannedBits values i + i + 2 := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, _⟩
  exact steps_eq_scannedBits_of_lt values i hi

/-- Linear in the combined encoded tape lengths. This is a bound for `steps`,
not yet a theorem about a concrete machine's execution. -/
theorem steps_le_input_encoding_size (values : List Nat) (i : Nat) :
    steps values i ≤ (encodeWords values).length + 2 * (encodeWord i).length := by
  have h := steps_le_encoded_length_strong values i
  rw [encodeWord_length]
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec

end

section

/-!
One actual TM2 transition tests and decrements a zero-delimited unary counter.
The guard peeks before branching: a true bit is popped, while a false delimiter
is retained. Both branches clear the one-bit register and preserve the ambient
state. There is no assumed execution trace or input-dependent finite program.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter

open Turing

variable {K Λ σ : Type} [DecidableEq K]

theorem counterTapes_other (counter other : K) (hne : other ≠ counter)
    (base : K → List Bool) (n : Nat) (suffix : List Bool) :
    counterTapes counter base n suffix other = base other := by
  simp [counterTapes, hne]

/-- Positive counters lose exactly one true bit; the delimiter and suffix
remain. Ambient state, unrelated tapes, and labels are accounted for explicitly. -/
theorem stepAux_succ (counter : K) (bodyLabel exitLabel : Λ)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.stepAux (guard counter bodyLabel exitLabel) (ambient, register)
      (counterTapes counter base (n + 1) suffix) =
      ⟨some bodyLabel, (ambient, none), counterTapes counter base n suffix⟩ := by
  simp [guard, TM2.stepAux, counterTapes, encodeWord, List.replicate_succ]

/-- A zero counter is inspected without removing its delimiter. -/
theorem stepAux_zero (counter : K) (bodyLabel exitLabel : Λ)
    (base : K → List Bool) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.stepAux (guard counter bodyLabel exitLabel) (ambient, register)
      (counterTapes counter base 0 suffix) =
      ⟨some exitLabel, (ambient, none), counterTapes counter base 0 suffix⟩ := by
  simp [guard, TM2.stepAux, counterTapes, encodeWord]

theorem guardStep_succ (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some guardLabel, (ambient, register), counterTapes counter base (n + 1) suffix⟩ =
      some ⟨some bodyLabel, (ambient, none), counterTapes counter base n suffix⟩ := by
  change some (TM2.stepAux (program guardLabel) (ambient, register)
    (counterTapes counter base (n + 1) suffix)) = _
  rw [atGuard, stepAux_succ]

theorem guardStep_zero (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some guardLabel, (ambient, register), counterTapes counter base 0 suffix⟩ =
      some ⟨some exitLabel, (ambient, none), counterTapes counter base 0 suffix⟩ := by
  change some (TM2.stepAux (program guardLabel) (ambient, register)
    (counterTapes counter base 0 suffix)) = _
  rw [atGuard, stepAux_zero]

/-- The positive branch executes in exactly one transition of the ambient program. -/
theorem guardTrace_succ (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some guardLabel, (ambient, register),
        counterTapes counter base (n + 1) suffix⟩) =
      some ⟨some bodyLabel, (ambient, none), counterTapes counter base n suffix⟩ := by
  simpa only [Function.iterate_one, MachineComposition.advance_some] using
    guardStep_succ counter guardLabel bodyLabel exitLabel program atGuard
      base n suffix ambient register

theorem guardTrace_zero (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some guardLabel, (ambient, register), counterTapes counter base 0 suffix⟩) =
      some ⟨some exitLabel, (ambient, none), counterTapes counter base 0 suffix⟩ := by
  simpa only [Function.iterate_one, MachineComposition.advance_some] using
    guardStep_zero counter guardLabel bodyLabel exitLabel program atGuard
      base suffix ambient register

def guardInTime_succ (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some guardLabel, (ambient, register), counterTapes counter base (n + 1) suffix⟩
      (some ⟨some bodyLabel, (ambient, none), counterTapes counter base n suffix⟩) 1 where
  steps := 1
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[1] _ = _
    exact guardTrace_succ counter guardLabel bodyLabel exitLabel program atGuard
      base n suffix ambient register
  steps_le_m := Nat.le_refl _

def guardInTime_zero (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some guardLabel, (ambient, register), counterTapes counter base 0 suffix⟩
      (some ⟨some exitLabel, (ambient, none), counterTapes counter base 0 suffix⟩) 1 where
  steps := 1
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[1] _ = _
    exact guardTrace_zero counter guardLabel bodyLabel exitLabel program atGuard
      base suffix ambient register
  steps_le_m := Nat.le_refl _

end UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter

end

section

/-!
Counted loops in one actual TM2 program. A unary guard is executed once before
each caller body and once more at zero. The caller supplies only individual
body traces, each returning to the guard with the same counter remainder.

Schedules are indexed by the remaining count: body `r` takes ambient state
`r + 1` to ambient state `r`. Consequently the run starts at index `n` and
ends at index zero. Bodies may change the ambient state and unprotected tapes.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCountedLoop

open Turing
open scoped BigOperators
open MachineUnaryCounter

variable {K Λ σ : Type} [DecidableEq K]

def guardConfiguration (counter : K) (guardLabel : Λ) (suffix : List Bool)
    (ambient : Nat → σ) (register : Nat → Option Bool)
    (base : Nat → K → List Bool) (n : Nat) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some guardLabel, (ambient n, register n), counterTapes counter (base n) n suffix⟩

def bodyConfiguration (counter : K) (bodyLabel : Λ) (suffix : List Bool)
    (ambient : Nat → σ) (base : Nat → K → List Bool) (n : Nat) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some bodyLabel, (ambient (n + 1), none), counterTapes counter (base (n + 1)) n suffix⟩

def exitConfiguration (counter : K) (exitLabel : Λ) (suffix : List Bool)
    (ambient : Nat → σ) (base : Nat → K → List Bool) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some exitLabel, (ambient 0, none), counterTapes counter (base 0) 0 suffix⟩

/-- The hypotheses are actual traces of the caller's body in the same program.
Both endpoints have the same unary remainder and unread suffix. -/
def BodyTraces (counter : K) (guardLabel bodyLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (suffix : List Bool) (ambient : Nat → σ) (register : Nat → Option Bool)
    (base : Nat → K → List Bool) (cost : Nat → Nat) (n : Nat) : Prop :=
  ∀ r, r < n →
    (MachineComposition.advance (TM2.step program))^[cost r]
      (some (bodyConfiguration counter bodyLabel suffix ambient base r)) =
      some (guardConfiguration counter guardLabel suffix ambient register base r)

/-- The loop trace is derived by composing each actual unary guard transition
with one supplied body trace. No whole-loop execution is assumed. -/
theorem loopTrace (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (suffix : List Bool) (ambient : Nat → σ) (register : Nat → Option Bool)
    (base : Nat → K → List Bool) (cost : Nat → Nat) (n : Nat)
    (bodyTraces : BodyTraces counter guardLabel bodyLabel program suffix
      ambient register base cost n) :
    (MachineComposition.advance (TM2.step program))^[totalSteps cost n]
      (some (guardConfiguration counter guardLabel suffix ambient register base n)) =
      some (exitConfiguration counter exitLabel suffix ambient base) := by
  revert bodyTraces
  induction n with
  | zero =>
      intro _
      simpa only [totalSteps_zero, guardConfiguration, exitConfiguration] using
        guardTrace_zero counter guardLabel bodyLabel exitLabel program atGuard
          (base 0) suffix (ambient 0) (register 0)
  | succ n ih =>
      intro bodyTraces
      rw [totalSteps_succ, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[totalSteps cost n + cost n]
        (TM2.step program
          ⟨some guardLabel, (ambient (n + 1), register (n + 1)),
            counterTapes counter (base (n + 1)) (n + 1) suffix⟩) = _
      rw [guardStep_succ counter guardLabel bodyLabel exitLabel program atGuard
        (base (n + 1)) n suffix (ambient (n + 1)) (register (n + 1)),
        Function.iterate_add_apply]
      change (MachineComposition.advance (TM2.step program))^[totalSteps cost n]
        ((MachineComposition.advance (TM2.step program))^[cost n]
          (some (bodyConfiguration counter bodyLabel suffix ambient base n))) = _
      rw [bodyTraces n (Nat.lt_succ_self n)]
      exact ih (fun r hr => bodyTraces r (Nat.lt_trans hr (Nat.lt_succ_self n)))

end UniqueGamesTheorem.Foundations.Complexity.MachineCountedLoop

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_FactoredFunctionsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.FactoredFunctionsDependent

open PerfectCompleteness.FactoredFunctions

variable {𝕜 Ω I : Type*} [Field 𝕜] {J : I → Type*}

theorem one_mem_dependentQuadraticSpan (lower : Ω → (i : I) → J i → 𝕜) :
    (1 : Ω → 𝕜) ∈ dependentQuadraticSpan lower :=
  Submodule.subset_span (Or.inl rfl)

theorem product_mem_dependentQuadraticSpan (lower : Ω → (i : I) → J i → 𝕜)
    (i : I) (t u : J i) :
    (fun x => lower x i t * lower x i u) ∈ dependentQuadraticSpan lower :=
  Submodule.subset_span (Or.inr ⟨i, t, u, rfl⟩)

end PerfectCompleteness.FactoredFunctionsDependent

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineInitialHeaders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Actual caller-program traces for non-destructive unary-prefix emission and
the two headers of the raw initial graph. Unread suffixes are never scanned.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineInitialHeaders

open Turing
open Reduction.MachineTransfer
open Reduction.MachineSubstitution
open MachineCopy

variable {K Λ σ : Type} [DecidableEq K]

/-- One transition emits a fixed literal word and enters the caller continuation. -/
theorem literalTrace (output : K) (word : List Bool) (label : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabel : program label = pushWord output word (exitAt output exit))
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some label, (ambient, register), base⟩) =
      some ⟨exit, (ambient, register),
        Function.update base output (word.reverse ++ base output)⟩ := by
  simp only [Function.iterate_one, MachineComposition.advance_some]
  change some (TM2.stepAux (program label) _ _) = _
  rw [atLabel, stepAux_pushWord]
  cases exit <;> rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineInitialHeaders

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineDrainManyLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual cleanup of a finite list of work tapes

Each list position supplies one fixed drain label. The finite-sequence theorem
composes the checked physical drains; neither the list nor a runtime tape index
is stored in the register. Repeated tape names are allowed. The cleanup bound
uses the lengths before cleanup, since draining can only shorten a tape.
-/

/-!
Preserved comparisons of actual field stacks and their finite equality profile.
All whole-word equalities below are specifications of finite-head comparison.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineFieldProfile

open Turing

section Transport
variable {K Λ σ τ : Type} [DecidableEq K]

omit [DecidableEq K] in
theorem statement_roundtrip (e : σ ≃ τ)
    (q : TM2.Stmt (fun _ : K => Bool) Λ τ) :
    MachineControl.statement id e (MachineControl.statement id e.symm q) = q := by
  induction q <;> simp_all [MachineControl.statement]

def copyStateEquiv (σ : Type) :
    ((σ × Bool × Option Bool) × Option Bool) ≃ MachineCompare.State σ where
  toFun s := (s.1.1, s.1.2.1, s.1.2.2, s.2)
  invFun s := ((s.1, s.2.1, s.2.2.1), s.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def normalState (ambient : σ) : MachineCompare.State σ := (ambient, false, none, none)

def copyStatement (q : TM2.Stmt (fun _ : K => Bool) Λ
    ((σ × Bool × Option Bool) × Option Bool)) :
    TM2.Stmt (fun _ : K => Bool) Λ (MachineCompare.State σ) :=
  MachineControl.statement id (copyStateEquiv σ) q

end Transport

end UniqueGamesTheorem.Foundations.Complexity.MachineFieldProfile

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_AssignmentTester
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.EmptyContext.equation_second_eq_third _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.EmptyContext.pairedEquations_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHonest.taggedAssignment_left _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHonest.taggedAssignment_right _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.canonicalInput_half _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.extendRestricted_valid _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.restrictQuery_extendRestricted _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.card_event _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inl_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inr_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_address _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_cube _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_dart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_event _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_localEvent _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_pairCube _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_vertex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.inputCoordinateEquiv_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_edgeAddress_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_vertexAddress_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Queries.mask_idempotent _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.averagingOperator_cayleyGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.coefficient_zeroFrequency _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.cubeXor_zeroFrequency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! A concrete constant-query proximity tester for a finite relation.

The proof oracle is a Boolean function on the Boolean functions on the finite
set of legal assignments. The tests are BLR linearity, self-corrected AND,
self-corrected unit, and comparison with a queried input coordinate.
The oracle's size depends exponentially on the number of legal assignments;
this is a fixed-relation construction, not a polynomial-size tester for an
arbitrary input formula. All tests below are explicit finite expectations.
-/

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.AssignmentTester

open UniqueGamesTheorem.Foundations.Hastad
open scoped BigOperators
open Finset

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem disagree_eq (a b : Bool) :
    disagree a b = (1 - bitSign a * bitSign b) / 2 := by
  cases a <;> cases b <;> norm_num [disagree, bitSign]

omit [Fintype A] [DecidableEq A] in
theorem cubeXor_comm (f g : Cube A) : cubeXor f g = cubeXor g f := by
  funext a
  simp [cubeXor, Bool.xor_comm]

theorem expect_cubeXor (F : Cube A → ℝ) (g : Cube A) :
    (𝔼 f, F (cubeXor f g)) = 𝔼 f, F f := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  congr 1
  refine Finset.sum_bij (fun f _ => cubeXor f g) ?_ ?_ ?_ ?_
  · intro f _
    exact Finset.mem_univ _
  · intro f _ h _ heq
    have hh := congrArg (fun x => cubeXor x g) heq
    simpa only [cubeXor_right_twice] using hh
  · intro f _
    exact ⟨cubeXor f g, Finset.mem_univ _, cubeXor_right_twice f g⟩
  · intro f _
    rfl

theorem distance_parity (F : Cube A → Bool) (s : Cube A) :
    distance F (parity s) = (1 - coefficient (fun f => bitSign (F f)) s) / 2 := by
  unfold distance
  simp_rw [disagree_eq, bitSign_parity, div_eq_mul_inv,
    ← Finset.expect_mul, Finset.expect_sub_distrib]
  simp only [Fintype.expect_const]
  rfl

def blrReject (F : Cube A → Bool) : ℝ :=
  𝔼 f, 𝔼 g, disagree (F f ^^ F g) (F (cubeXor f g))

theorem blrReject_nonneg (F : Cube A → Bool) : 0 ≤ blrReject F := by
  apply Finset.expect_nonneg
  intro f _
  apply Finset.expect_nonneg
  intro g _
  exact disagree_nonneg _ _

def selfCorrect (F : Cube A → Bool) (x r : Cube A) : Bool :=
  F r ^^ F (cubeXor r x)

theorem parity_selfCorrect (s x r : Cube A) :
    (parity s r ^^ parity s (cubeXor r x)) = parity s x := by
  rw [parity_xor]
  cases parity s r <;> cases parity s x <;> rfl

/-- The two actual oracle queries recover the parity at every requested x. -/
theorem selfCorrect_error (F : Cube A → Bool) (s x : Cube A) :
    (𝔼 r, disagree (selfCorrect F x r) (parity s x)) ≤ 2 * distance F (parity s) := by
  have hle (r : Cube A) :
      disagree (selfCorrect F x r) (parity s x) ≤
      disagree (F r) (parity s r) +
        disagree (F (cubeXor r x)) (parity s (cubeXor r x)) := by
    rw [← parity_selfCorrect s x r]
    exact disagree_xor_le _ _ _ _
  have h := Finset.expect_le_expect (s := Finset.univ) (fun r _ => hle r)
  rw [Finset.expect_add_distrib,
    expect_cubeXor (fun r => disagree (F r) (parity s r)) x] at h
  change _ ≤ distance F (parity s) + distance F (parity s) at h
  linarith

theorem expect_flipAt (F : Cube A → ℝ) (i : A) :
    (𝔼 f, F (flipAt i f)) = 𝔼 f, F f := by
  simp_rw [flipAt_eq_xor]
  exact expect_cubeXor F _

def andLawFailure (s f g : Cube A) : Bool :=
  parity s (cubeAnd f g) ^^ (parity s f && parity s g)

theorem andLawFailure_flipAt_second (s : Cube A) (i : A) (f g : Cube A)
    (hi : s i = true) :
    andLawFailure s f (flipAt i g) =
      (andLawFailure s f g ^^ (parity s f ^^ f i)) := by
  have hAnd : cubeAnd f (flipAt i g) =
      (if f i then flipAt i (cubeAnd f g) else cubeAnd f g) := by
    funext a
    by_cases ha : a = i
    · subst a
      cases hfi : f i <;> simp [cubeAnd, flipAt, hfi]
    · cases hfi : f i <;> simp [cubeAnd, flipAt, ha]
  have hg := parity_flipAt s i g hi
  have hfg := parity_flipAt s i (cubeAnd f g) hi
  cases hfi : f i <;> cases hf : parity s f <;>
    cases hg₀ : parity s g <;> cases ha : parity s (cubeAnd f g) <;>
    simp [andLawFailure, hAnd, hg, hfg, hfi, hf, hg₀, ha]

/-- Every parity involving two or more distinct coordinates violates Boolean
AND with probability at least one quarter under two independent queries. -/
theorem parity_and_rejection (s : Cube A) (i j : A)
    (hi : s i = true) (hj : s j = true) (hij : i ≠ j) :
    (1 : ℝ) / 4 ≤ 𝔼 f, 𝔼 g, truth (andLawFailure s f g) := by
  have hpoint (f g : Cube A) : (1 : ℝ) ≤
      truth (andLawFailure s f g) + truth (andLawFailure s f (flipAt i g)) +
      truth (andLawFailure s (flipAt j f) g) +
      truth (andLawFailure s (flipAt j f) (flipAt i g)) := by
    rw [andLawFailure_flipAt_second s i f g hi,
      andLawFailure_flipAt_second s i (flipAt j f) g hi]
    have hD : (parity s (flipAt j f) ^^ (flipAt j f) i) =
        !(parity s f ^^ f i) := by
      rw [parity_flipAt s j f hj]
      simp only [flipAt, ite_eq_right hij]
      cases hf : parity s f <;> cases hfi : f i <;> simp
    rw [hD]
    exact four_truth_lower _ _ _
  have havg := Finset.expect_le_expect (s := Finset.univ) (fun f _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun g _ => hpoint f g))
  simp only [Finset.expect_add_distrib, Fintype.expect_const] at havg
  have hinner (f : Cube A) :
      (𝔼 g, truth (andLawFailure s f (flipAt i g))) =
        𝔼 g, truth (andLawFailure s f g) :=
    expect_flipAt (fun g => truth (andLawFailure s f g)) i
  have houter : (𝔼 f, 𝔼 g, truth (andLawFailure s (flipAt j f) g)) =
      𝔼 f, 𝔼 g, truth (andLawFailure s f g) :=
    expect_flipAt (fun f => 𝔼 g, truth (andLawFailure s f g)) j
  simp only [hinner, houter] at havg
  linarith

/-- Six oracle queries, using three independent self-correction masks. -/
def andReject (F : Cube A → Bool) : ℝ :=
  𝔼 f, 𝔼 g, 𝔼 r₀, 𝔼 r₁, 𝔼 r₂,
    disagree (selfCorrect F (cubeAnd f g) r₀)
      (selfCorrect F f r₁ && selfCorrect F g r₂)

def unitReject (F : Cube A → Bool) : ℝ :=
  𝔼 r, disagree (selfCorrect F (fun _ => true) r) true

variable {K : Type*} [Fintype K] [Nonempty K]

/-- One original input query and two proof-oracle queries. -/
def inputReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) : ℝ :=
  𝔼 k, 𝔼 r, disagree (σ k) (selfCorrect F (fun a => label a k) r)

def testerReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) : ℝ :=
  (blrReject F + andReject F + unitReject F + inputReject label σ F) / 4

theorem andReject_nonneg (F : Cube A → Bool) : 0 ≤ andReject F := by
  apply Finset.expect_nonneg
  intro f _
  apply Finset.expect_nonneg
  intro g _
  apply Finset.expect_nonneg
  intro r₀ _
  apply Finset.expect_nonneg
  intro r₁ _
  apply Finset.expect_nonneg
  intro r₂ _
  exact disagree_nonneg _ _

theorem unitReject_nonneg (F : Cube A → Bool) : 0 ≤ unitReject F := by
  apply Finset.expect_nonneg
  intro r _
  exact disagree_nonneg _ _

omit [Nonempty K] in
theorem inputReject_nonneg (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) :
    0 ≤ inputReject label σ F := by
  apply Finset.expect_nonneg
  intro k _
  apply Finset.expect_nonneg
  intro r _
  exact disagree_nonneg _ _

theorem andReject_transfer (F : Cube A → Bool) (s : Cube A) :
    (𝔼 f, 𝔼 g, truth (andLawFailure s f g)) ≤
      andReject F + 6 * distance F (parity s) := by
  have hlocal (f g : Cube A) : truth (andLawFailure s f g) ≤
      (𝔼 r₀, 𝔼 r₁, 𝔼 r₂,
        disagree (selfCorrect F (cubeAnd f g) r₀)
          (selfCorrect F f r₁ && selfCorrect F g r₂)) +
      6 * distance F (parity s) := by
    have hp (r₀ r₁ r₂ : Cube A) := and_disagree_transfer
      (parity s (cubeAnd f g)) (parity s f) (parity s g)
      (selfCorrect F (cubeAnd f g) r₀) (selfCorrect F f r₁) (selfCorrect F g r₂)
    have havg := Finset.expect_le_expect (s := Finset.univ) (fun r₀ _ =>
      Finset.expect_le_expect (s := Finset.univ) (fun r₁ _ =>
        Finset.expect_le_expect (s := Finset.univ) (fun r₂ _ => hp r₀ r₁ r₂)))
    simp only [Finset.expect_add_distrib, Fintype.expect_const] at havg
    have h₀ := selfCorrect_error F s (cubeAnd f g)
    have h₁ := selfCorrect_error F s f
    have h₂ := selfCorrect_error F s g
    rw [andLawFailure, truth_xor]
    linarith
  have h := Finset.expect_le_expect (s := Finset.univ) (fun f _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun g _ => hlocal f g))
  simpa only [Finset.expect_add_distrib, Fintype.expect_const, andReject] using h

theorem parity_zero (f : Cube A) : parity (fun _ => false) f = false := by
  apply bitSign_injective
  rw [bitSign_parity]
  simp [walsh, bitSign]

theorem unitReject_zero_parity (F : Cube A → Bool) :
    1 - 2 * distance F (parity (fun _ => false)) ≤ unitReject F := by
  have herr := selfCorrect_error F (fun _ => false) (fun _ => true)
  simp only [parity_zero] at herr
  have heq : unitReject F +
      (𝔼 r, disagree (selfCorrect F (fun _ => true) r) false) = 1 := by
    unfold unitReject
    rw [← Finset.expect_add_distrib]
    have hp (b : Bool) : disagree b true + disagree b false = 1 := by
      cases b <;> norm_num [disagree]
    simp only [hp, Fintype.expect_const]
  linarith

theorem parity_singleMask_eval (a : A) (f : Cube A) :
    parity (singleMask a) f = f a := by
  apply bitSign_injective
  rw [bitSign_parity, walsh_symm, walsh_singleMask]

theorem inputReject_transfer (label : A → K → Bool) (σ : K → Bool)
    (F : Cube A → Bool) (a : A) :
    distance σ (label a) ≤ inputReject label σ F +
      2 * distance F (parity (singleMask a)) := by
  have hlocal (k : K) : disagree (σ k) (label a k) ≤
      (𝔼 r, disagree (σ k) (selfCorrect F (fun a => label a k) r)) +
        2 * distance F (parity (singleMask a)) := by
    have hp (r : Cube A) := disagree_triangle (σ k)
      (selfCorrect F (fun a => label a k) r) (label a k)
    have havg := Finset.expect_le_expect (s := Finset.univ) (fun r _ => hp r)
    simp only [Fintype.expect_const, Finset.expect_add_distrib] at havg
    have herr := selfCorrect_error F (singleMask a) (fun a => label a k)
    simp only [parity_singleMask_eval] at herr
    linarith
  have h := Finset.expect_le_expect (s := Finset.univ) (fun k _ => hlocal k)
  simpa only [Finset.expect_add_distrib, Fintype.expect_const, inputReject, distance] using h

omit [Fintype A] [DecidableEq A] in
theorem selfCorrect_dictator (a : A) (x r : Cube A) :
    selfCorrect (fun f => f a) x r = x a := by
  change (r a ^^ (r a ^^ x a)) = x a
  cases r a <;> cases x a <;> rfl

def oracleAnswer (σ : K → Bool) (F : Cube A → Bool) : K ⊕ Cube A → Bool :=
  Sum.elim σ F

def eventReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (kind : Fin 4) (k : K) (f g r₀ r₁ r₂ : Cube A) : ℝ :=
  truth (!(eventAccepts kind (fun slot =>
    oracleAnswer σ F (eventQueries label kind k f g r₀ r₁ r₂ slot))))

section

omit [Fintype A] [DecidableEq A] [Fintype K] [Nonempty K]

theorem eventReject_blr (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventReject label σ F 0 k f g r₀ r₁ r₂ =
      disagree (F f ^^ F g) (F (cubeXor f g)) := by
  simp [eventReject, eventAccepts, eventQueries, oracleAnswer, truth_not_decide_eq]

theorem eventReject_and (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventReject label σ F 1 k f g r₀ r₁ r₂ =
      disagree (selfCorrect F (cubeAnd f g) r₀)
        (selfCorrect F f r₁ && selfCorrect F g r₂) := by
  simp [eventReject, eventAccepts, eventQueries, oracleAnswer,
    truth_not_decide_eq, selfCorrect]

end

/-- One finite uniform sample space for the executable six-address test. -/
def explicitTesterReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) : ℝ :=
  𝔼 kind : Fin 4, 𝔼 k, 𝔼 f, 𝔼 g, 𝔼 r₀, 𝔼 r₁, 𝔼 r₂,
    eventReject label σ F kind k f g r₀ r₁ r₂

end UniqueGamesTheorem.Foundations.PCP.AssignmentTester

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_CodeComposition
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.EmptyContext.equation_second_eq_third _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.EmptyContext.pairedEquations_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHonest.taggedAssignment_left _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHonest.taggedAssignment_right _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.canonicalInput_half _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.extendRestricted_valid _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.restrictQuery_extendRestricted _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.card_event _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inl_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inr_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_address _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_cube _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_dart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_event _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_localEvent _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_pairCube _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_vertex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.inputCoordinateEquiv_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_edgeAddress_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_vertexAddress_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Queries.mask_idempotent _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AssignmentTester.cubeXor_right_twice _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AssignmentTester.flipAt_twice _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.averagingOperator_cayleyGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.coefficient_zeroFrequency _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.cubeXor_zeroFrequency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.CodeComposition

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Hastad

theorem disagreement_eq_sign (a b : Bool) :
    disagreement a b = (1 - bitSign a * bitSign b) / 2 := by
  cases a <;> cases b <;> norm_num [disagreement, bitSign]

theorem relativeDistance_eq_sign {X : Type*} [Fintype X] [Nonempty X]
    (f g : X → Bool) :
    relativeDistance f g = (1 - 𝔼 x, bitSign (f x) * bitSign (g x)) / 2 := by
  simp only [relativeDistance, disagreement_eq_sign]
  rw [← Finset.expect_div, Finset.expect_sub_distrib]
  simp

def singletonMask {A : Type*} [DecidableEq A] (a : A) : Cube A :=
  fun i => decide (i = a)

theorem walsh_singletonMask {A : Type*} [Fintype A] [DecidableEq A]
    (a : A) (x : Cube A) : walsh (singletonMask a) x = bitSign (x a) := by
  classical
  unfold walsh singletonMask
  rw [Finset.prod_eq_single a]
  · simp
  · intro b _ hba
    simp [hba, bitSign]
  · simp

theorem singletonMask_ne {A : Type*} [DecidableEq A] {a b : A} (hab : a ≠ b) :
    singletonMask a ≠ singletonMask b := by
  intro h
  have he := congrFun h a
  simp [singletonMask, hab] at he

theorem exists_nearest {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (f : Cube A → Bool) :
    ∃ a : A, ∀ b : A, relativeDistance f (codeword a) ≤ relativeDistance f (codeword b) := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.exists_min_image Finset.univ
    (fun a : A => relativeDistance f (codeword a)) Finset.univ_nonempty
  exact ⟨a, fun b => ha b (Finset.mem_univ b)⟩

/-- Classical choice is used only for the soundness analysis, not the output algorithm. -/
def nearest {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] (f : Cube A → Bool) : A :=
  Classical.choose (exists_nearest f)

theorem nearest_minimal {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (f : Cube A → Bool) (a : A) :
    relativeDistance f (codeword (nearest f)) ≤ relativeDistance f (codeword a) :=
  Classical.choose_spec (exists_nearest f) a

theorem pairWord_distance {X : Type*} [Fintype X] [Nonempty X]
    (left right left' right' : X → Bool) :
    relativeDistance (pairWord left right) (pairWord left' right') =
      (relativeDistance left left' + relativeDistance right right') / 2 := by
  classical
  simp [relativeDistance, Fintype.expect_eq_sum_div_card, Fintype.card_prod,
    Fintype.sum_prod_type, pairWord]
  ring

end UniqueGamesTheorem.Foundations.PCP.CodeComposition

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_AlphabetReductionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetRetraction.edgeSatisfied_pullback _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetRetraction.rejectionCount_pullback _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.DegreeReplacement.padded_satisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.DegreeReplacement.padded_satisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.acceptsAt_graphRows _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.reverseAt_graphRows _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_accepts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph_rejectionCount _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GraphTables.acceptsAt_graphRows _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GraphTables.reverseAt_graphRows _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GraphTables.semantics_accepts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GraphTables.semantics_ofGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GraphTables.semantics_ofGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GraphTables.semantics_ofGraph_rejectionCount _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GraphTables.semantics_ofGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GraphTables.semantics_ofGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GraphTables.semantics_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GraphTables.semantics_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_head _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_reverse_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_reverse_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.paddedG_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The explicit assignment tester applied to the encoded satisfying pairs of an
actual finite edge predicate.  The resulting soundness loss is independent of
the alphabet size.  Uniform padding of the finite sample space and assembly of
the global incidence graph are separate constructions.
-/

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetReduction

open UniqueGamesTheorem.Foundations.Hastad
open CodeComposition

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def edgeTesterReject (accepts : A → A → Bool) (left right : Cube A → Bool)
    (F : Cube (LegalPair accepts) → Bool) : ℝ :=
  AssignmentTester.explicitTesterReject (pairEncoding accepts) (pairWord left right) F

end UniqueGamesTheorem.Foundations.PCP.AlphabetReduction

end

end

section

namespace UniqueGamesTheorem.Foundations.PCP

namespace ConstraintGraph

variable {V E A : Type*}

def Satisfiable (G : ConstraintGraph V E A) : Prop :=
  ∃ labeling : V → A, ∀ e, G.edgeSatisfied labeling e = true

theorem mem_rejectedDarts [Fintype E] (G : ConstraintGraph V E A)
    (labeling : V → A) (e : E) :
    e ∈ G.rejectedDarts labeling ↔ G.edgeSatisfied labeling e = false := by
  simp [rejectedDarts]

theorem rejected_exists_of_not_satisfiable (G : ConstraintGraph V E A)
    (unsat : ¬ G.Satisfiable) (labeling : V → A) :
    ∃ e, G.edgeSatisfied labeling e = false := by
  classical
  by_contra none
  apply unsat
  refine ⟨labeling, fun e => ?_⟩
  have notFalse : G.edgeSatisfied labeling e ≠ false := by
    intro h
    exact none ⟨e, h⟩
  cases h : G.edgeSatisfied labeling e <;> simp_all

theorem rejectionCount_positive [Fintype E] (G : ConstraintGraph V E A)
    (unsat : ¬ G.Satisfiable) (labeling : V → A) :
    1 ≤ G.rejectionCount labeling := by
  obtain ⟨e, he⟩ := G.rejected_exists_of_not_satisfiable unsat labeling
  exact Finset.one_le_card.mpr ⟨e, (G.mem_rejectedDarts labeling e).mpr he⟩

end ConstraintGraph

end UniqueGamesTheorem.Foundations.PCP

end

section

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.ConstraintGraph

variable {V E A : Type*}

section Minimum

variable [Fintype V] [Fintype E] [Fintype A] [Nonempty A]

def rejectionCounts (G : ConstraintGraph V E A) : Finset Nat := by
  classical
  exact Finset.univ.image G.rejectionCount

theorem rejectionCounts_nonempty (G : ConstraintGraph V E A) :
    G.rejectionCounts.Nonempty := by
  classical
  exact Finset.univ_nonempty.image G.rejectionCount

def minimumRejections (G : ConstraintGraph V E A) : Nat :=
  G.rejectionCounts.min' G.rejectionCounts_nonempty

theorem minimumRejections_le (G : ConstraintGraph V E A) (labeling : V → A) :
    G.minimumRejections ≤ G.rejectionCount labeling := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨labeling, Finset.mem_univ _, rfl⟩)

theorem exists_minimizer (G : ConstraintGraph V E A) :
    ∃ labeling : V → A, G.rejectionCount labeling = G.minimumRejections := by
  classical
  have h := Finset.min'_mem G.rejectionCounts G.rejectionCounts_nonempty
  obtain ⟨labeling, _, heq⟩ := Finset.mem_image.mp h
  exact ⟨labeling, heq⟩

omit [Fintype V] [Fintype A] [Nonempty A] in
theorem rejectionCount_eq_zero_iff (G : ConstraintGraph V E A) (labeling : V → A) :
    G.rejectionCount labeling = 0 ↔ ∀ e, G.edgeSatisfied labeling e = true := by
  classical
  constructor
  · intro h e
    have hempty : G.rejectedDarts labeling = ∅ := Finset.card_eq_zero.mp h
    cases he : G.edgeSatisfied labeling e with
    | false =>
        have hm := (G.mem_rejectedDarts labeling e).mpr he
        rw [hempty] at hm
        simp at hm
    | true => rfl
  · intro h
    simp [rejectionCount, rejectedDarts, h]

theorem minimumRejections_eq_zero_iff (G : ConstraintGraph V E A) :
    G.minimumRejections = 0 ↔ G.Satisfiable := by
  constructor
  · intro h
    obtain ⟨labeling, heq⟩ := G.exists_minimizer
    exact ⟨labeling, (G.rejectionCount_eq_zero_iff labeling).mp (heq.trans h)⟩
  · rintro ⟨labeling, h⟩
    have hc := (G.rejectionCount_eq_zero_iff labeling).mpr h
    exact Nat.eq_zero_of_le_zero (hc ▸ G.minimumRejections_le labeling)

def gap (G : ConstraintGraph V E A) : ℝ :=
  (G.minimumRejections : ℝ) / Fintype.card E

theorem gap_nonnegative (G : ConstraintGraph V E A) : 0 ≤ G.gap :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem gap_eq_zero_iff [Nonempty E] (G : ConstraintGraph V E A) :
    G.gap = 0 ↔ G.Satisfiable := by
  have he : (Fintype.card E : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [gap, div_eq_zero_iff, he, or_false, Nat.cast_eq_zero]
  exact G.minimumRejections_eq_zero_iff

/-- A lower bound on the actual minimum is exactly the universal count bound. -/
theorem le_gap_iff [Nonempty E] (G : ConstraintGraph V E A) (ε : ℝ) :
    ε ≤ G.gap ↔ ∀ labeling : V → A,
      ε * Fintype.card E ≤ (G.rejectionCount labeling : ℝ) := by
  have he : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  change ε ≤ (G.minimumRejections : ℝ) / Fintype.card E ↔ _
  rw [le_div_iff₀ he]
  constructor
  · intro h labeling
    exact h.trans (Nat.cast_le.mpr (G.minimumRejections_le labeling))
  · intro h
    obtain ⟨labeling, heq⟩ := G.exists_minimizer
    simpa only [heq] using h labeling

theorem inverse_card_le_gap_of_unsatisfiable [Nonempty E]
    (G : ConstraintGraph V E A) (unsat : ¬ G.Satisfiable) :
    1 / (Fintype.card E : ℝ) ≤ G.gap := by
  apply (G.le_gap_iff _).mpr
  intro labeling
  have he : (Fintype.card E : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : (1 : ℝ) ≤ (G.rejectionCount labeling : ℝ) := by
    exact_mod_cast G.rejectionCount_positive unsat labeling
  simpa only [div_mul_cancel₀ _ he] using hc

end Minimum

section Reindex

variable {W D B : Type*}

theorem reindex_edgeSatisfied (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B)
    (labeling : V → A) (e : E) :
    (G.reindex vertices darts labels).edgeSatisfied (labelingEquiv vertices labels labeling)
      (darts e) = G.edgeSatisfied labeling e := by
  simp [reindex, labelingEquiv, edgeSatisfied, head, Equiv.trans_apply]

theorem reindex_rejectionCount [Fintype E] [Fintype D] (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B) (labeling : V → A) :
    (G.reindex vertices darts labels).rejectionCount (labelingEquiv vertices labels labeling) =
      G.rejectionCount labeling := by
  classical
  unfold rejectionCount
  symm
  apply Finset.card_bij (fun e _ => darts e)
  · intro e he
    rw [mem_rejectedDarts, reindex_edgeSatisfied]
    exact (G.mem_rejectedDarts labeling e).mp he
  · intro e _ f _ h
    exact darts.injective h
  · intro d hd
    refine ⟨darts.symm d, ?_, darts.apply_symm_apply d⟩
    rw [mem_rejectedDarts]
    rw [← reindex_edgeSatisfied G vertices darts labels labeling (darts.symm d)]
    rw [darts.apply_symm_apply]
    exact (mem_rejectedDarts _ _ _).mp hd

variable [Fintype V] [Fintype E] [Fintype A] [Nonempty A]
  [Fintype W] [Fintype D] [Fintype B] [Nonempty B]

omit [Nonempty A] [Nonempty B] in
theorem rejectionCounts_reindex (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B) :
    (G.reindex vertices darts labels).rejectionCounts = G.rejectionCounts := by
  classical
  ext n
  simp only [rejectionCounts, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨labeling, hn⟩
    refine ⟨(labelingEquiv vertices labels).symm labeling, ?_⟩
    rw [← reindex_rejectionCount G vertices darts labels,
      Equiv.apply_symm_apply]
    exact hn
  · rintro ⟨labeling, hn⟩
    refine ⟨labelingEquiv vertices labels labeling, ?_⟩
    rw [reindex_rejectionCount]
    exact hn

theorem minimumRejections_reindex (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B) :
    (G.reindex vertices darts labels).minimumRejections = G.minimumRejections := by
  unfold minimumRejections
  simp only [rejectionCounts_reindex]

theorem satisfiable_reindex (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B) :
    (G.reindex vertices darts labels).Satisfiable ↔ G.Satisfiable := by
  rw [← minimumRejections_eq_zero_iff, minimumRejections_reindex,
    minimumRejections_eq_zero_iff]

end Reindex

end UniqueGamesTheorem.Foundations.PCP.ConstraintGraph

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_ClauseVerifierLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP

open Target

def honestAnswer {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) : ClauseAnswer :=
  ⟨assignment clause[0].variableIndex, assignment clause[1].variableIndex,
   assignment clause[2].variableIndex⟩

theorem honest_satisfies {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) :
    localSatisfies clause (honestAnswer clause assignment) = clause.eval assignment := rfl

theorem honest_answerAt {n : Nat} (clause : Clause n) (assignment : Fin n → Bool)
    (slot : Slot) : answerAt (honestAnswer clause assignment) slot =
      assignment (nameAt clause slot) := by
  cases slot <;> rfl

end UniqueGamesTheorem.Foundations.PCP

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_NameCompaction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
An explicit name compaction for finite three-literal CNF formulas. Only the
occurring names are scanned: the declared variable count is never enumerated.
Both assignment transports preserve every clause evaluation and therefore
every finite clause-score gap. The encoding bound is a size theorem; a machine
running-time bound and the constant-gap PCP construction remain separate.
-/

namespace UniqueGamesTheorem.Foundations.PCP.NameCompaction

open UniqueGamesTheorem.Foundations.Target

def evaluationList (F : Formula) (A : Fin F.variables → Bool) : List Bool :=
  F.clauses.map (fun c => c.eval A)

def failedCount (F : Formula) (A : Fin F.variables → Bool) : Nat :=
  (evaluationList F A).count false

end UniqueGamesTheorem.Foundations.PCP.NameCompaction

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_InitialGraphLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetRetraction.edgeSatisfied_pullback _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetRetraction.rejectionCount_pullback _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.acceptsAt_graphRows _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.reverseAt_graphRows _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_accepts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph_rejectionCount _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GraphTables.acceptsAt_graphRows _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GraphTables.reverseAt_graphRows _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GraphTables.semantics_accepts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GraphTables.semantics_ofGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GraphTables.semantics_ofGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GraphTables.semantics_ofGraph_rejectionCount _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GraphTables.semantics_ofGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GraphTables.semantics_ofGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GraphTables.semantics_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GraphTables.semantics_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_reverse_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_reverse_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.paddedG_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The initial finite constraint graph of an arbitrary concrete 3CNF formula.
Clause and variable vertices use one eight-element alphabet. Variable labels
are the canonical triples `(bit, false, false)`; clause labels are arbitrary
triples. Every incidence has two directed darts, including repeated names.
A tautological dummy loop keeps the graph nonempty for empty formulas.

Name compaction precedes the public construction. The resulting vertex count
is at most `4*m+1`, and the dart count is exactly `6*m+1`. Unsatisfiability gives
an inverse-size gap, not a constant gap. No PCP theorem is assumed or claimed.
-/

namespace UniqueGamesTheorem.Foundations.PCP.InitialGraph

open Target

def variableLabel (value : Bool) : Label := (value, false, false)

end UniqueGamesTheorem.Foundations.PCP.InitialGraph

end

section

/-! Reversible regular port graphs and their actual finite walks. Vertices may
repeat; loops and parallel edges retain their distinct ports. The rotation
map sends an outgoing dart to its arrival dart and is an involution. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringWalks

variable {V D : Type*}

def headTailEquiv (V D : Type*) (n : Nat) :
    Walk V D (n + 1) ≃ (Walk V D n × D) where
  toFun w := ((w.1, fun j => w.2 j.succ), w.2 0)
  invFun z := (z.1.1, Fin.cases z.2 z.1.2)
  left_inv w := by
    apply Prod.ext
    · rfl
    · funext j
      exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

/-- Isolate any actual path edge. Previously traversed ports are replaced by
their arrival ports, so the change of coordinates remains invertible. -/
def pivotEquiv (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) →
      (Walk V D (n + 1) ≃ (Edge V D × (Fin n → D)))
  | 0, _ => splitHead V D 0
  | n + 1, k => Fin.cases (splitHead V D (n + 1))
      (fun j => (rotateHead G (n + 1)).trans
        ((headTailEquiv V D (n + 1)).trans
          ((Equiv.prodCongr (pivotEquiv G n j) (Equiv.refl D)).trans
            (headTailEquiv (Edge V D) D n).symm))) k

theorem pivotEquiv_fst (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 1)),
      (pivotEquiv G n k w).1 = edgeAt G n w k := by
  intro n
  induction n with
  | zero => intro k w; rfl
  | succ n ih =>
    intro k w
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · change (pivotEquiv G n j (advanceTail G w)).1 =
        edgeAt G n (advanceTail G w) j
      exact ih j (advanceTail G w)

theorem edgeAt_port (G : PortGraph V D) :
    ∀ (n : Nat) (w : Walk V D (n + 1)) (k : Fin (n + 1)),
      (edgeAt G n w k).2 = w.2 k := by
  intro n
  induction n with
  | zero =>
    intro w k
    have hk : k = 0 := Fin.eq_zero k
    subst k
    rfl
  | succ n ih =>
    intro w k
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · exact ih (advanceTail G w) j

theorem pivotEquiv_succ_apply (G : PortGraph V D)
    (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 2)) :
    pivotEquiv G (n + 1) k.succ w =
      ((pivotEquiv G n k (advanceTail G w)).1,
       Fin.cases (G.rot (w.1, w.2 0)).2
         (pivotEquiv G n k (advanceTail G w)).2) := rfl

def leftFromPivot (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) → V → (Fin n → D) → V
  | 0, _, v, _ => v
  | n + 1, k, v, r => Fin.cases v
      (fun j => next G (leftFromPivot G n j v (fun m => r m.succ)) (r 0)) k

def rightFromPivot (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) → Edge V D → (Fin n → D) → V
  | 0, _, e, _ => next G e.1 e.2
  | n + 1, k, e, r => Fin.cases
      (wordEnd G (n + 1) (next G e.1 e.2) r)
      (fun j => rightFromPivot G n j e (fun m => r m.succ)) k

theorem leftFromPivot_actual (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 1)),
      leftFromPivot G n k (pivotEquiv G n k w).1.1 (pivotEquiv G n k w).2 = w.1 := by
  intro n
  induction n with
  | zero => intro k w; rfl
  | succ n ih =>
    intro k w
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · rw [pivotEquiv_succ_apply]
      change next G
        (leftFromPivot G n j (pivotEquiv G n j (advanceTail G w)).1.1
          (pivotEquiv G n j (advanceTail G w)).2)
        (G.rot (w.1, w.2 0)).2 = w.1
      rw [ih j (advanceTail G w)]
      change (G.rot ((G.rot (w.1, w.2 0)).1, (G.rot (w.1, w.2 0)).2)).1 = w.1
      exact congrArg Prod.fst (rot_rot G (w.1, w.2 0))

theorem rightFromPivot_actual (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 1)),
      rightFromPivot G n k (pivotEquiv G n k w).1 (pivotEquiv G n k w).2 =
        endpoint G w := by
  intro n
  induction n with
  | zero => intro k w; rfl
  | succ n ih =>
    intro k w
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · rw [pivotEquiv_succ_apply]
      change rightFromPivot G n j (pivotEquiv G n j (advanceTail G w)).1
        (pivotEquiv G n j (advanceTail G w)).2 = endpoint G w
      rw [ih j (advanceTail G w)]
      rfl

end UniqueGamesTheorem.Foundations.PCP.PoweringWalks

end

section

/-!
Cloud replacement for arbitrary finite constraint graphs. The new vertices are
the old darts; internal ports enforce equality inside each cloud, and one
external port applies the original constraint. Dummy loop darts allow padding
each cloud independently before replacement.

The supplied cloud port graphs are explicit parameters; no expansion or
soundness claim is assumed.
-/

open scoped BigOperators

namespace UniqueGamesTheorem.Foundations.PCP.DegreeReplacement

open PoweringWalks

variable {V E A D : Type*}

theorem replacement_complete [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (labeling : V → A) (h : ∀ e, G.edgeSatisfied labeling e = true) :
    ∀ p, (replacementGraph G H).edgeSatisfied (liftLabel G labeling) p = true := by
  rintro ⟨e, p⟩
  rcases p with d | u
  · exact replacement_satisfied_inl G H labeling e d
  · rw [replacement_satisfied_inr]
    exact h e

theorem rejectionCount_eq_sum [Fintype E] (G : ConstraintGraph V E A)
    (labeling : V → A) :
    G.rejectionCount labeling =
      ∑ e, if G.edgeSatisfied labeling e = false then 1 else 0 := by
  classical
  simp only [ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts,
    Finset.card_eq_sum_ones, Finset.sum_filter]

theorem padded_complete (G : ConstraintGraph V E A) (dummy : V → Type*)
    (labeling : V → A) (h : ∀ e, G.edgeSatisfied labeling e = true) :
    ∀ c, (paddedGraph G dummy).edgeSatisfied labeling c = true := by
  intro c
  cases c with
  | inl e => exact h e
  | inr z => rfl

theorem padded_rejectionCount [Fintype V] [Fintype E]
    (G : ConstraintGraph V E A) (dummy : V → Type*) [∀ v, Fintype (dummy v)]
    (labeling : V → A) :
    (paddedGraph G dummy).rejectionCount labeling = G.rejectionCount labeling := by
  classical
  simp only [rejectionCount_eq_sum, Fintype.sum_sum_type]
  simp
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rfl

end UniqueGamesTheorem.Foundations.PCP.DegreeReplacement

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PoweringLabelsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Relations.repeatedConsistentDecidable
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetRetraction.edgeSatisfied_pullback _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetRetraction.rejectionCount_pullback _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_dart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_vertex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.dartEquiv_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_edgeAddress_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_event_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_vertexAddress_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph_rejectionCount _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GraphTables.semantics_ofGraph_rejectionCount _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.edgeSatisfied_inr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Full-radius local opinions use a common alphabet indexed by bounded
port addresses. Every opinion is decoded through a fixed address selector;
arbitrary alphabet symbols need not agree on colliding addresses. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringLabels

open PoweringWalks
open scoped BigOperators

variable {V D A : Type*}

def encode (G : PortGraph V D) (t : Nat) (v : V) (ℓ : Ball G t v → A) :
    PaddedLabel D t A := fun w => ℓ (wordToBall G t v w)

theorem decode_encode {G : PortGraph V D} {t : Nat} {v : V}
    (S : AddressSelector G t v) (ℓ : Ball G t v → A) :
    decode S (encode G t v ℓ) = ℓ := by
  funext u
  change ℓ (wordToBall G t v (S.address u)) = ℓ u
  rw [S.correct]

end UniqueGamesTheorem.Foundations.PCP.PoweringLabels

end

section

/-!
# Executable integer encodings for the powering construction

All encodings below have explicit inverses. They use the arithmetic finite
function, sigma, and product equivalences rather than choosing enumerations
from cardinality proofs. Word digits use the head-major convention; addresses
are grouped by increasing word length. A dart is numbered first by its vertex,
then its word, with its two orientations adjacent.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringEnumeration

open PoweringLabels
open scoped BigOperators

theorem dartBlockEquiv_val (d n : Nat) (p : Fin (n + 1) → Fin d) (b : Bool) :
    (dartBlockEquiv d n (p, b)).val =
      2 * (wordEquiv d (n + 1) p).val + (orientationEquiv b).val := by
  change (orientationEquiv b).val + 2 * (wordEquiv d (n + 1) p).val = _
  exact Nat.add_comm _ _

theorem dartEquiv_val (vertices d n : Nat) (b : Bool) (v : Fin vertices)
    (p : Fin (n + 1) → Fin d) :
    (dartEquiv vertices d n (b, (v, p))).val =
      (2 * d ^ (n + 1)) * v.val +
        2 * (wordEquiv d (n + 1) p).val + (orientationEquiv b).val := by
  change (dartBlockEquiv d n (p, b)).val + (2 * d ^ (n + 1)) * v.val = _
  rw [dartBlockEquiv_val]
  omega

def encodeDart (vertices d n : Nat) :
    (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) →
      Fin (2 * vertices * d ^ (n + 1)) := dartEquiv vertices d n

def decodeDart (vertices d n : Nat) :
    Fin (2 * vertices * d ^ (n + 1)) →
      (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) := (dartEquiv vertices d n).symm

@[simp] theorem decodeDart_encodeDart (vertices d n : Nat)
    (e : Bool × (Fin vertices × (Fin (n + 1) → Fin d))) :
    decodeDart vertices d n (encodeDart vertices d n e) = e :=
  (dartEquiv vertices d n).symm_apply_apply e

@[simp] theorem encodeDart_decodeDart (vertices d n : Nat)
    (i : Fin (2 * vertices * d ^ (n + 1))) :
    encodeDart vertices d n (decodeDart vertices d n i) = i :=
  (dartEquiv vertices d n).apply_symm_apply i

end UniqueGamesTheorem.Foundations.PCP.PoweringEnumeration

end

section

/-!
An actual incidence constraint graph for a finite Boolean verifier with q queries.
Left labels are complete local answer tuples. Their validity includes consistency
at repeated proof addresses. A dart checks the tuple at the least position naming
its proof address. Both sides use the same 2^q-element alphabet; arbitrary right
labels are explicitly decoded by their first coordinate, and honest right labels
are constant tuples. Every incidence is represented by two opposite darts.

The count theorem proves a loss of exactly q in a supplied verifier rejection
fraction. It supplies a concrete construction, not a PCP-hardness premise. The
generic count statements permit an empty event type and introduce no dummy darts.
-/

namespace UniqueGamesTheorem.Foundations.PCP.QueryIncidence

variable {E X : Type*} {q : Nat}

def response (T : Verifier E X q) (assignment : X → Bool) (event : E) : Label q :=
  fun i => assignment (T.query event i)

theorem canonicalSlot_query [DecidableEq X] (T : Verifier E X q) (event : E) (i : Fin q) :
    T.query event (canonicalSlot T event i) = T.query event i :=
  Fin.find_spec (p := fun j => T.query event j = T.query event i) ⟨i, rfl⟩

theorem edgeSatisfied_eq_incidence [DecidableEq X] (T : Verifier E X q)
    (positive : 0 < q) (labeling : Vertex E X → Label q)
    (event : E) (slot : Fin q) (orientation : Bool) :
    (graph T positive).edgeSatisfied labeling ((event, slot), orientation) =
      incidenceAccept T positive event slot (labeling (.inl event))
        (labeling (.inr (T.query event slot))) := by
  cases orientation <;> rfl

def honestLabeling (T : Verifier E X q) (assignment : X → Bool) : Vertex E X → Label q
  | .inl event => response T assignment event
  | .inr address => encodeRight (assignment address)

theorem honest_leftValid (T : Verifier E X q) (assignment : X → Bool) (event : E)
    (accepted : T.accepts event (response T assignment event) = true) :
    LeftValid T event (response T assignment event) := by
  refine ⟨accepted, ?_⟩
  intro i j hij
  exact congrArg assignment hij

theorem honest_incidence [DecidableEq X] (T : Verifier E X q) (positive : 0 < q)
    (assignment : X → Bool) (event : E)
    (accepted : T.accepts event (response T assignment event) = true) (slot : Fin q) :
    incidenceAccept T positive event slot
      (honestLabeling T assignment (.inl event))
      (honestLabeling T assignment (.inr (T.query event slot))) = true := by
  simp only [incidenceAccept, Bool.and_eq_true, honestLabeling,
    decode_encodeRight]
  refine ⟨_root_.decide_eq_true (honest_leftValid T assignment event accepted), ?_⟩
  exact _root_.decide_eq_true (congrArg assignment (canonicalSlot_query T event slot))

theorem perfect_completeness [DecidableEq X] (T : Verifier E X q) (positive : 0 < q)
    (assignment : X → Bool)
    (accepted : ∀ event, T.accepts event (response T assignment event) = true) :
    ∀ dart, (graph T positive).edgeSatisfied (honestLabeling T assignment) dart = true := by
  rintro ⟨⟨event, slot⟩, orientation⟩
  rw [edgeSatisfied_eq_incidence]
  exact honest_incidence T positive assignment event (accepted event) slot

theorem satisfiable_of_verifier_satisfiable [DecidableEq X] (T : Verifier E X q)
    (positive : 0 < q)
    (sat : ∃ assignment : X → Bool,
      ∀ event, T.accepts event (response T assignment event) = true) :
    (graph T positive).Satisfiable := by
  obtain ⟨assignment, h⟩ := sat
  exact ⟨honestLabeling T assignment, perfect_completeness T positive assignment h⟩

def decodedAssignment (positive : 0 < q) (labeling : Vertex E X → Label q) : X → Bool :=
  fun address => decodeRight positive (labeling (.inr address))

theorem incidenceAccept_true [DecidableEq X] (T : Verifier E X q) (positive : 0 < q)
    (event : E) (slot : Fin q) (left right : Label q)
    (accepted : incidenceAccept T positive event slot left right = true) :
    T.accepts event left = true ∧ RepeatedConsistent T event left ∧
      left (canonicalSlot T event slot) = decodeRight positive right := by
  simp only [incidenceAccept, Bool.and_eq_true] at accepted
  have hvalid : LeftValid T event left := _root_.of_decide_eq_true accepted.1
  exact ⟨hvalid.1, hvalid.2, _root_.of_decide_eq_true accepted.2⟩

theorem all_incidences_imply_event [DecidableEq X] (T : Verifier E X q)
    (positive : 0 < q) (labeling : Vertex E X → Label q) (event : E)
    (accepted : ∀ slot, incidenceAccept T positive event slot (labeling (.inl event))
      (labeling (.inr (T.query event slot))) = true) :
    T.accepts event (response T (decodedAssignment positive labeling) event) = true := by
  have first := incidenceAccept_true T positive event (zeroSlot positive) _ _
    (accepted (zeroSlot positive))
  have labels_equal : labeling (.inl event) = response T (decodedAssignment positive labeling) event := by
    funext slot
    have info := incidenceAccept_true T positive event slot _ _ (accepted slot)
    exact (first.2.1 slot (canonicalSlot T event slot)
      (canonicalSlot_query T event slot).symm).trans info.2.2
  rw [← labels_equal]
  exact first.1

theorem rejected_event_forces_slot [DecidableEq X] (T : Verifier E X q)
    (positive : 0 < q) (labeling : Vertex E X → Label q) (event : E)
    (rejected : T.accepts event (response T (decodedAssignment positive labeling) event) = false) :
    ∃ slot, incidenceAccept T positive event slot (labeling (.inl event))
      (labeling (.inr (T.query event slot))) = false := by
  classical
  by_contra none
  have all : ∀ slot, incidenceAccept T positive event slot (labeling (.inl event))
      (labeling (.inr (T.query event slot))) = true := by
    intro slot
    cases h : incidenceAccept T positive event slot (labeling (.inl event))
        (labeling (.inr (T.query event slot))) with
    | false => exact False.elim (none ⟨slot, h⟩)
    | true => rfl
  have h := all_incidences_imply_event T positive labeling event all
  rw [rejected] at h
  cases h

def rejectedEvents [Fintype E] (T : Verifier E X q) (assignment : X → Bool) : Finset E :=
  Finset.univ.filter (fun event => T.accepts event (response T assignment event) = false)

def verifierRejectionCount [Fintype E] (T : Verifier E X q) (assignment : X → Bool) : Nat :=
  (rejectedEvents T assignment).card

/-- Every rejected event contributes two distinct rejected darts, one in each
orientation. A classical witness is used only in this counting proof. -/
theorem rejection_count_bound [Fintype E] [DecidableEq X]
    (T : Verifier E X q) (positive : 0 < q) (labeling : Vertex E X → Label q) :
    2 * verifierRejectionCount T (decodedAssignment positive labeling) ≤
      (graph T positive).rejectionCount labeling := by
  classical
  let failed := rejectedEvents T (decodedAssignment positive labeling)
  have witnesses : ∀ event, event ∈ failed →
      ∃ slot, incidenceAccept T positive event slot (labeling (.inl event))
        (labeling (.inr (T.query event slot))) = false := by
    intro event he
    apply rejected_event_forces_slot T positive labeling event
    simpa [failed, rejectedEvents] using he
  let chosen := fun event he => Classical.choose (witnesses event he)
  let inject : (failed.product (Finset.univ : Finset Bool)) →
      (graph T positive).rejectedDarts labeling := fun p =>
    ⟨((p.val.1, chosen p.val.1 (Finset.mem_product.mp p.property).1), p.val.2), by
      apply (ConstraintGraph.mem_rejectedDarts _ _ _).mpr
      rw [edgeSatisfied_eq_incidence]
      exact Classical.choose_spec (witnesses p.val.1 (Finset.mem_product.mp p.property).1)⟩
  have injective : Function.Injective inject := by
    intro a b h
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun d => d.val.1.1) h
    · exact congrArg (fun d => d.val.2) h
  have bound := Finset.card_le_card_of_injective injective
  simpa [failed, verifierRejectionCount, ConstraintGraph.rejectionCount,
    Finset.card_product, Nat.mul_comm] using bound

end UniqueGamesTheorem.Foundations.PCP.QueryIncidence

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_AlphabetRetractionLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTables.graph_ofGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTables.graph_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTables.lookup_ofGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GraphTransport.reindex_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.accepts_ofPortGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.portGraph_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.rotation_ofPortGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables.walkRows_edge _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables.walkRows_head_value _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables.walkRows_tail_value _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringWalks.lazyGraph_rot_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringWalks.lazyGraph_rot_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs.square_next _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs.square_rot_apply _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs.zigzag_rot_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Pull a graph predicate back through a surjective label decoder.  This preserves
every rejection count after decoding.  A concrete section embeds the initial
eight-label graph into the fixed 64-label alphabet used throughout amplification.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetRetraction

variable {V E A B : Type*}

theorem satisfiable_pullback_iff (G : ConstraintGraph V E A)
    (decode : B → A) (encode : A → B) (sectionLaw : ∀ a, decode (encode a) = a) :
    (pullback G decode).Satisfiable ↔ G.Satisfiable := by
  constructor
  · rintro ⟨labeling, h⟩
    exact ⟨decode ∘ labeling, h⟩
  · rintro ⟨labeling, h⟩
    refine ⟨encode ∘ labeling, fun e => ?_⟩
    change G.accepts e (decode (encode (labeling (G.tail e))))
      (decode (encode (labeling (G.head e)))) = true
    simpa only [ConstraintGraph.edgeSatisfied, sectionLaw] using h e

end UniqueGamesTheorem.Foundations.PCP.AlphabetRetraction

end

section

namespace UniqueGamesTheorem.Foundations.PCP.SpectralReturn

open PoweringWalks
open scoped BigOperators

noncomputable section

def correlation {A : Type*} [Fintype A] (f g : A → ℝ) : ℝ :=
  mean (fun x => f x * g x)

def iterateOperator {V D : Type*} [Fintype D] (G : PortGraph V D) :
    Nat → (V → ℝ) → (V → ℝ)
  | 0, f => f
  | n + 1, f => averagingOperator G (iterateOperator G n f)

def edgeDensity {V D : Type*} [Fintype V] [Fintype D] (bad : V × D → Bool) : ℝ :=
  mean (edgeProfile bad)

def markedStep {V D : Type*} [Fintype D] (G : PortGraph V D)
    (bad : V × D → Bool) (f : V → ℝ) (v : V) : ℝ :=
  Finset.univ.expect (fun d => if bad (v, d) then f (G.rot (v, d)).1 else 0)

def returnMass {V D : Type*} [Fintype V] [Fintype D]
    (G : PortGraph V D) (bad : V × D → Bool) (gap : Nat) : ℝ :=
  mean (markedStep G bad (iterateOperator G gap (edgeProfile bad)))

section Averages

variable {A B : Type*} [Fintype A] [Fintype B]

theorem mean_eq_sum_div_card (f : A → ℝ) :
    mean f = (∑ x, f x) / (Fintype.card A : ℝ) :=
  Fintype.expect_eq_sum_div_card f

theorem mean_add (f g : A → ℝ) :
    mean (fun x => f x + g x) = mean f + mean g :=
  Finset.expect_add_distrib _ f g

theorem mean_sub (f g : A → ℝ) :
    mean (fun x => f x - g x) = mean f - mean g :=
  Finset.expect_sub_distrib _ f g

theorem mean_mul_left (c : ℝ) (f : A → ℝ) :
    mean (fun x => c * f x) = c * mean f :=
  (Finset.mul_expect _ f c).symm

theorem mean_mul_right (f : A → ℝ) (c : ℝ) :
    mean (fun x => f x * c) = mean f * c :=
  (Finset.expect_mul _ f c).symm

theorem mean_nonnegative (f : A → ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ mean f :=
  Finset.expect_nonneg (fun x _ => hf x)

theorem mean_mono {f g : A → ℝ} (h : ∀ x, f x ≤ g x) : mean f ≤ mean g :=
  Finset.expect_le_expect (fun x _ => h x)

theorem energy_nonnegative (f : A → ℝ) : 0 ≤ energy f :=
  mean_nonnegative _ (fun x => sq_nonneg (f x))

/-- The finite Cauchy--Schwarz inequality, in the chosen normalized convention. -/
theorem correlation_sq_le (f g : A → ℝ) :
    correlation f g ^ 2 ≤ energy f * energy g :=
  Finset.expect_mul_sq_le_sq_mul_sq Finset.univ f g

theorem energy_sub_const [Nonempty A] (f : A → ℝ) (c : ℝ) :
    energy (fun x => f x - c) = energy f - 2 * c * mean f + c ^ 2 := by
  have h : (fun x => (f x - c) ^ 2) =
      (fun x => (f x) ^ 2 - (2 * c) * f x + c ^ 2) := by
    funext x
    ring
  unfold energy
  rw [h, mean_add, mean_sub, mean_mul_left, mean_const]

theorem correlation_sub_const [Nonempty A] (f g : A → ℝ) (c d : ℝ) :
    correlation (fun x => f x - c) (fun x => g x - d) =
      correlation f g - d * mean f - c * mean g + c * d := by
  have h : (fun x => (f x - c) * (g x - d)) =
      (fun x => f x * g x - d * f x - c * g x + c * d) := by
    funext x
    ring
  unfold correlation
  rw [h, mean_add, mean_sub, mean_sub, mean_mul_left, mean_mul_left, mean_const]

end Averages

section Graph

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
  (G : PortGraph V D)

omit [Nonempty V] in
theorem mean_operator (f : V → ℝ) : mean (averagingOperator G f) = mean f := by
  calc
    mean (averagingOperator G f) = mean (fun e : V × D => f (G.rot e).1) :=
      (mean_prod (fun e : V × D => f (G.rot e).1)).symm
    _ = mean (fun e : V × D => f e.1) := mean_equiv G.rot (fun e => f e.1)
    _ = mean (fun v : V => mean (fun _ : D => f v)) :=
      mean_prod (fun e : V × D => f e.1)
    _ = mean f := by simp only [mean_const]

omit [Fintype V] [Nonempty V] in
theorem operator_sub_const (f : V → ℝ) (c : ℝ) :
    averagingOperator G (fun v => f v - c) = fun v => averagingOperator G f v - c := by
  funext v
  change mean (fun d => f (G.rot (v, d)).1 - c) = _
  rw [mean_sub, mean_const]
  rfl

omit [Nonempty V] in
theorem mean_iterate (n : Nat) (f : V → ℝ) : mean (iterateOperator G n f) = mean f := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterateOperator, mean_operator, ih]

omit [Fintype V] [Nonempty V] in
theorem iterate_sub_const (n : Nat) (f : V → ℝ) (c : ℝ) :
    iterateOperator G n (fun v => f v - c) = fun v => iterateOperator G n f v - c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterateOperator, ih, operator_sub_const]; rfl

omit [Nonempty V] [Nonempty D] in
/-- Reversal moves the first marked edge to its endpoint. The profile therefore
appears at the endpoint, before the `gap` remaining vertex transitions. -/
theorem mean_markedStep (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (f : V → ℝ) :
    mean (markedStep G bad f) = correlation (edgeProfile bad) f := by
  calc
    mean (markedStep G bad f) =
        mean (fun e : V × D => if bad e then f (G.rot e).1 else 0) := by
      exact (mean_prod (fun e : V × D => if bad e then f (G.rot e).1 else 0)).symm
    _ = mean (fun e : V × D => if bad (G.rot e)
          then f (G.rot (G.rot e)).1 else 0) :=
      (mean_equiv G.rot (fun e : V × D => if bad e then f (G.rot e).1 else 0)).symm
    _ = mean (fun e : V × D => if bad e then f e.1 else 0) := by
      congr 1
      funext e
      rw [reversal e, G.rot_involutive e]
    _ = mean (fun v => mean (fun d => if bad (v, d) then f v else 0)) :=
      mean_prod (fun e : V × D => if bad e then f e.1 else 0)
    _ = correlation (edgeProfile bad) f := by
      unfold correlation
      congr 1
      funext v
      have h : (fun d => if bad (v, d) then f v else 0) =
          (fun d => (if bad (v, d) then (1 : ℝ) else 0) * f v) := by
        funext d
        cases bad (v, d) <;> simp
      rw [h, mean_mul_right]
      rfl

omit [Nonempty V] [Nonempty D] in
theorem returnMass_eq_correlation (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (gap : Nat) :
    returnMass G bad gap = correlation (edgeProfile bad)
      (iterateOperator G gap (edgeProfile bad)) :=
  mean_markedStep G bad reversal _

omit [Nonempty V] in
theorem iterate_energy_bound (lambda : ℝ) (certificate : SpectralCertificate G lambda)
    (f : V → ℝ) (hf : mean f = 0) (n : Nat) :
    energy (iterateOperator G n f) ≤ (lambda ^ n) ^ 2 * energy f := by
  induction n with
  | zero => simp [iterateOperator]
  | succ n ih =>
      calc
        energy (iterateOperator G (n + 1) f) ≤
            lambda ^ 2 * energy (iterateOperator G n f) :=
          certificate.contraction _ ((mean_iterate G n f).trans hf)
        _ ≤ lambda ^ 2 * ((lambda ^ n) ^ 2 * energy f) :=
          mul_le_mul_of_nonneg_left ih (sq_nonneg lambda)
        _ = (lambda ^ (n + 1)) ^ 2 * energy f := by rw [pow_succ]; ring

omit [Nonempty V] in
theorem zero_mean_correlation_bound (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (f : V → ℝ)
    (hf : mean f = 0) (n : Nat) :
    correlation f (iterateOperator G n f) ≤ lambda ^ n * energy f := by
  have hsq : correlation f (iterateOperator G n f) ^ 2 ≤
      (lambda ^ n * energy f) ^ 2 := by
    calc
      _ ≤ energy f * energy (iterateOperator G n f) := correlation_sq_le _ _
      _ ≤ energy f * ((lambda ^ n) ^ 2 * energy f) :=
        mul_le_mul_of_nonneg_left (iterate_energy_bound G lambda certificate f hf n)
          (energy_nonnegative f)
      _ = _ := by ring
  exact le_of_sq_le_sq hsq
    (mul_nonneg (pow_nonneg certificate.nonnegative n) (energy_nonnegative f))

theorem correlation_centered (f : V → ℝ) (n : Nat) :
    correlation f (iterateOperator G n f) = mean f ^ 2 +
      correlation (fun v => f v - mean f)
        (iterateOperator G n (fun v => f v - mean f)) := by
  rw [iterate_sub_const, correlation_sub_const, mean_iterate]
  ring

end Graph

section Profiles

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]

omit [Fintype V] [Nonempty V] [Nonempty D] in
theorem edgeProfile_nonnegative (bad : V × D → Bool) (v : V) : 0 ≤ edgeProfile bad v :=
  mean_nonnegative _ (fun d => by cases bad (v, d) <;> norm_num)

omit [Fintype V] [Nonempty V] in
theorem edgeProfile_le_one (bad : V × D → Bool) (v : V) : edgeProfile bad v ≤ 1 := by
  change mean (fun d => if bad (v, d) then (1 : ℝ) else 0) ≤ 1
  calc
    _ ≤ mean (fun _ : D => (1 : ℝ)) := mean_mono (fun d => by
      cases bad (v, d) <;> norm_num)
    _ = 1 := mean_const _

omit [Nonempty V] [Nonempty D] in
theorem edgeDensity_nonnegative (bad : V × D → Bool) : 0 ≤ edgeDensity bad :=
  mean_nonnegative _ (edgeProfile_nonnegative bad)

omit [Nonempty V] in
theorem edgeProfile_energy_le_density (bad : V × D → Bool) :
    energy (edgeProfile bad) ≤ edgeDensity bad :=
  mean_mono (fun v => by
    have h0 := edgeProfile_nonnegative bad v
    have h1 := edgeProfile_le_one bad v
    nlinarith)

theorem edgeProfile_centered_energy (bad : V × D → Bool) :
    energy (fun v => edgeProfile bad v - edgeDensity bad) ≤
      edgeDensity bad * (1 - edgeDensity bad) := by
  rw [energy_sub_const]
  have h := edgeProfile_energy_le_density bad
  change energy (edgeProfile bad) - 2 * edgeDensity bad * edgeDensity bad +
    edgeDensity bad ^ 2 ≤ _
  nlinarith

/-- Sharp return bound. No division by the bad-edge density occurs, so the empty
bad set is covered. `gap = 0` gives the adjacent-edge upper bound `epsilon`. -/
theorem returnMass_le_sharp (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (gap : Nat) :
    returnMass G bad gap ≤ edgeDensity bad ^ 2 +
      lambda ^ gap * (edgeDensity bad * (1 - edgeDensity bad)) := by
  rw [returnMass_eq_correlation G bad reversal, correlation_centered]
  have hzero : mean (fun v => edgeProfile bad v - edgeDensity bad) = 0 := by
    rw [mean_sub, mean_const]
    simp only [edgeDensity, sub_self]
  have hc := zero_mean_correlation_bound G lambda certificate
    (fun v => edgeProfile bad v - edgeDensity bad) hzero gap
  have hv := mul_le_mul_of_nonneg_left (edgeProfile_centered_energy bad)
    (pow_nonneg certificate.nonnegative gap)
  change edgeDensity bad ^ 2 + _ ≤ _
  exact add_le_add (le_refl _) (hc.trans hv)

/-- The simple bound used in the second-moment estimate. -/
theorem returnMass_le (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (gap : Nat) :
    returnMass G bad gap ≤ edgeDensity bad ^ 2 + edgeDensity bad * lambda ^ gap := by
  have h := returnMass_le_sharp G lambda certificate bad reversal gap
  have hvar : edgeDensity bad * (1 - edgeDensity bad) ≤ edgeDensity bad := by
    nlinarith [sq_nonneg (edgeDensity bad)]
  have hm := mul_le_mul_of_nonneg_left hvar (pow_nonneg certificate.nonnegative gap)
  nlinarith

end Profiles

/-- The finite geometric-series bound that absorbs forward and reverse returns.
It applies to every finite window, with no limiting probability argument. -/
theorem geometric_sum_le (lambda : ℝ) (h0 : 0 ≤ lambda) (h1 : lambda < 1) (n : Nat) :
    (∑ k ∈ Finset.range n, lambda ^ k) ≤ 1 / (1 - lambda) := by
  have hsum : (∑ k ∈ Finset.range n, lambda ^ k) * (1 - lambda) = 1 - lambda ^ n := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, pow_succ]; nlinarith
  have hden : 0 < 1 - lambda := by linarith
  apply (le_div_iff₀ hden).2
  rw [hsum]
  linarith [pow_nonneg h0 n]

section ReturnSums

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]

/-- The return contribution from one marked edge, over a finite forward window. -/
theorem sum_returnMass_le (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (n : Nat) :
    (∑ gap ∈ Finset.range n, returnMass G bad gap) ≤
      (n : ℝ) * edgeDensity bad ^ 2 + edgeDensity bad / (1 - lambda) := by
  calc
    _ ≤ ∑ gap ∈ Finset.range n,
        (edgeDensity bad ^ 2 + edgeDensity bad * lambda ^ gap) :=
      Finset.sum_le_sum (fun gap _ => returnMass_le G lambda certificate bad reversal gap)
    _ = (n : ℝ) * edgeDensity bad ^ 2 +
        edgeDensity bad * (∑ gap ∈ Finset.range n, lambda ^ gap) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (n : ℝ) * edgeDensity bad ^ 2 + edgeDensity bad * (1 / (1 - lambda)) :=
      add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left
          (geometric_sum_le lambda certificate.nonnegative certificate.lt_one n)
          (edgeDensity_nonnegative bad))
    _ = _ := by ring

/-- Sum over all distinct ordered-time pairs, counting each pair once.
The row for the later edge `j` has gaps `0,...,j-1`. -/
theorem triangular_returnMass_sum_le (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (n : Nat) :
    (∑ j ∈ Finset.range n, ∑ gap ∈ Finset.range j, returnMass G bad gap) ≤
      ((n : ℝ) * ((n : ℝ) - 1) / 2) * edgeDensity bad ^ 2 +
        (n : ℝ) * (edgeDensity bad / (1 - lambda)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hrow := sum_returnMass_le G lambda certificate bad reversal n
      have h := add_le_add ih hrow
      calc
        _ ≤ ((n : ℝ) * ((n : ℝ) - 1) / 2) * edgeDensity bad ^ 2 +
            (n : ℝ) * (edgeDensity bad / (1 - lambda)) +
            ((n : ℝ) * edgeDensity bad ^ 2 + edgeDensity bad / (1 - lambda)) := h
        _ = _ := by simp only [Nat.cast_add, Nat.cast_one] <;> ring

/-- The exact finite envelope needed after expanding the square of the hit
count. The diagonal contributes `n * epsilon`; both off-diagonal triangles
contribute twice the return sum. The actual walk-event identity is supplied by
`PoweringMoment` and `PoweringReturn`. -/
theorem secondMoment_return_envelope (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (n : Nat) :
    (n : ℝ) * edgeDensity bad +
        2 * (∑ j ∈ Finset.range n, ∑ gap ∈ Finset.range j, returnMass G bad gap) ≤
      (n : ℝ) * edgeDensity bad *
        (1 + 2 / (1 - lambda) + ((n : ℝ) - 1) * edgeDensity bad) := by
  calc
    _ ≤ (n : ℝ) * edgeDensity bad +
        2 * (((n : ℝ) * ((n : ℝ) - 1) / 2) * edgeDensity bad ^ 2 +
          (n : ℝ) * (edgeDensity bad / (1 - lambda))) :=
      add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left
          (triangular_returnMass_sum_le G lambda certificate bad reversal n) (by norm_num))
    _ = _ := by ring

end ReturnSums

end

end UniqueGamesTheorem.Foundations.PCP.SpectralReturn

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_GraphTables
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetRetraction.edgeSatisfied_pullback _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetRetraction.rejectionCount_pullback _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.DegreeReplacement.padded_satisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.DegreeReplacement.padded_satisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.acceptsAt_graphRows _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.reverseAt_graphRows _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_accepts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph_rejectionCount _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_head _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_reverse_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_reverse_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.paddedG_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Executable directed-dart tables for the fixed 64-label alphabet

The header gives vertex and dart counts. Every dart has one ordered row:
tail index, reverse-dart index, and 4096 Boolean predicate entries. Entry
`b + 64 * a` is the predicate at labels `(a,b)`. All fields, including bits
as 0/1 words, use the existing zero-delimited unary natural-word codec.

The decoder checks all index bounds, row counts, predicate lengths, reverse
involution, predicate transpose, and absence of trailing fields. Directed rows
preserve loops, self-reversing darts, and repeated constraint occurrences.
The size theorems concern the full encoded table, not a machine runtime.
-/

namespace UniqueGamesTheorem.Foundations.PCP.GraphTables

open UniqueGamesTheorem.Foundations.Complexity

theorem enumeratedGraph_edgeSatisfied {V E A : Type*} {n m : Nat}
    (G : ConstraintGraph V E A) (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m)
    (labelOrder : A ≃ Label) (labeling : V → A) (e : E) :
    (enumeratedGraph G vertexOrder dartOrder labelOrder).edgeSatisfied
      (fun v => labelOrder (labeling (vertexOrder.symm v))) (dartOrder e) =
        G.edgeSatisfied labeling e := by
  simp [ConstraintGraph.edgeSatisfied, ConstraintGraph.head, enumeratedGraph]

/-- Every directed occurrence contributes once before and after enumeration. -/
theorem enumeratedGraph_rejectionCount {V E A : Type*} [Fintype E] {n m : Nat}
    (G : ConstraintGraph V E A) (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m)
    (labelOrder : A ≃ Label) (labeling : V → A) :
    (enumeratedGraph G vertexOrder dartOrder labelOrder).rejectionCount
      (fun v => labelOrder (labeling (vertexOrder.symm v))) = G.rejectionCount labeling := by
  classical
  unfold ConstraintGraph.rejectionCount
  symm
  apply Finset.card_equiv dartOrder
  intro e
  simp only [ConstraintGraph.mem_rejectedDarts, enumeratedGraph_edgeSatisfied]

end UniqueGamesTheorem.Foundations.PCP.GraphTables

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_GenericGraphTables
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetRetraction.edgeSatisfied_pullback _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetRetraction.rejectionCount_pullback _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.DegreeReplacement.padded_satisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.DegreeReplacement.padded_satisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_head _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_reverse_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_reverse_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.paddedG_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Executable directed graph tables over a fixed finite alphabet

The alphabet size `q` is fixed by the encoding, not encoded as a variable input
field. The header stores vertex and directed-dart counts. Each ordered dart row
stores its tail, reverse index, and every `q*q` predicate bit in order `b+q*a`.
All fields use the existing unary natural-word codec. Decoding validates graph
laws and preserves loops and repeated darts. Size bounds count the complete
serialized table and make no running-time assertion.
-/

namespace UniqueGamesTheorem.Foundations.PCP.GenericGraphTables

open UniqueGamesTheorem.Foundations.Complexity

variable {q : Nat}

theorem relationIndex_val (a b : (Label q)) :
    ((relationIndex q) (a, b)).val = b.val + q * a.val := rfl

theorem enumeratedGraph_edgeSatisfied {V E A : Type*} {n m : Nat}
    (G : ConstraintGraph V E A) (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m)
    (labelOrder : A ≃ (Label q)) (labeling : V → A) (e : E) :
    (enumeratedGraph G vertexOrder dartOrder labelOrder).edgeSatisfied
      (fun v => labelOrder (labeling (vertexOrder.symm v))) (dartOrder e) =
        G.edgeSatisfied labeling e := by
  simp [ConstraintGraph.edgeSatisfied, ConstraintGraph.head, enumeratedGraph]

/-- Every directed occurrence contributes once before and after enumeration. -/
theorem enumeratedGraph_rejectionCount {V E A : Type*} [Fintype E] {n m : Nat}
    (G : ConstraintGraph V E A) (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m)
    (labelOrder : A ≃ (Label q)) (labeling : V → A) :
    (enumeratedGraph G vertexOrder dartOrder labelOrder).rejectionCount
      (fun v => labelOrder (labeling (vertexOrder.symm v))) = G.rejectionCount labeling := by
  classical
  unfold ConstraintGraph.rejectionCount
  symm
  apply Finset.card_equiv dartOrder
  intro e
  simp only [ConstraintGraph.mem_rejectedDarts, enumeratedGraph_edgeSatisfied]

end UniqueGamesTheorem.Foundations.PCP.GenericGraphTables

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_InputLemmas
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec.decodeWords_encodeWord _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter.counterTapes_counter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Serialization boundaries and direct row lookup for the shared executable
fixed-alphabet graph codec. The alphabet is a fixed parameter. Rows remain in
their stored order, including repeated darts and loops. Word offsets are fixed;
bit offsets are represented by actual encoded prefixes because unary fields
have data-dependent lengths. These are data identities, not runtime certificates.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Input

open UniqueGamesTheorem.Foundations.Complexity

export GenericGraphTables (Label RelationTable DartRow Rows Valid Table
  relationIndex relationIndex_val relationAt relationOf relationAt_relationOf
  reverseAt acceptsAt rowList rowList_length semantics semantics_reverse
  semantics_tail semantics_accepts ofGraph semantics_ofGraph ofEnumeratedGraph
  bitWord relationWords relationWords_length rowWords parseRelation parseRelation_encoded )

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Input

end

section

/-!
An actual fixed-alphabet TM2 parser for the complete Boolean relation table.
The finite syntax contains one slot reader for each of the `q*q` coordinates.
Each reader consumes `[false]` or `[true,false]`, stores the bit, and clears the
head register. No parser outcome or execution trace is an assumption.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.ReadRelation

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K] {q : Nat}

abbrev State (σ : Type) (q : Nat) := (σ × RelationTable q) × Option Bool

@[instance_reducible] def stateFintype (σ : Type) (q : Nat) [Fintype σ] :
    Fintype (State σ q) := by
  letI := relationFintype q
  exact inferInstance

/-- Read one encoded Boolean into a fixed slot of the finite relation register. -/
def readSlot (source : K) (i : Fin (q * q))
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q)) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q) :=
  .pop source
    (fun state head =>
      ((state.1.1, state.1.2.set i.val (head.getD false) i.isLt), head))
    (.branch (fun state => state.2.getD false)
      (.pop source (fun state _ => (state.1, none)) next)
      (.load (fun state => (state.1, none)) next))

theorem stepAux_readSlot (source : K) (i : Fin (q * q)) (bit : Bool)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q))
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (initial : RelationTable q) (register : Option Bool) :
    TM2.stepAux (readSlot source i next) ((ambient, initial), register)
      (Function.update base source (encodeWord (bitWord bit) ++ suffix)) =
      TM2.stepAux next ((ambient, initial.set i.val bit i.isLt), none)
        (Function.update base source suffix) := by
  cases bit <;> simp [readSlot, TM2.stepAux, bitWord, encodeWord]

def readSlots (source : K) : List (Fin (q * q)) →
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q) →
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q)
  | [], next => .load (fun state => (state.1, none)) next
  | i :: indices, next => readSlot source i (readSlots source indices next)

def indexedWords (relation : RelationTable q) (indices : List (Fin (q * q))) : List Nat :=
  indices.map (fun i => bitWord relation[i.val])

def fillSlots (relation : RelationTable q) : List (Fin (q * q)) →
    RelationTable q → RelationTable q
  | [], initial => initial
  | i :: indices, initial =>
      fillSlots relation indices (initial.set i.val relation[i.val] i.isLt)

theorem fillSlots_preserves_correct (relation : RelationTable q)
    (indices : List (Fin (q * q))) (initial : RelationTable q) (i : Fin (q * q))
    (hcorrect : initial[i.val] = relation[i.val]) :
    (fillSlots relation indices initial)[i.val] = relation[i.val] := by
  induction indices generalizing initial with
  | nil => exact hcorrect
  | cons j indices ih =>
    apply ih
    by_cases hji : j.val = i.val
    · simp [hji]
    · simp [hji, hcorrect]

theorem fillSlots_mem (relation : RelationTable q) (indices : List (Fin (q * q)))
    (initial : RelationTable q) (i : Fin (q * q)) (hi : i ∈ indices) :
    (fillSlots relation indices initial)[i.val] = relation[i.val] := by
  induction indices generalizing initial with
  | nil => simp at hi
  | cons j indices ih =>
    change (fillSlots relation indices (initial.set j.val relation[j.val] j.isLt))[i.val] = _
    rcases List.mem_cons.mp hi with h | h
    · subst j
      apply fillSlots_preserves_correct
      simp
    · exact ih _ h

theorem fillSlots_finRange (relation initial : RelationTable q) :
    fillSlots relation (List.finRange (q * q)) initial = relation := by
  apply Vector.ext
  intro i hi
  exact fillSlots_mem relation (List.finRange (q * q)) initial ⟨i, hi⟩
    (List.mem_finRange _)

theorem indexedWords_finRange (relation : RelationTable q) :
    indexedWords relation (List.finRange (q * q)) = relationWords relation := by
  have h : (List.finRange (q * q)).map (fun i => relation[i.val]) = relation.toList := by
    rw [List.finRange, List.map_ofFn]
    change List.ofFn (fun i : Fin (q * q) => relation[i.val]) = relation.toList
    rw [← Vector.toList_ofFn, Vector.ofFn_getElem]
  calc
    _ = ((List.finRange (q * q)).map (fun i => relation[i.val])).map bitWord := by
      simp only [indexedWords, List.map_map, Function.comp_def]
    _ = relation.toList.map bitWord := congrArg (fun bits : List Bool => bits.map bitWord) h
    _ = _ := rfl

/-- Each stored register bit is obtained from its actual serialized field. -/
theorem stepAux_readSlots (source : K) (indices : List (Fin (q * q)))
    (relation : RelationTable q)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q))
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (initial : RelationTable q) (register : Option Bool) :
    TM2.stepAux (readSlots source indices next) ((ambient, initial), register)
      (Function.update base source (encodeWords (indexedWords relation indices) ++ suffix)) =
      TM2.stepAux next ((ambient, fillSlots relation indices initial), none)
        (Function.update base source suffix) := by
  induction indices generalizing initial register with
  | nil => simp [readSlots, fillSlots, indexedWords, encodeWords, TM2.stepAux]
  | cons i indices ih =>
    simp only [readSlots, indexedWords, List.map_cons, encodeWords, List.append_assoc, fillSlots]
    rw [stepAux_readSlot]
    exact ih _ none

/-- Fixed finite program fragment; it can be inserted before any continuation. -/
def readRelation (source : K)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q)) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q) :=
  readSlots source (List.finRange (q * q)) next

theorem stepAux_readRelation (source : K) (relation : RelationTable q)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q))
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (initial : RelationTable q) (register : Option Bool) :
    TM2.stepAux (readRelation source next) ((ambient, initial), register)
      (Function.update base source (encodeWords (relationWords relation) ++ suffix)) =
      TM2.stepAux next ((ambient, relation), none) (Function.update base source suffix) := by
  simpa only [readRelation, indexedWords_finRange, fillSlots_finRange] using
    stepAux_readSlots source (List.finRange (q * q)) relation next
      base suffix ambient initial register

def parser (source : K) (exitLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q) :=
  readRelation source (.goto fun _ => exitLabel)

theorem parserStep (source : K) (readLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ q))
    (atRead : program readLabel = parser source exitLabel)
    (base : K → List Bool) (relation : RelationTable q) (suffix : List Bool)
    (ambient : σ) (initial : RelationTable q) (register : Option Bool) :
    TM2.step program
      ⟨some readLabel, ((ambient, initial), register),
        Function.update base source (encodeWords (relationWords relation) ++ suffix)⟩ =
      some ⟨some exitLabel, ((ambient, relation), none), Function.update base source suffix⟩ := by
  change some (TM2.stepAux (program readLabel) ((ambient, initial), register)
    (Function.update base source (encodeWords (relationWords relation) ++ suffix))) = _
  rw [atRead, parser, stepAux_readRelation]
  rfl

/-- One transition executes the fixed chain of `q*q` slot readers. -/
theorem parserTrace (source : K) (readLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ q))
    (atRead : program readLabel = parser source exitLabel)
    (base : K → List Bool) (relation : RelationTable q) (suffix : List Bool)
    (ambient : σ) (initial : RelationTable q) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some readLabel, ((ambient, initial), register),
        Function.update base source (encodeWords (relationWords relation) ++ suffix)⟩) =
      some ⟨some exitLabel, ((ambient, relation), none), Function.update base source suffix⟩ := by
  simpa only [Function.iterate_one, MachineComposition.advance_some] using
    parserStep source readLabel exitLabel program atRead base relation suffix ambient initial register

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.ReadRelation

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_ExpandersLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTables.graph_ofGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTables.graph_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTables.lookup_ofGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.accepts_ofPortGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.portGraph_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.rotation_ofPortGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables.walkRows_edge _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables.walkRows_head_value _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables.walkRows_tail_value _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs.square_next _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs.square_rot_apply _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs.zigzag_rot_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
# Finite existence of the Cayley expander base

The sample space is the actual finite type of indexed Boolean-cube generators.
For each nonzero character, the checked sign sampling equivalence supplies its
uniform word law. A finite union bound then selects a generator family whose
nonconstant character biases are small. There is no random-graph hypothesis.

The fixed numbers below are manipulated symbolically; no enumeration of the
generator sample space is executed. The subsequent square-and-zigzag family
is a separate construction.
-/

/-! Exact changes of finite vertex and port coordinates. The graph rotation and
its normalized averaging operator are transported by the same equivalences. -/

section

/-! The actual half-lazy port graph retains a Boolean stay/step flag and an
ordinary port. This supplies the concrete graph underlying Boolean-tape
length smoothing. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringLazy

open PoweringWalks SpectralReturn

variable {V D : Type*}

theorem operator_binomialMean [Fintype D] (G : PortGraph V D)
    (n : Nat) (g : Nat → V → ℝ) (v : V) :
    averagingOperator G (fun w => LazySmoothing.binomialMean n (fun k => g k w)) v =
      LazySmoothing.binomialMean n (fun k => averagingOperator G (g k) v) := by
  unfold averagingOperator LazySmoothing.binomialMean
  exact Finset.expect_comm Finset.univ Finset.univ
    (fun d tape => g (LazySmoothing.bitCount tape) (G.rot (v, d)).1)

theorem averagingOperator_lazy [Fintype D] [Nonempty D]
    (G : PortGraph V D) (f : V → ℝ) (v : V) :
    averagingOperator (lazyGraph G) f v = (f v + averagingOperator G f v) / 2 := by
  change mean (fun bd : Bool × D => f ((lazyGraph G).rot (v, bd)).1) = _
  rw [mean_prod]
  change Finset.univ.expect (fun b : Bool =>
    mean (fun d : D => f ((lazyGraph G).rot (v, (b, d))).1)) = _
  rw [LazySmoothing.expect_bool]
  simp only [lazyGraph_rot_false, lazyGraph_rot_true]
  rw [mean_const]
  rfl

/-- The exact Boolean-tape mixture for the actual lazy transition operator. -/
theorem iterate_lazy_eq_binomialMean [Fintype D] [Nonempty D]
    (G : PortGraph V D) (n : Nat) (f : V → ℝ) :
    iterateOperator (lazyGraph G) n f =
      fun v => LazySmoothing.binomialMean n (fun k => iterateOperator G k f v) := by
  induction n with
  | zero =>
    funext v
    simp [iterateOperator]
  | succ n ih =>
    funext v
    change averagingOperator (lazyGraph G) (iterateOperator (lazyGraph G) n f) v = _
    rw [ih, averagingOperator_lazy, operator_binomialMean, LazySmoothing.mean_succ]
    rfl

theorem iterate_mem_Icc [Fintype D] [Nonempty D]
    (G : PortGraph V D) (f : V → ℝ) (hf : ∀ w, f w ∈ Set.Icc (0 : ℝ) 1)
    (n : Nat) (v : V) : iterateOperator G n f v ∈ Set.Icc (0 : ℝ) 1 := by
  induction n generalizing v with
  | zero => exact hf v
  | succ n ih =>
    change mean (fun d : D => iterateOperator G n f (G.rot (v, d)).1) ∈ Set.Icc (0 : ℝ) 1
    constructor
    · exact mean_nonnegative _ (fun d => (ih ((G.rot (v, d)).1)).1)
    · calc
        mean (fun d : D => iterateOperator G n f (G.rot (v, d)).1) ≤
            mean (fun _ : D => (1 : ℝ)) :=
          mean_mono (fun d => (ih ((G.rot (v, d)).1)).2)
        _ = 1 := mean_const _

/-- The modal lower bound survives every allowed nearby actual lazy length. -/
theorem lazy_endpoint_modal_transfer [Fintype D] [Nonempty D]
    (G : PortGraph V D) (q M m : Nat) (hq : 1 ≤ q) (hM : 1 ≤ M)
    (hlo : (4 * q * M) ^ 2 - M ≤ m) (hhi : m ≤ (4 * q * M) ^ 2 + M)
    (f : V → ℝ) (hf : ∀ w, f w ∈ Set.Icc (0 : ℝ) 1) (v : V)
    (hmodal : 1 / (q : ℝ) ≤ iterateOperator (lazyGraph G) ((4 * q * M) ^ 2) f v) :
    1 / (2 * (q : ℝ)) ≤ iterateOperator (lazyGraph G) m f v := by
  rw [iterate_lazy_eq_binomialMean] at hmodal ⊢
  exact LazySmoothing.modal_transfer q M m hq hM hlo hhi
    (fun k => iterateOperator G k f v) (fun k => iterate_mem_Icc G f hf k v) hmodal

end UniqueGamesTheorem.Foundations.PCP.PoweringLazy

end

/-! Spectral contraction for the actual Boolean-flag lazy port graph. The
operator identity is proved in `PoweringLazy`; the estimate here averages the
elementary two-term square inequality. -/

namespace UniqueGamesTheorem.Foundations.PCP.LazySpectral

open PoweringWalks SpectralReturn

variable {V D : Type*}

/-- Lazification averages the input and one actual graph step, so its energy
is at most the corresponding average of the two energies. -/
theorem lazy_energy_le_average [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (f : V → ℝ) :
    energy (averagingOperator (lazyGraph G) f) ≤
      (energy f + energy (averagingOperator G f)) / 2 := by
  calc
    energy (averagingOperator (lazyGraph G) f) =
        mean (fun v => ((f v + averagingOperator G f v) / 2) ^ 2) := by
      unfold energy
      congr 1
      funext v
      rw [PoweringLazy.averagingOperator_lazy]
    _ ≤ mean (fun v => (f v ^ 2 + averagingOperator G f v ^ 2) / 2) :=
      mean_mono (fun v => half_sum_sq_le _ _)
    _ = mean (fun v => (1 / 2 : ℝ) * (f v ^ 2 + averagingOperator G f v ^ 2)) := by
      congr 1
      funext v
      ring
    _ = (1 / 2 : ℝ) * (energy f + energy (averagingOperator G f)) := by
      rw [mean_mul_left, mean_add]
      rfl
    _ = (energy f + energy (averagingOperator G f)) / 2 := by ring

/-- The concrete lazy graph inherits a squared-energy bound from an actual
certificate for its underlying graph. -/
theorem lazy_energy_bound [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (lambda : ℝ) (hG : SpectralCertificate G lambda)
    (f : V → ℝ) (hf : mean f = 0) :
    energy (averagingOperator (lazyGraph G) f) ≤
      ((1 + lambda ^ 2) / 2) * energy f := by
  calc
    energy (averagingOperator (lazyGraph G) f) ≤
        (energy f + energy (averagingOperator G f)) / 2 := lazy_energy_le_average G f
    _ ≤ (energy f + lambda ^ 2 * energy f) / 2 := by
      have h := hG.contraction f hf
      linarith
    _ = ((1 + lambda ^ 2) / 2) * energy f := by ring

/-- An actual `7/8` certificate gives the stated `31/32` certificate after
lazification: its intermediate squared-energy factor is `113/128`. -/
theorem lazy_certificate_31_32 [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (hG : SpectralCertificate G (7 / 8)) :
    SpectralCertificate (lazyGraph G) (31 / 32) where
  nonnegative := by norm_num
  lt_one := by norm_num
  contraction f hf := by
    have h := lazy_energy_bound G (7 / 8) hG f hf
    have hcoef : ((1 + (7 / 8 : ℝ) ^ 2) / 2) ≤ (31 / 32 : ℝ) ^ 2 := by norm_num
    exact h.trans (mul_le_mul_of_nonneg_right hcoef (energy_nonnegative f))

end UniqueGamesTheorem.Foundations.PCP.LazySpectral

/-! Actual finite walk averages and their operator representations.
All changes of probability coordinates come from explicit equivalences. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringReturn

open PoweringWalks SpectralReturn
open PoweringMoment (bit)

variable {V D : Type*}

theorem mean_word_cons_head [Fintype D] (n : Nat)
    (F : (Fin (n + 1) → D) → ℝ) :
    mean F = mean (fun d : D => mean (fun r : Fin n → D => F (Fin.cases d r))) := by
  calc
    mean F = mean (fun z : D × (Fin n → D) => F (Fin.cases z.1 z.2)) :=
      (mean_equiv (portConsEquiv D n) F).symm
    _ = _ := mean_prod _

theorem mean_word_cons_tail [Fintype D] (n : Nat)
    (F : (Fin (n + 1) → D) → ℝ) :
    mean F = mean (fun r : Fin n → D => mean (fun d : D => F (Fin.cases d r))) := by
  calc
    mean F = mean (fun z : (Fin n → D) × D => F (Fin.cases z.2 z.1)) :=
      (mean_equiv ((Equiv.prodComm (Fin n → D) D).trans (portConsEquiv D n)) F).symm
    _ = _ := mean_prod _

theorem iterateOperator_succ_right [Fintype D] (G : PortGraph V D)
    (n : Nat) (f : V → ℝ) :
    iterateOperator G n (averagingOperator G f) = iterateOperator G (n + 1) f := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (averagingOperator G) ih

theorem mean_wordEnd [Fintype D] [Nonempty D] (G : PortGraph V D) :
    ∀ (n : Nat) (v : V) (f : V → ℝ),
      mean (fun r : Fin n → D => f (wordEnd G n v r)) = iterateOperator G n f v := by
  intro n
  induction n with
  | zero =>
    intro v f
    change mean (fun _ : Fin 0 → D => f v) = f v
    exact mean_const _
  | succ n ih =>
    intro v f
    rw [mean_word_cons_head]
    change mean (fun d : D => mean (fun r : Fin n → D =>
      f (wordEnd G n (next G v d) r))) = _
    calc
      _ = mean (fun d : D => iterateOperator G n f (next G v d)) := by
        congr 1
        funext d
        exact ih (next G v d) f
      _ = iterateOperator G (n + 1) f v := rfl

/-- Conditional endpoint factorization at an arbitrary fixed pivot dart. -/
theorem mean_pivot_endpoints [Fintype D] [Nonempty D] (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (e : Edge V D) (φ ψ : V → ℝ),
      mean (fun r : Fin n → D =>
        φ (leftFromPivot G n k e.1 r) * ψ (rightFromPivot G n k e r)) =
        iterateOperator G k.val φ e.1 *
          iterateOperator G (n - k.val) ψ (next G e.1 e.2) := by
  intro n
  induction n with
  | zero =>
    intro k e φ ψ
    have hk : k = 0 := Fin.eq_zero k
    subst k
    change mean (fun _ : Fin 0 → D => φ e.1 * ψ (next G e.1 e.2)) =
      φ e.1 * ψ (next G e.1 e.2)
    exact mean_const _
  | succ n ih =>
    intro k e φ ψ
    refine Fin.cases ?_ (fun j => ?_) k
    · change mean (fun r : Fin (n + 1) → D =>
        φ e.1 * ψ (wordEnd G (n + 1) (next G e.1 e.2) r)) =
          φ e.1 * iterateOperator G (n + 1) ψ (next G e.1 e.2)
      rw [mean_mul_left, mean_wordEnd]
    · simp only [Fin.val_succ, Nat.add_sub_add_right]
      rw [mean_word_cons_tail]
      change mean (fun r : Fin n → D => mean (fun d : D =>
        φ (next G (leftFromPivot G n j e.1 r) d) *
          ψ (rightFromPivot G n j e r))) =
        iterateOperator G (j.val + 1) φ e.1 *
          iterateOperator G (n - j.val) ψ (next G e.1 e.2)
      calc
        _ = mean (fun r : Fin n → D =>
            averagingOperator G φ (leftFromPivot G n j e.1 r) *
              ψ (rightFromPivot G n j e r)) := by
          congr 1
          funext r
          rw [mean_mul_right]
          rfl
        _ = iterateOperator G j.val (averagingOperator G φ) e.1 *
            iterateOperator G (n - j.val) ψ (next G e.1 e.2) :=
          ih j e (averagingOperator G φ) ψ
        _ = _ := by rw [iterateOperator_succ_right]

/-- The pivot and both endpoint opinions are averaged over actual walks. -/
theorem mean_edge_endpoints [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (n : Nat) (k : Fin (n + 1)) (φ ψ : Edge V D → V → ℝ) :
    mean (fun w : Walk V D (n + 1) =>
      φ (edgeAt G n w k) w.1 * ψ (edgeAt G n w k) (endpoint G w)) =
      mean (fun e : Edge V D =>
        iterateOperator G k.val (φ e) e.1 *
          iterateOperator G (n - k.val) (ψ e) (next G e.1 e.2)) := by
  let F : Edge V D × (Fin n → D) → ℝ := fun z =>
    φ z.1 (leftFromPivot G n k z.1.1 z.2) *
      ψ z.1 (rightFromPivot G n k z.1 z.2)
  calc
    _ = mean (fun w => F (pivotEquiv G n k w)) := by
      congr 1
      funext w
      dsimp [F]
      rw [leftFromPivot_actual, rightFromPivot_actual, pivotEquiv_fst]
    _ = mean F := mean_equiv (pivotEquiv G n k) F
    _ = mean (fun e : Edge V D => mean (fun r : Fin n → D =>
        φ e (leftFromPivot G n k e.1 r) * ψ e (rightFromPivot G n k e r))) := mean_prod F
    _ = _ := by
      congr 1
      funext e
      exact mean_pivot_endpoints G n k e (φ e) (ψ e)

theorem bit_bool (b : Bool) : bit (b = true) = (if b then 1 else 0 : ℝ) := by
  cases b <;> simp [bit]

theorem mean_edge_bit [Fintype D] (bad : V × D → Bool) (v : V) :
    mean (fun d : D => bit (bad (v, d) = true)) = edgeProfile bad v := by
  simp only [bit_bool, mean, edgeProfile]

theorem mean_marked_bit [Fintype D] (G : PortGraph V D)
    (bad : V × D → Bool) (f : V → ℝ) (v : V) :
    mean (fun d : D => bit (bad (v, d) = true) * f (next G v d)) =
      markedStep G bad f v := by
  change mean (fun d : D => bit (bad (v, d) = true) * f (next G v d)) =
    mean (fun d : D => if bad (v, d) then f (next G v d) else 0)
  congr 1
  funext d
  cases bad (v, d) <;> simp [bit]

theorem edgeAt_zero (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1)) :
    edgeAt G n w 0 = (w.1, w.2 0) := by
  cases n <;> rfl

theorem word_first_hit_mean [Fintype D] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) (n : Nat) (v : V) :
    mean (fun p : Fin (n + 1) → D => bit (bad (edgeAt G n (v, p) 0) = true)) =
      edgeProfile bad v := by
  rw [mean_word_cons_head]
  simp_rw [edgeAt_zero]
  change mean (fun d : D => mean (fun _ : Fin n → D => bit (bad (v, d) = true))) = _
  calc
    _ = mean (fun d : D => bit (bad (v, d) = true)) := by simp only [mean_const]
    _ = edgeProfile bad v := mean_edge_bit bad v

theorem word_hit_mean [Fintype D] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) :
    ∀ (n : Nat) (v : V) (k : Fin (n + 1)),
      mean (fun p : Fin (n + 1) → D => bit (bad (edgeAt G n (v, p) k) = true)) =
        iterateOperator G k.val (edgeProfile bad) v := by
  intro n
  induction n with
  | zero =>
    intro v k
    have hk : k = 0 := Fin.eq_zero k
    subst k
    exact word_first_hit_mean G bad 0 v
  | succ n ih =>
    intro v k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact word_first_hit_mean G bad (n + 1) v
    · rw [mean_word_cons_head]
      change mean (fun d : D => mean (fun p : Fin (n + 1) → D =>
        bit (bad (edgeAt G n (next G v d, p) j) = true))) =
          averagingOperator G (iterateOperator G j.val (edgeProfile bad)) v
      calc
        _ = mean (fun d : D => iterateOperator G j.val (edgeProfile bad) (next G v d)) := by
          congr 1
          funext d
          exact ih (next G v d) j
        _ = _ := rfl

theorem word_pair_hit_mean [Fintype D] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) :
    ∀ (n : Nat) (v : V) (i j : Fin (n + 1)), i < j →
      mean (fun p : Fin (n + 1) → D =>
        bit (bad (edgeAt G n (v, p) i) = true) *
          bit (bad (edgeAt G n (v, p) j) = true)) =
        iterateOperator G i.val (markedStep G bad
          (iterateOperator G (j.val - i.val - 1) (edgeProfile bad))) v := by
  intro n
  induction n with
  | zero =>
    intro v i j hij
    have hi : i = 0 := Fin.eq_zero i
    have hj : j = 0 := Fin.eq_zero j
    subst i
    subst j
    exact ((lt_irrefl _) hij).elim
  | succ n ih =>
    intro v i
    refine Fin.cases ?_ (fun a => ?_) i
    · intro j
      refine Fin.cases ?_ (fun b => ?_) j
      · intro hij
        exact ((lt_irrefl _) hij).elim
      · intro _hij
        simp only [Fin.val_zero, Fin.val_succ, Nat.sub_zero, Nat.add_sub_cancel]
        rw [mean_word_cons_head]
        change mean (fun d : D => mean (fun p : Fin (n + 1) → D =>
          bit (bad (v, d) = true) * bit (bad (edgeAt G n (next G v d, p) b) = true))) =
          markedStep G bad (iterateOperator G b.val (edgeProfile bad)) v
        calc
          _ = mean (fun d : D => bit (bad (v, d) = true) *
              iterateOperator G b.val (edgeProfile bad) (next G v d)) := by
            congr 1
            funext d
            rw [mean_mul_left, word_hit_mean]
          _ = _ := mean_marked_bit G bad _ v
    · intro j
      refine Fin.cases ?_ (fun b => ?_) j
      · intro hij
        exact (Nat.not_lt_zero _ hij).elim
      · intro hij
        have hab : a < b := Nat.lt_of_succ_lt_succ hij
        simp only [Fin.val_succ, Nat.add_sub_add_right]
        rw [mean_word_cons_head]
        change mean (fun d : D => mean (fun p : Fin (n + 1) → D =>
          bit (bad (edgeAt G n (next G v d, p) a) = true) *
            bit (bad (edgeAt G n (next G v d, p) b) = true))) =
          averagingOperator G (iterateOperator G a.val (markedStep G bad
            (iterateOperator G (b.val - a.val - 1) (edgeProfile bad)))) v
        calc
          _ = mean (fun d : D => iterateOperator G a.val (markedStep G bad
              (iterateOperator G (b.val - a.val - 1) (edgeProfile bad))) (next G v d)) := by
            congr 1
            funext d
            exact ih (next G v d) a b hab
          _ = _ := rfl

theorem hit_mean [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) (n : Nat) (k : Fin (n + 1)) :
    mean (fun w : Walk V D (n + 1) => bit (bad (edgeAt G n w k) = true)) =
      edgeDensity bad := by
  calc
    _ = mean (fun v : V => mean (fun p : Fin (n + 1) → D =>
        bit (bad (edgeAt G n (v, p) k) = true))) :=
      mean_prod (A := V) (B := Fin (n + 1) → D)
        (fun w => bit (bad (edgeAt G n w k) = true))
    _ = mean (iterateOperator G k.val (edgeProfile bad)) := by
      congr 1
      funext v
      exact word_hit_mean G bad n v k
    _ = mean (edgeProfile bad) := mean_iterate G k.val _
    _ = _ := rfl

theorem pair_hit_mean [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) (n : Nat)
    (i j : Fin (n + 1)) (hij : i < j) :
    mean (fun w : Walk V D (n + 1) => bit (bad (edgeAt G n w i) = true) *
      bit (bad (edgeAt G n w j) = true)) = returnMass G bad (j.val - i.val - 1) := by
  calc
    _ = mean (fun v : V => mean (fun p : Fin (n + 1) → D =>
        bit (bad (edgeAt G n (v, p) i) = true) *
          bit (bad (edgeAt G n (v, p) j) = true))) :=
      mean_prod (A := V) (B := Fin (n + 1) → D)
        (fun w => bit (bad (edgeAt G n w i) = true) *
          bit (bad (edgeAt G n w j) = true))
    _ = mean (iterateOperator G i.val (markedStep G bad
        (iterateOperator G (j.val - i.val - 1) (edgeProfile bad)))) := by
      congr 1
      funext v
      exact word_pair_hit_mean G bad n v i j hij
    _ = mean (markedStep G bad
        (iterateOperator G (j.val - i.val - 1) (edgeProfile bad))) := mean_iterate G i.val _
    _ = _ := rfl

theorem pair_event_mean [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) (n : Nat)
    (i j : Fin (n + 1)) (hij : i < j) :
    mean (fun w : Walk V D (n + 1) =>
      bit (bad (edgeAt G n w i) = true ∧ bad (edgeAt G n w j) = true)) =
        returnMass G bad (j.val - i.val - 1) := by
  simpa only [PoweringMoment.bit_mul] using pair_hit_mean G bad n i j hij

end UniqueGamesTheorem.Foundations.PCP.PoweringReturn

/-! The second moment of the actual marked-edge count in a consecutive walk
window. Pair events are reduced to the checked spectral return operator. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringMomentBound

open scoped BigOperators
open PoweringWalks SpectralReturn PoweringReturn
open PoweringMoment (bit hits)

theorem symmetric_gap_matrix_sum (ε : ℝ) (r : Nat → ℝ) :
    ∀ (m : Nat) (f : Fin m → Fin m → ℝ),
      (∀ i j, f i j = f j i) → (∀ i, f i i = ε) →
      (∀ i j, i.val < j.val → f i j = r (j.val - i.val - 1)) →
      (∑ i, ∑ j, f i j) = (m : ℝ) * ε +
        2 * ∑ j ∈ Finset.range m, ∑ gap ∈ Finset.range j, r gap := by
  intro m
  induction m with
  | zero => intro f _hSym _hDiag _hUpper; simp
  | succ m ih =>
    intro f hSym hDiag hUpper
    have hOld : (∑ i : Fin m, ∑ j : Fin m, f i.castSucc j.castSucc) =
        (m : ℝ) * ε + 2 * ∑ j ∈ Finset.range m, ∑ gap ∈ Finset.range j, r gap := by
      apply ih (fun i j => f i.castSucc j.castSucc)
      · intro i j; exact hSym i.castSucc j.castSucc
      · intro i; exact hDiag i.castSucc
      · intro i j hij; exact hUpper i.castSucc j.castSucc hij
    have hLast : (∑ i : Fin m, f i.castSucc (Fin.last m)) =
        ∑ gap ∈ Finset.range m, r gap := by
      calc
        _ = ∑ i : Fin m, r (m - 1 - i.val) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hUpper i.castSucc (Fin.last m) i.isLt]
          simp only [Fin.val_last, Fin.val_castSucc]
          congr 1
          omega
        _ = ∑ i ∈ Finset.range m, r (m - 1 - i) :=
          Fin.sum_univ_eq_sum_range (fun i => r (m - 1 - i)) m
        _ = _ := Finset.sum_range_reflect r m
    have hLastRow : (∑ j : Fin m, f (Fin.last m) j.castSucc) =
        ∑ gap ∈ Finset.range m, r gap := by
      calc
        _ = ∑ j : Fin m, f j.castSucc (Fin.last m) := by
          apply Finset.sum_congr rfl
          intro j _
          exact hSym (Fin.last m) j.castSucc
        _ = _ := hLast
    calc
      (∑ i, ∑ j, f i j) =
          (∑ i : Fin m, ∑ j : Fin m, f i.castSucc j.castSucc) +
            (∑ i : Fin m, f i.castSucc (Fin.last m)) +
            (∑ j : Fin m, f (Fin.last m) j.castSucc) + f (Fin.last m) (Fin.last m) := by
        simp only [Fin.sum_univ_castSucc, Finset.sum_add_distrib]
        ring
      _ = (m : ℝ) * ε +
          2 * (∑ j ∈ Finset.range m, ∑ gap ∈ Finset.range j, r gap) +
          (∑ gap ∈ Finset.range m, r gap) + (∑ gap ∈ Finset.range m, r gap) + ε := by
        rw [hOld, hLast, hLastRow, hDiag]
      _ = ((m + 1 : Nat) : ℝ) * ε +
          2 * ∑ j ∈ Finset.range (m + 1), ∑ gap ∈ Finset.range j, r gap := by
        rw [Finset.sum_range_succ]
        simp only [Nat.cast_add, Nat.cast_one]
        ring

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]

def windowEvent (G : PortGraph V D) (bad : V × D → Bool)
    (n start m : Nat) (h : start + m ≤ n + 1) (i : Fin m) (w : Walk V D (n + 1)) : Prop :=
  bad (edgeAt G n w (windowIndex n start m h i)) = true

theorem window_second_moment_eq (G : PortGraph V D) (bad : V × D → Bool)
    (n start m : Nat) (h : start + m ≤ n + 1) :
    mean (fun w => hits (windowEvent G bad n start m h) w ^ 2) =
      (m : ℝ) * edgeDensity bad +
        2 * ∑ j ∈ Finset.range m, ∑ gap ∈ Finset.range j, returnMass G bad gap := by
  rw [show mean (fun w => hits (windowEvent G bad n start m h) w ^ 2) =
      ∑ i, ∑ j, mean (fun w => bit (windowEvent G bad n start m h i w ∧
        windowEvent G bad n start m h j w)) from
    PoweringMoment.second_moment_eq (windowEvent G bad n start m h)]
  apply symmetric_gap_matrix_sum
  · intro i j
    congr 1
    funext w
    simp only [and_comm]
  · intro i
    simp only [and_self]
    exact hit_mean G bad n (windowIndex n start m h i)
  · intro i j hij
    have hwin : windowIndex n start m h i < windowIndex n start m h j :=
      Nat.add_lt_add_left hij start
    have hp := pair_event_mean G bad n (windowIndex n start m h i)
      (windowIndex n start m h j) hwin
    simpa only [windowEvent, windowIndex, Nat.add_sub_add_left] using hp

/-- All moment terms come from actual walk events; the only analytic input
is the stated spectral contraction certificate of the given graph. -/
theorem window_second_moment_le (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e)
    (n start m : Nat) (h : start + m ≤ n + 1) :
    mean (fun w => hits (windowEvent G bad n start m h) w ^ 2) ≤
      (m : ℝ) * edgeDensity bad *
        (1 + 2 / (1 - lambda) + ((m : ℝ) - 1) * edgeDensity bad) := by
  rw [window_second_moment_eq]
  exact secondMoment_return_envelope G lambda certificate bad reversal m

end UniqueGamesTheorem.Foundations.PCP.PoweringMomentBound

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_ZigzagGraphsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTables.graph_ofGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTables.graph_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTables.lookup_ofGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.accepts_ofPortGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.portGraph_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.rotation_ofPortGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables.walkRows_edge _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables.walkRows_head_value _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables.walkRows_tail_value _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Actual graph squares and zigzag products

Rotations operate on actual vertex-port pairs. All returned ports are retained,
including ports belonging to loops and parallel edges. Each construction is a
palindrome of involutions and hence defines a reversible regular port graph.
-/

namespace UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs

open PoweringWalks

variable {V D E : Type*}

/-! ## Exact averaging operators -/

noncomputable section

/-- Average only the inner cloud coordinate, keeping the outer vertex fixed. -/
def cloudOperator [Fintype E] (H : PortGraph D E) (f : V × D → ℝ) (x : V × D) : ℝ :=
  SpectralReturn.mean (fun e => f (x.1, (H.rot (x.2, e)).1))

/-- The permutation on cloud vertices induced by the actual outer rotation. -/
def graphPermutation (G : PortGraph V D) (f : V × D → ℝ) (x : V × D) : ℝ :=
  f (G.rot x)

/-- Uniform averaging on the graph square is two original averaging steps. -/
theorem averagingOperator_square [Fintype D] (G : PortGraph V D) (f : V → ℝ) :
    SpectralReturn.averagingOperator (square G) f =
      SpectralReturn.averagingOperator G (SpectralReturn.averagingOperator G f) := by
  funext v
  let w : D × D → ℝ := fun ds => f (G.rot ((G.rot (v, ds.1)).1, ds.2)).1
  change SpectralReturn.mean w =
    SpectralReturn.mean (fun d₁ => SpectralReturn.mean (fun d₂ => w (d₁, d₂)))
  exact SpectralReturn.mean_prod w

/-- The zigzag operator is precisely inner average, outer permutation, inner
average. This factorization follows from the actual rotation formula. -/
theorem averagingOperator_zigzag [Fintype E] (G : PortGraph V D)
    (H : PortGraph D E) (f : V × D → ℝ) :
    SpectralReturn.averagingOperator (zigzag G H) f =
      cloudOperator H (graphPermutation G (cloudOperator H f)) := by
  funext x
  rcases x with ⟨v, d⟩
  let w : E × E → ℝ := fun es =>
    let first := H.rot (d, es.1)
    let middle := G.rot (v, first.1)
    let last := H.rot (middle.2, es.2)
    f (middle.1, last.1)
  change SpectralReturn.mean w =
    SpectralReturn.mean (fun e₁ => SpectralReturn.mean (fun e₂ => w (e₁, e₂)))
  exact SpectralReturn.mean_prod w

end

end UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs

end

section

/-!
# Energy contraction for the actual zigzag graph

The proof splits a function into its cloud average and its cloud-centered
part. All operators are the actual graph averages from `ZigzagGraphs`.
-/

namespace UniqueGamesTheorem.Foundations.PCP.ZigzagSpectral

open PoweringWalks SpectralReturn ZigzagGraphs

noncomputable section

variable {V D E : Type*}

def cloudMean [Fintype D] (f : V × D → ℝ) (v : V) : ℝ :=
  mean (fun d => f (v, d))

def projection [Fintype D] (f : V × D → ℝ) : V × D → ℝ :=
  liftCloud (cloudMean f)

def centered [Fintype D] (f : V × D → ℝ) : V × D → ℝ := f - projection f

theorem mean_liftCloud [Fintype V] [Fintype D] [Nonempty D] (f : V → ℝ) :
    mean (liftCloud (D := D) f) = mean f := by
  change mean (fun x : V × D => f x.1) = mean f
  rw [mean_prod]
  simp only [mean_const]

theorem energy_liftCloud [Fintype V] [Fintype D] [Nonempty D] (f : V → ℝ) :
    energy (liftCloud (D := D) f) = energy f :=
  mean_liftCloud (D := D) (fun v => f v ^ 2)

theorem mean_cloudMean [Fintype V] [Fintype D] (f : V × D → ℝ) :
    mean (cloudMean f) = mean f := (mean_prod f).symm

theorem energy_prod [Fintype V] [Fintype D] (f : V × D → ℝ) :
    energy f = mean (fun v => energy (fun d => f (v, d))) :=
  mean_prod (fun x => f x ^ 2)

theorem cloudMean_centered_zero [Fintype D] [Nonempty D]
    (f : V × D → ℝ) (v : V) : cloudMean (centered f) v = 0 := by
  change mean (fun d => f (v, d) - cloudMean f v) = 0
  rw [mean_sub, mean_const]
  exact sub_self _

theorem energy_centered_eq_sub [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy (centered f) = energy f - energy (projection f) := by
  have hpoint (v : V) : energy (fun d => centered f (v, d)) =
      energy (fun d => f (v, d)) - (cloudMean f v) ^ 2 := by
    change energy (fun d => f (v, d) - cloudMean f v) = _
    rw [energy_sub_const]
    change energy (fun d => f (v, d)) - 2 * cloudMean f v * cloudMean f v +
      (cloudMean f v) ^ 2 = _
    ring
  have hproj : energy (projection f) = energy (cloudMean f) := energy_liftCloud _
  calc
    energy (centered f) = mean (fun v => energy (fun d => centered f (v, d))) :=
      energy_prod _
    _ = mean (fun v => energy (fun d => f (v, d)) - (cloudMean f v) ^ 2) := by
      congr 1
      funext v
      exact hpoint v
    _ = mean (fun v => energy (fun d => f (v, d))) -
        mean (fun v => (cloudMean f v) ^ 2) := mean_sub _ _
    _ = energy f - energy (projection f) := by
      rw [← energy_prod f, hproj]
      rfl

theorem projection_energy_decomposition [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy f = energy (projection f) + energy (centered f) := by
  rw [energy_centered_eq_sub]
  ring

theorem energy_centered_le [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy (centered f) ≤ energy f := by
  rw [energy_centered_eq_sub]
  exact sub_le_self _ (energy_nonnegative _)

/-- Squared normalized mean is bounded by normalized squared energy. -/
theorem mean_sq_le_energy {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) :
    mean f ^ 2 ≤ energy f := by
  have h := correlation_sq_le f (fun _ => 1)
  simpa [correlation, energy] using h

/-- Every actual reversible regular graph average is an energy contraction. -/
theorem averaging_energy_le [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
    (G : PortGraph V D) (f : V → ℝ) : energy (averagingOperator G f) ≤ energy f := by
  calc
    energy (averagingOperator G f) ≤ mean (averagingOperator G (fun v => f v ^ 2)) := by
      apply mean_mono
      intro v
      exact mean_sq_le_energy (fun d => f (G.rot (v, d)).1)
    _ = energy f := mean_operator G _

theorem cloudOperator_add [Fintype E] (H : PortGraph D E) (f g : V × D → ℝ) :
    cloudOperator H (f + g) = cloudOperator H f + cloudOperator H g := by
  funext x
  exact mean_add _ _

theorem cloudOperator_sub [Fintype E] (H : PortGraph D E) (f g : V × D → ℝ) :
    cloudOperator H (f - g) = cloudOperator H f - cloudOperator H g := by
  funext x
  exact mean_sub _ _

theorem cloudOperator_projection [Fintype D] [Fintype E] [Nonempty E]
    (H : PortGraph D E) (f : V × D → ℝ) : cloudOperator H (projection f) = projection f := by
  funext x
  change mean (fun _ : E => cloudMean f x.1) = cloudMean f x.1
  exact mean_const _

theorem cloudOperator_centered [Fintype D] [Fintype E] [Nonempty E]
    (H : PortGraph D E) (f : V × D → ℝ) :
    cloudOperator H (centered f) = cloudOperator H f - projection f := by
  unfold centered
  rw [cloudOperator_sub, cloudOperator_projection]

theorem graphPermutation_energy [Fintype V] [Fintype D] (G : PortGraph V D)
    (f : V × D → ℝ) : energy (graphPermutation G f) = energy f :=
  mean_equiv G.rot (fun x => f x ^ 2)

theorem cloud_energy_le [Fintype V] [Fintype D] [Fintype E]
    [Nonempty D] [Nonempty E] (H : PortGraph D E) (f : V × D → ℝ) :
    energy (cloudOperator H f) ≤ energy f := by
  calc
    energy (cloudOperator H f) =
        mean (fun v => energy (averagingOperator H (fun d => f (v, d)))) := energy_prod _
    _ ≤ mean (fun v => energy (fun d => f (v, d))) :=
      mean_mono (fun v => averaging_energy_le H _)
    _ = energy f := (energy_prod f).symm

theorem cloud_centered_contraction [Fintype V] [Fintype D] [Fintype E]
    (H : PortGraph D E) (lambda : ℝ) (hH : SpectralCertificate H lambda)
    (f : V × D → ℝ) (hzero : ∀ v, cloudMean f v = 0) :
    energy (cloudOperator H f) ≤ lambda ^ 2 * energy f := by
  calc
    energy (cloudOperator H f) =
        mean (fun v => energy (averagingOperator H (fun d => f (v, d)))) := energy_prod _
    _ ≤ mean (fun v => lambda ^ 2 * energy (fun d => f (v, d))) :=
      mean_mono (fun v => hH.contraction _ (hzero v))
    _ = lambda ^ 2 * mean (fun v => energy (fun d => f (v, d))) := mean_mul_left _ _
    _ = lambda ^ 2 * energy f := by rw [← energy_prod f]

theorem cloud_residual_bound [Fintype V] [Fintype D] [Fintype E]
    [Nonempty D] [Nonempty E] (H : PortGraph D E) (lambda : ℝ)
    (hH : SpectralCertificate H lambda) (f : V × D → ℝ) :
    energy (cloudOperator H f - projection f) ≤ lambda ^ 2 * energy f := by
  rw [← cloudOperator_centered H f]
  exact (cloud_centered_contraction H lambda hH (centered f)
    (cloudMean_centered_zero f)).trans
      (mul_le_mul_of_nonneg_left (energy_centered_le f) (sq_nonneg lambda))

/-- Cloud projection of the outer permutation is the genuine outer graph
average when its input is constant on each cloud. -/
theorem projection_graphPermutation_projection [Fintype D] (G : PortGraph V D)
    (f : V × D → ℝ) :
    projection (graphPermutation G (projection f)) =
      liftCloud (averagingOperator G (cloudMean f)) := rfl

theorem projected_outer_bound [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (lambda : ℝ) (hG : SpectralCertificate G lambda)
    (f : V × D → ℝ) (hf : mean f = 0) :
    energy (projection (graphPermutation G (projection f))) ≤
      lambda ^ 2 * energy (projection f) := by
  have hzero : mean (cloudMean f) = 0 := (mean_cloudMean f).trans hf
  have hleft : energy (projection (graphPermutation G (projection f))) =
      energy (averagingOperator G (cloudMean f)) := by
    rw [projection_graphPermutation_projection]
    exact energy_liftCloud _
  have hright : energy (projection f) = energy (cloudMean f) := energy_liftCloud _
  rw [hleft, hright]
  exact hG.contraction _ hzero

theorem energy_add_three_le {A : Type*} [Fintype A] (a b c : A → ℝ) :
    energy (a + b + c) ≤ 3 * (energy a + energy b + energy c) := by
  calc
    energy (a + b + c) ≤ mean (fun x => 3 * (a x ^ 2 + b x ^ 2 + c x ^ 2)) := by
      apply mean_mono
      intro x
      change (a x + b x + c x) ^ 2 ≤ 3 * (a x ^ 2 + b x ^ 2 + c x ^ 2)
      nlinarith [sq_nonneg (a x - b x), sq_nonneg (a x - c x), sq_nonneg (b x - c x)]
    _ = 3 * (energy a + energy b + energy c) := by
      rw [mean_mul_left, mean_add, mean_add]
      rfl

/-- A deliberately loose bound sufficient for the expander iteration. -/
theorem zigzag_energy_bound [Fintype V] [Fintype D] [Fintype E]
    [Nonempty D] [Nonempty E]
    (G : PortGraph V D) (H : PortGraph D E) (lambdaG lambdaH : ℝ)
    (hG : SpectralCertificate G lambdaG) (hH : SpectralCertificate H lambdaH)
    (f : V × D → ℝ) (hf : mean f = 0) :
    energy (averagingOperator (zigzag G H) f) ≤
      3 * (lambdaG ^ 2 + lambdaH ^ 2) * energy f := by
  let u := projection f
  let v := centered f
  let a := projection (graphPermutation G u)
  let b := cloudOperator H (graphPermutation G u) - a
  let c := cloudOperator H (graphPermutation G (cloudOperator H v))
  have hfactor : averagingOperator (zigzag G H) f = a + b + c := by
    rw [averagingOperator_zigzag]
    have hf' : f = u + v := by
      funext x
      change f x = projection f x + (f x - projection f x)
      ring
    have hbu : cloudOperator H u = u := cloudOperator_projection H f
    have hbf : cloudOperator H f = u + cloudOperator H v := by
      rw [hf', cloudOperator_add, hbu]
    rw [hbf]
    have hp : graphPermutation G (u + cloudOperator H v) =
        graphPermutation G u + graphPermutation G (cloudOperator H v) := rfl
    rw [hp, cloudOperator_add]
    change cloudOperator H (graphPermutation G u) + c =
      a + (cloudOperator H (graphPermutation G u) - a) + c
    funext x
    change cloudOperator H (graphPermutation G u) x + c x =
      a x + (cloudOperator H (graphPermutation G u) x - a x) + c x
    ring
  have ha : energy a ≤ lambdaG ^ 2 * energy u := projected_outer_bound G lambdaG hG f hf
  have hb : energy b ≤ lambdaH ^ 2 * energy u := by
    have h := cloud_residual_bound H lambdaH hH (graphPermutation G u)
    simpa only [graphPermutation_energy] using h
  have hc : energy c ≤ lambdaH ^ 2 * energy v := by
    calc
      energy c ≤ energy (graphPermutation G (cloudOperator H v)) := cloud_energy_le H _
      _ = energy (cloudOperator H v) := graphPermutation_energy G _
      _ ≤ lambdaH ^ 2 * energy v :=
        cloud_centered_contraction H lambdaH hH v (cloudMean_centered_zero f)
  rw [hfactor]
  calc
    energy (a + b + c) ≤ 3 * (energy a + energy b + energy c) := energy_add_three_le _ _ _
    _ ≤ 3 * (lambdaG ^ 2 * energy u + lambdaH ^ 2 * energy u + lambdaH ^ 2 * energy v) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add ha hb) hc) (by norm_num)
    _ ≤ 3 * (lambdaG ^ 2 + lambdaH ^ 2) * energy f := by
      have hdecomp : energy f = energy u + energy v := projection_energy_decomposition f
      rw [hdecomp]
      have hn := mul_nonneg (sq_nonneg lambdaG) (energy_nonnegative v)
      nlinarith

theorem square_certificate [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
    (G : PortGraph V D) (lambda : ℝ) (hG : SpectralCertificate G lambda) :
    SpectralCertificate (square G) (lambda ^ 2) where
  nonnegative := sq_nonneg lambda
  lt_one := by
    have hprod := mul_pos (sub_pos.mpr hG.lt_one)
      (show 0 < 1 + lambda by linarith [hG.nonnegative])
    nlinarith
  contraction f hf := by
    rw [averagingOperator_square]
    calc
      energy (averagingOperator G (averagingOperator G f)) ≤
          lambda ^ 2 * energy (averagingOperator G f) :=
        hG.contraction _ ((mean_operator G f).trans hf)
      _ ≤ lambda ^ 2 * (lambda ^ 2 * energy f) :=
        mul_le_mul_of_nonneg_left (hG.contraction f hf) (sq_nonneg lambda)
      _ = (lambda ^ 2) ^ 2 * energy f := by ring

/-- Squaring an outer graph with certificate `1/2`, then zigzagging with an
inner graph with certificate `1/100`, again has certificate `1/2`. -/
theorem square_zigzag_halfCertificate [Fintype V] [Fintype D] [Fintype E]
    [Nonempty V] [Nonempty D] [Nonempty E]
    (G : PortGraph V D) (H : PortGraph (D × D) E)
    (hG : SpectralCertificate G (1 / 2)) (hH : SpectralCertificate H (1 / 100)) :
    SpectralCertificate (zigzag (square G) H) (1 / 2) where
  nonnegative := by norm_num
  lt_one := by norm_num
  contraction f hf := by
    have h := zigzag_energy_bound (square G) H ((1 / 2 : ℝ) ^ 2) (1 / 100)
      (square_certificate G (1 / 2) hG) hH f hf
    have hcoef : 3 * (((1 / 2 : ℝ) ^ 2) ^ 2 + (1 / 100) ^ 2) ≤ (1 / 2 : ℝ) ^ 2 := by
      norm_num
    exact h.trans (mul_le_mul_of_nonneg_right hcoef (energy_nonnegative f))

end

end UniqueGamesTheorem.Foundations.PCP.ZigzagSpectral

end

section

/-!
# A concrete finite family from the Cayley base

The initial graph has one vertex and the fixed number of loop ports. Each
subsequent graph is the actual square-and-zigzag construction. Consequently
the vertex sizes are exact powers of one fixed integer, including size one.
The finite base is selected from the proved existence theorem.
-/

namespace UniqueGamesTheorem.Foundations.PCP.ExpanderFamily

open PoweringWalks SpectralReturn Expanders

theorem port_degree_ge_eight : 8 ≤ Fintype.card Port := by
  rw [card_port]
  norm_num [baseDegree, initialDegree, basePower]

end UniqueGamesTheorem.Foundations.PCP.ExpanderFamily

end

section

/-!
# Padding actual tail fibers to the geometric graph-family sizes

Every nonempty cloud is padded to the next family size. Empty clouds stay
empty, so their old vertices do not create new darts. Explicit equivalences
identify padded tail fibers and partition all darts by their original tails.
These facts give the global size bound without an expansion assumption.
-/

namespace UniqueGamesTheorem.Foundations.PCP.CloudPadding

open scoped BigOperators
open DegreeReplacement

variable {V E A : Type*}

/-- Every original dart occurs in exactly one cloud. -/
def dartCloudEquiv (G : ConstraintGraph V E A) : E ≃ Σ v : V, Cloud G v where
  toFun e := ⟨G.tail e, ⟨e, rfl⟩⟩
  invFun z := z.2.val
  left_inv _ := rfl
  right_inv := by
    rintro ⟨v, ⟨e, he⟩⟩
    cases he
    rfl

section Finite

variable [Fintype V] [DecidableEq V] [Fintype E]

theorem sum_card_cloud (G : ConstraintGraph V E A) :
    (∑ v, Fintype.card (Cloud G v)) = Fintype.card E := by
  simpa only [Fintype.card_sigma] using (Fintype.card_congr (dartCloudEquiv G)).symm

end Finite

end UniqueGamesTheorem.Foundations.PCP.CloudPadding

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_ExpanderTables
attribute [-instance] _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.accepts_ofPortGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.portGraph_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.rotation_ofPortGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables.walkRows_edge _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables.walkRows_head_value _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables.walkRows_tail_value _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.ExpanderTables

open PoweringWalks SpectralReturn

theorem step_certificate {v d : Nat} [NeZero v] [NeZero d]
    (G : Table v (d * d)) (H : Table ((d * d) * (d * d)) d)
    (hG : SpectralCertificate (graph G) (1 / 2 : ℝ))
    (hH : SpectralCertificate (graph H) (1 / 100 : ℝ)) :
    SpectralCertificate (graph (step G H)) (1 / 2 : ℝ) := by
  rw [step, graph_ofGraph]
  apply GraphTransport.reindex_spectralCertificate
  apply ZigzagSpectral.square_zigzag_halfCertificate
  · exact hG
  · exact GraphTransport.reindex_spectralCertificate _ _ _ _ hH

theorem initial_certificate (d : Nat) :
    SpectralCertificate (graph (initial d)) (1 / 2 : ℝ) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro f hf
  have hfun : f = fun _ => f 0 := funext (fun x => congrArg f (Subsingleton.elim x 0))
  have hm : mean f = f 0 := (congrArg mean hfun).trans (mean_const _)
  have hz : f 0 = 0 := hm.symm.trans hf
  rw [hfun, hz]
  simp [energy, mean, averagingOperator]

theorem vertexCount_positive {q : Nat} (hq : 0 < q) (n : Nat) :
    0 < vertexCount q n := by
  rw [vertexCount_eq]
  exact Nat.pow_pos (Nat.mul_pos hq hq)

theorem family_certificate {d : Nat} [NeZero d]
    (H : Table ((d * d) * (d * d)) d)
    (hH : SpectralCertificate (graph H) (1 / 100 : ℝ)) (n : Nat) :
    SpectralCertificate (graph (family H n)) (1 / 2 : ℝ) := by
  induction n with
  | zero => exact initial_certificate d
  | succ n ih =>
    let : NeZero (vertexCount (d * d) n) :=
      ⟨Nat.ne_of_gt (vertexCount_positive (Nat.mul_pos (NeZero.pos d) (NeZero.pos d)) n)⟩
    exact step_certificate _ _ ih hH

end UniqueGamesTheorem.Foundations.PCP.ExpanderTables

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_OverlayLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.accepts_ofPortGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.portGraph_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.rotation_ofPortGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables.walkRows_edge _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables.walkRows_head_value _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables.walkRows_tail_value _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_reverse_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_reverse_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.paddedG_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Overlay a regular constraint graph with an actual regular port graph whose
new constraints always accept. The port sets are disjoint, so all original
rejected darts are retained exactly. The averaging operator is the actual
degree-weighted mixture of the two graph averages.
-/

open scoped BigOperators

namespace UniqueGamesTheorem.Foundations.PCP.Overlay

open PoweringWalks SpectralReturn

variable {V D E A : Type*}

/-- Every labeling rejects exactly the same number of darts before and after overlay. -/
theorem rejectionCount_eq [Fintype V] [Fintype D] [Fintype E]
    (G : ConstraintGraph V (V × D) A) (H : PortGraph V E)
    (htail : G.tail = Prod.fst) (labeling : V → A) :
    (constraintGraph G H).rejectionCount labeling = G.rejectionCount labeling := by
  classical
  simp only [DegreeReplacement.rejectionCount_eq_sum, Fintype.sum_prod_type,
    Fintype.sum_sum_type]
  simp [edgeSatisfied_inl G H htail]

section Averages

variable [Fintype V] [Fintype D] [Fintype E]

omit [Fintype V] in
/-- The normalized graph average weights the components by their actual port counts. -/
theorem operator_mix [Nonempty D] [Nonempty E]
    (G : PortGraph V D) (H : PortGraph V E) (f : V → ℝ) (v : V) :
    averagingOperator (portGraph G H) f v =
      (Fintype.card D : ℝ) / ((Fintype.card D : ℝ) + Fintype.card E) *
        averagingOperator G f v +
      (Fintype.card E : ℝ) / ((Fintype.card D : ℝ) + Fintype.card E) *
        averagingOperator H f v := by
  have hd : (0 : ℝ) < Fintype.card D := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card D)
  have he : (0 : ℝ) < Fintype.card E := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card E)
  change mean (fun p : D ⊕ E => f ((portGraph G H).rot (v, p)).1) = _
  rw [mean_eq_sum_div_card]
  simp only [Fintype.sum_sum_type, Fintype.card_sum, Nat.cast_add,
    portGraph_rot_inl, portGraph_rot_inr]
  unfold averagingOperator
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  field_simp [hd.ne', he.ne', (add_pos hd he).ne']

/-- Convexity of the squared energy, proved pointwise before taking the finite mean. -/
theorem energy_convex_mix (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (f g : V → ℝ) :
    energy (fun v => a * f v + b * g v) ≤ a * energy f + b * energy g := by
  calc
    energy (fun v => a * f v + b * g v) ≤
        mean (fun v => a * (f v) ^ 2 + b * (g v) ^ 2) := by
      apply mean_mono
      intro v
      have hnormalize := congrArg (fun t : ℝ => t * (a * (f v) ^ 2 + b * (g v) ^ 2)) hab
      have hnonneg := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (f v - g v))
      nlinarith
    _ = a * energy f + b * energy g := by
      rw [mean_add, mean_mul_left, mean_mul_left]
      rfl

/-- Actual overlay contraction from the supplied graph's spectral bound and
the proved energy contraction of an arbitrary reversible regular graph. -/
theorem energy_bound [Nonempty V] [Nonempty D] [Nonempty E]
    (G : PortGraph V D) (H : PortGraph V E) (lambda : ℝ)
    (certificate : SpectralCertificate H lambda) (f : V → ℝ) (hf : mean f = 0) :
    energy (averagingOperator (portGraph G H) f) ≤
      ((Fintype.card D : ℝ) + (Fintype.card E : ℝ) * lambda ^ 2) /
        ((Fintype.card D : ℝ) + Fintype.card E) * energy f := by
  let a : ℝ := (Fintype.card D : ℝ) / ((Fintype.card D : ℝ) + Fintype.card E)
  let b : ℝ := (Fintype.card E : ℝ) / ((Fintype.card D : ℝ) + Fintype.card E)
  have hd : (0 : ℝ) < Fintype.card D := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card D)
  have he : (0 : ℝ) < Fintype.card E := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card E)
  have hden : (0 : ℝ) < (Fintype.card D : ℝ) + Fintype.card E := add_pos hd he
  have ha : 0 ≤ a := div_nonneg hd.le hden.le
  have hb : 0 ≤ b := div_nonneg he.le hden.le
  have hab : a + b = 1 := by
    dsimp [a, b]
    rw [← add_div, div_self hden.ne']
  have hop : averagingOperator (portGraph G H) f =
      fun v => a * averagingOperator G f v + b * averagingOperator H f v := by
    funext v
    exact operator_mix G H f v
  calc
    energy (averagingOperator (portGraph G H) f) ≤
        a * energy (averagingOperator G f) + b * energy (averagingOperator H f) := by
      rw [hop]
      exact energy_convex_mix a b ha hb hab _ _
    _ ≤ a * energy f + b * (lambda ^ 2 * energy f) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (ZigzagSpectral.averaging_energy_le G f) ha)
        (mul_le_mul_of_nonneg_left (certificate.contraction f hf) hb)
    _ = _ := by
      dsimp [a, b]
      ring

/-- With one more original port than overlay ports, a half-spectral overlay
has squared contraction at most three quarters. -/
theorem energy_bound_three_quarters [Nonempty V]
    (G : PortGraph V D) (H : PortGraph V E)
    (hdegree : Fintype.card D = Fintype.card E + 1) (hpositive : 1 ≤ Fintype.card E)
    (certificate : SpectralCertificate H (1 / 2 : ℝ))
    (f : V → ℝ) (hf : mean f = 0) :
    energy (averagingOperator (portGraph G H) f) ≤ (3 / 4 : ℝ) * energy f := by
  let _ : Nonempty E := Fintype.card_pos_iff.mp (lt_of_lt_of_le Nat.zero_lt_one hpositive)
  let _ : Nonempty D := Fintype.card_pos_iff.mp (by omega)
  have he : (1 : ℝ) ≤ Fintype.card E := by exact_mod_cast hpositive
  have hd : (Fintype.card D : ℝ) = (Fintype.card E : ℝ) + 1 := by exact_mod_cast hdegree
  have hden : (0 : ℝ) < (Fintype.card D : ℝ) + Fintype.card E := by linarith
  have hcoefficient :
      ((Fintype.card D : ℝ) + (Fintype.card E : ℝ) * (1 / 2 : ℝ) ^ 2) /
        ((Fintype.card D : ℝ) + Fintype.card E) ≤ (3 / 4 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  exact (energy_bound G H (1 / 2) certificate f hf).trans
    (mul_le_mul_of_nonneg_right hcoefficient (energy_nonnegative f))

theorem spectralCertificate_seven_eighths [Nonempty V]
    (G : PortGraph V D) (H : PortGraph V E)
    (hdegree : Fintype.card D = Fintype.card E + 1) (hpositive : 1 ≤ Fintype.card E)
    (certificate : SpectralCertificate H (1 / 2 : ℝ)) :
    SpectralCertificate (portGraph G H) (7 / 8 : ℝ) where
  nonnegative := by norm_num
  lt_one := by norm_num
  contraction := by
    intro f hf
    exact (energy_bound_three_quarters G H hdegree hpositive certificate f hf).trans
      (mul_le_mul_of_nonneg_right (by norm_num : (3 / 4 : ℝ) ≤ (7 / 8 : ℝ) ^ 2)
        (energy_nonnegative f))

end Averages

end UniqueGamesTheorem.Foundations.PCP.Overlay

end

section

/-! Lazification of the actual constraint graph. Original ports retain their
tests; the equally many stay-put ports always accept. The reverse is precisely
the existing lazy port-graph rotation used by the spectral and walk lemmas. -/
namespace UniqueGamesTheorem.Foundations.PCP.LazyConstraint

open scoped BigOperators
open PoweringWalks

variable {V D A : Type*}

/-- The equality holds for every labeling, including nonsatisfying ones. -/
theorem rejectionCount_eq [Fintype V] [Fintype D]
    (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst)
    (labeling : V → A) :
    (constraintGraph G).rejectionCount labeling = G.rejectionCount labeling := by
  classical
  simp only [DegreeReplacement.rejectionCount_eq_sum, Fintype.sum_prod_type,
    Fintype.sum_bool]
  simp [edgeSatisfied_true G htail]

end UniqueGamesTheorem.Foundations.PCP.LazyConstraint

end

section

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingLevels

/-- At most `fuel` continuing iterations can increment the exponent. -/
theorem levelLoop_level_le (g k fuel e s : Nat) :
    (levelLoop g k fuel e s).1 ≤ e + fuel := by
  induction fuel generalizing e s with
  | zero => simp only [levelLoop, Nat.add_zero, le_refl]
  | succ fuel ih =>
      simp only [levelLoop]
      split
      · omega
      · have h := ih (e + 1) (s * g)
        omega

end UniqueGamesTheorem.Foundations.PCP.PreprocessingLevels

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineCeilingPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCeilingPower

open Turing
open MachineComposition
open UniqueGamesTheorem.Foundations.PCP

protected abbrev Tape.enumList : List Tape := [.input, .work, .power, .saved, .level, .fuel,
  .spare, .product]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

variable {σ : Type}

theorem replicate_encodeWord (a b : Nat) :
    List.replicate a true ++ encodeWord b = encodeWord (a + b) := by
  simp only [encodeWord, ← List.append_assoc, List.replicate_append_replicate]

theorem coreTime_le (g k f p : Nat) :
    coreTime g k f p ≤ (f + 1) * roundBudget g k := by
  have hB : 3 ≤ roundBudget g k := by unfold roundBudget; omega
  induction f generalizing p with
  | zero => simpa only [coreTime, Nat.zero_add, Nat.one_mul] using hB
  | succ f ih =>
      rw [coreTime]
      by_cases h : k ≤ p
      · rw [ite_eq_left h]
        have hp := prefixTime_le_roundBudget g k p
        have hm := Nat.mul_le_mul_left (f + 1) hB
        have hc : f + 2 ≤ (f + 1) * roundBudget g k := by omega
        calc
          prefixTime k p + (f + 2) ≤ roundBudget g k + (f + 1) * roundBudget g k :=
            Nat.add_le_add hp hc
          _ = (f + 1 + 1) * roundBudget g k := by ring
      · rw [ite_eq_right h]
        have hb := continuingTime_le g k p (by omega)
        have hr := ih (p * g)
        calc
          prefixTime k p + ((p + g * p + 2) + coreTime g k f (p * g)) =
              (prefixTime k p + (p + g * p + 2)) + coreTime g k f (p * g) := by omega
          _ ≤ roundBudget g k + (f + 1) * roundBudget g k := Nat.add_le_add hb hr
          _ = (f + 1 + 1) * roundBudget g k := by ring

theorem totalTime_le (g k : Nat) : totalTime g k ≤ timeBound g k := by
  have h := coreTime_le g k k 1
  calc
    totalTime g k ≤ 1 + 2 * (k + 2) + (k + 1) * roundBudget g k :=
      Nat.add_le_add_left h _
    _ = timeBound g k := by unfold roundBudget timeBound; ring

theorem timePolynomial_encoding (g k : Nat) :
    (timePolynomial g).eval (encodeWord k).length = timeBound g k := by
  simp [timePolynomial, timeBound, encodeWord_length]

end UniqueGamesTheorem.Foundations.Complexity.MachineCeilingPower

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_SourceMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceMachine

open Turing
open UniqueGamesTheorem.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K]

/-- Stack state after one completed field, retaining an arbitrary old destination. -/
def afterField (source destination : K) (base : K → List Bool)
    (n : Nat) (suffix : List Bool) : K → List Bool :=
  fieldTapes source destination base suffix (encodeWord n ++ base destination)

end UniqueGamesTheorem.Foundations.Hastad.SourceMachine

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineLookupCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite control for destructive unary-indexed table lookup. The guard decreases
the index even when the table is exhausted. Selection tests for an empty table
before writing the destination. All tests inspect just one finite head register.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineLookup

open Turing

variable {K Λ σ : Type} [DecidableEq K]

theorem tapes_other (index source destination p : K)
    (hi : p ≠ index) (hs : p ≠ source) (hd : p ≠ destination)
    (base : K → List Bool) (counter input output : List Bool) :
    tapes index source destination base counter input output p = base p := by
  simp [tapes, hi, hs, hd]

theorem update_index (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination)
    (base : K → List Bool) (counter input output replacement : List Bool) :
    Function.update (tapes index source destination base counter input output) index replacement =
      tapes index source destination base replacement input output := by
  funext p
  by_cases hi : p = index
  · subst p; simp [tapes, his, hid]
  · by_cases hs : p = source
    · subst p; by_cases hs : source = destination <;> simp [tapes, hi, hs, Ne.symm hid]
    · by_cases hd : p = destination
      · subst p; simp [tapes, hi]
      · simp [tapes, hi, hs, hd]

theorem update_source (index source destination : K) (hsd : source ≠ destination)
    (base : K → List Bool) (counter input output replacement : List Bool) :
    Function.update (tapes index source destination base counter input output) source replacement =
      tapes index source destination base counter replacement output := by
  funext p
  by_cases hs : p = source
  · subst p; simp [tapes, hsd]
  · by_cases hd : p = destination
    · subst p; simp [tapes, hs]
    · simp [tapes, hs, hd]

theorem update_destination (index source destination : K)
    (base : K → List Bool) (counter input output replacement : List Bool) :
    Function.update (tapes index source destination base counter input output)
      destination replacement = tapes index source destination base counter input replacement := by
  simp [tapes]

theorem fieldTapes_eq (index source destination : K) (hsd : source ≠ destination)
    (base : K → List Bool) (counter input output input' output' : List Bool) :
    Hastad.SourceMachine.fieldTapes source destination
      (tapes index source destination base counter input output) input' output' =
      tapes index source destination base counter input' output' := by
  rw [Hastad.SourceMachine.fieldTapes, update_source _ _ _ hsd, update_destination]

end UniqueGamesTheorem.Foundations.Complexity.MachineLookup

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineLookupDiscard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Execution of the destructive field-discard loop in an arbitrary ambient TM2
program. The scanner consumes a unary payload and its delimiter, preserves the
ambient state and other tapes, and clears its head register on return. At EOF it
returns immediately, leaving the tapes unchanged.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineLookup

open Turing

variable {K Λ σ : Type} [DecidableEq K]

theorem discardStep_delimiter (source : K) (loopLabel returnLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = discard source loopLabel returnLabel)
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, register), Function.update base source (false :: suffix)⟩ =
      some ⟨some returnLabel, (ambient, none), Function.update base source suffix⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (Function.update base source (false :: suffix))) = _
  rw [atLoop]
  simp [discard, TM2.stepAux]

theorem discardStep_true (source : K) (loopLabel returnLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = discard source loopLabel returnLabel)
    (base : K → List Bool) (input : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, register), Function.update base source (true :: input)⟩ =
      some ⟨some loopLabel, (ambient, some true), Function.update base source input⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (Function.update base source (true :: input))) = _
  rw [atLoop]
  simp [discard, TM2.stepAux]

/-- A normalized tape form for the field-discard trace. -/
theorem discardTrace_update (source : K) (loopLabel returnLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = discard source loopLabel returnLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some loopLabel, (ambient, register),
        Function.update base source (encodeWord n ++ suffix)⟩) =
      some ⟨some returnLabel, (ambient, none), Function.update base source suffix⟩ := by
  induction n generalizing register with
  | zero =>
    simpa only [Nat.zero_add, Function.iterate_one, MachineComposition.advance_some,
      encodeWord, List.replicate_zero, List.nil_append, List.singleton_append] using
      discardStep_delimiter source loopLabel returnLabel program atLoop
        base suffix ambient register
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    simp only [encodeWord, List.replicate_succ, List.cons_append]
    change (MachineComposition.advance (TM2.step program))^[n + 1]
      (TM2.step program ⟨some loopLabel, (ambient, register),
        Function.update base source (true :: (encodeWord n ++ suffix))⟩) = _
    rw [discardStep_true source loopLabel returnLabel program atLoop, ih]

/-- Discard exactly the first encoded field, in one transition per payload bit
plus one transition for its delimiter. No condition is imposed on other tapes. -/
theorem discardTrace (source : K) (loopLabel returnLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = discard source loopLabel returnLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (hinput : base source = encodeWord n ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some loopLabel, (ambient, register), base⟩) =
      some ⟨some returnLabel, (ambient, none), Function.update base source suffix⟩ := by
  have hbase : Function.update base source (encodeWord n ++ suffix) = base := by
    funext p
    by_cases hp : p = source
    · subst p; simp [hinput]
    · simp [hp]
  have h := discardTrace_update source loopLabel returnLabel program atLoop
    base n suffix ambient register
  rw [hbase] at h
  exact h

/-- The same exact trace packaged for composition with ambient machine phases. -/
def discardInTime (source : K) (loopLabel returnLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = discard source loopLabel returnLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (hinput : base source = encodeWord n ++ suffix)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some loopLabel, (ambient, register), base⟩
      (some ⟨some returnLabel, (ambient, none), Function.update base source suffix⟩)
      (n + 1) where
  steps := n + 1
  evals_in_steps := discardTrace source loopLabel returnLabel program atLoop
    base n suffix hinput ambient register
  steps_le_m := Nat.le_refl _

end UniqueGamesTheorem.Foundations.Complexity.MachineLookup

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineCloudCount
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCloudPadding.countMemory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCloudCount

open Turing
open MachineComposition

abbrev Alphabet (_ : Tape) := Bool

variable {Λ σ : Type}

def finishField (restore : Λ) : TM2.Stmt Alphabet Λ (State σ) :=
  .load (fun state => ((state.1.1, false), none)) (.goto fun _ => restore)

def fieldLoop (again restore : Λ) : TM2.Stmt Alphabet Λ (State σ) :=
  .pop .work (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.peek .target (fun state head => (state.1, head))
        (.branch (fun state => state.2.getD false)
          (.pop .target (fun state _ => (state.1, none))
            (.push .scratch (fun _ => true) (.goto fun _ => again)))
          (.load (fun state => ((state.1.1, true), none)) (.goto fun _ => again))))
      (.peek .target (fun state head => (state.1, head))
        (.branch (fun state => !state.1.2 && !(state.2.getD false))
          (.push .count (fun _ => true) (finishField restore))
          (finishField restore))))

theorem fieldStep_zero (again restore : Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (atField : program again = fieldLoop again restore)
    (original suffix targetSuffix spare : List Bool) (v : Nat)
    (scratch count : List Bool) (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program
      ⟨some again, ((ambient, flag), register),
        memory original (encodeWord 0 ++ suffix) (encodeWord v ++ targetSuffix)
          scratch count spare⟩ =
      some ⟨some restore, ((ambient, false), none),
        memory original suffix (encodeWord v ++ targetSuffix) scratch
          (List.replicate (hit flag 0 v) true ++ count) spare⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atField]
  cases v <;> cases flag <;>
    simp [fieldLoop, finishField, TM2.stepAux, encodeWord, hit, List.replicate_succ]

theorem fieldStep_succ_zero (again restore : Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (atField : program again = fieldLoop again restore)
    (original suffix targetSuffix spare : List Bool) (x : Nat)
    (scratch count : List Bool) (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program
      ⟨some again, ((ambient, flag), register),
        memory original (encodeWord (x + 1) ++ suffix) (encodeWord 0 ++ targetSuffix)
          scratch count spare⟩ =
      some ⟨some again, ((ambient, true), none),
        memory original (encodeWord x ++ suffix) (encodeWord 0 ++ targetSuffix)
          scratch count spare⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atField]
  simp [fieldLoop, TM2.stepAux, encodeWord, List.replicate_succ]

theorem fieldStep_succ_succ (again restore : Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (atField : program again = fieldLoop again restore)
    (original suffix targetSuffix spare : List Bool) (x v : Nat)
    (scratch count : List Bool) (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program
      ⟨some again, ((ambient, flag), register),
        memory original (encodeWord (x + 1) ++ suffix)
          (encodeWord (v + 1) ++ targetSuffix) scratch count spare⟩ =
      some ⟨some again, ((ambient, flag), none),
        memory original (encodeWord x ++ suffix) (encodeWord v ++ targetSuffix)
          (true :: scratch) count spare⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atField]
  simp [fieldLoop, TM2.stepAux, encodeWord, List.replicate_succ]

/-- The actual field-reading trace. The scratch holds exactly the consumed
target bits, and the output increment records equality of the complete field. -/
theorem fieldTrace (again restore : Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (atField : program again = fieldLoop again restore)
    (original suffix targetSuffix spare : List Bool) (x v : Nat)
    (scratch count : List Bool) (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step program))^[x + 1]
      (some ⟨some again, ((ambient, flag), register),
        memory original (encodeWord x ++ suffix) (encodeWord v ++ targetSuffix)
          scratch count spare⟩) =
      some ⟨some restore, ((ambient, false), none),
        memory original suffix (encodeWord (v - x) ++ targetSuffix)
          (List.replicate (min x v) true ++ scratch)
          (List.replicate (hit flag x v) true ++ count) spare⟩ := by
  induction x generalizing v scratch flag register with
  | zero =>
      simpa only [Nat.zero_add, Function.iterate_one, advance_some, Nat.sub_zero,
        Nat.zero_min, List.replicate_zero, List.nil_append] using
        fieldStep_zero again restore program atField original suffix targetSuffix spare v
          scratch count ambient flag register
  | succ x ih =>
      rw [Function.iterate_succ_apply]
      change (advance (TM2.step program))^[x + 1]
        (TM2.step program ⟨some again, ((ambient, flag), register),
          memory original (encodeWord (x + 1) ++ suffix) (encodeWord v ++ targetSuffix)
            scratch count spare⟩) = _
      cases v with
      | zero =>
          rw [fieldStep_succ_zero again restore program atField]
          simpa [hit] using ih 0 scratch true none
      | succ v =>
          rw [fieldStep_succ_succ again restore program atField]
          simpa [hit, Nat.succ_min_succ, List.replicate_succ', List.append_assoc] using
            ih v (true :: scratch) flag none

theorem replicate_encodeWord (a b : Nat) :
    List.replicate a true ++ encodeWord b = encodeWord (a + b) := by
  simp only [encodeWord, ← List.append_assoc, List.replicate_append_replicate]

/-- The actual restoring transfer returns every consumed target bit. -/
theorem preservingFieldTrace (again restore next : Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (atField : program again = fieldLoop again restore)
    (atRestore : program restore = Reduction.MachineTransfer.loopAt
      .scratch .target id false restore (some next))
    (original suffix targetSuffix count spare : List Bool) (x v : Nat)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[x + min x v + 2]
      (some ⟨some again, ((ambient, false), register),
        memory original (encodeWord x ++ suffix) (encodeWord v ++ targetSuffix)
          [] count spare⟩) =
      some ⟨some next, ((ambient, false), none),
        memory original suffix (encodeWord v ++ targetSuffix) []
          (List.replicate (if x = v then 1 else 0) true ++ count) spare⟩ := by
  have hfield := fieldTrace again restore program atField original suffix targetSuffix spare
    x v [] count ambient false register
  simp only [List.append_nil, hit, true_and] at hfield
  let after := memory original suffix (encodeWord (v - x) ++ targetSuffix)
    (List.replicate (min x v) true)
    (List.replicate (if x = v then 1 else 0) true ++ count) spare
  have hrestore := Reduction.MachineTransfer.transferAt_fromTapes
    Tape.scratch Tape.target (by decide) id false restore (some next) program atRestore
      after (ambient, false) none
  have hsum : min x v + (v - x) = v := by omega
  simp only [after, memory_scratch, memory_target, List.length_replicate,
    List.reverse_replicate, List.map_id, Reduction.MachineTransfer.tapesAt,
    update_memory_scratch, update_memory_target] at hrestore
  rw [← List.append_assoc, replicate_encodeWord, hsum] at hrestore
  rw [show x + min x v + 2 = (min x v + 1) + (x + 1) by omega,
    Function.iterate_add_apply, hfield]
  exact hrestore

/-- Consecutive concrete field-discard instructions consume a fixed list of
fields. The hypotheses specify code, not an abstract body execution. -/
theorem discardFieldsTrace (labels : Nat → Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (fields : List Nat) (offset : Nat)
    (atField : ∀ i, i < fields.length → program (labels (offset + i)) =
      MachineLookup.discard .work (labels (offset + i)) (labels (offset + i + 1)))
    (original suffix target scratch count spare : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step program))^[(encodeWords fields).length]
      (some ⟨some (labels offset), ((ambient, flag), register),
        memory original (encodeWords fields ++ suffix) target scratch count spare⟩) =
      some ⟨some (labels (offset + fields.length)),
        ((ambient, flag), if fields = [] then register else none),
        memory original suffix target scratch count spare⟩ := by
  induction fields generalizing offset register with
  | nil => simp only [encodeWords, List.length_nil, Function.iterate_zero_apply,
      List.nil_append, Nat.add_zero, ↓reduceIte]
  | cons x fields ih =>
      have hfirst := MachineLookup.discardTrace Tape.work (labels offset) (labels (offset + 1))
        program (by simpa only [Nat.add_zero] using atField 0 (by simp))
        (memory original (encodeWords (x :: fields) ++ suffix) target scratch count spare)
        x (encodeWords fields ++ suffix) (by simp only [memory_work, encodeWords, List.append_assoc])
        (ambient, flag) register
      simp only [update_memory_work] at hfirst
      have hrest := ih (offset + 1) (by
        intro i hi
        have h := atField (i + 1) (by simpa only [List.length_cons] using Nat.succ_lt_succ hi)
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h) none
      rw [show (encodeWords (x :: fields)).length =
          (encodeWords fields).length + (x + 1) by
          simp only [encodeWords, List.length_append, encodeWord_length]
          omega,
        Function.iterate_add_apply, hfirst]
      simpa only [List.length_cons, List.cons_ne_nil,
        ite_false, if_false, ite_self, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest

def rowEntry : TM2.Stmt Alphabet Label (State σ) :=
  .peek .work (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.load (fun state => ((state.1.1, false), none)) (.goto fun _ => .field))
      (.load (fun state => ((state.1.1, false), none)) .halt))

/-- A single fixed program copies the input once, skips two headers, then
compares the first field of each 4098-field row. -/
def program : Label → TM2.Stmt Alphabet Label (State σ)
  | .copyFirst => Reduction.MachineTransfer.loopAt
      .original .spare id false .copyFirst (some .copySecond)
  | .copySecond => MachineCopy.forkLoop
      .spare .original .work false .copySecond (some .headerFirst)
  | .headerFirst => MachineLookup.discard .work .headerFirst .headerSecond
  | .headerSecond => MachineLookup.discard .work .headerSecond .row
  | .row => rowEntry
  | .field => fieldLoop .field .restore
  | .restore => Reduction.MachineTransfer.loopAt
      .scratch .target id false .restore (some (skipLabel 0))
  | .skip i => MachineLookup.discard .work (.skip i) (skipLabel (i.val + 1))

theorem program_skip {i : Nat} (hi : i < 4097) :
    program (σ := σ) (skipLabel i) =
      MachineLookup.discard .work (skipLabel i) (skipLabel (i + 1)) := by
  simp only [skipLabel, dite_eq_left hi, program]

theorem rowStep_nonempty (original work target scratch count spare : List Bool)
    (hwork : work ≠ []) (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (program (σ := σ))
      ⟨some .row, ((ambient, flag), register), memory original work target scratch count spare⟩ =
      some ⟨some .field, ((ambient, false), none),
        memory original work target scratch count spare⟩ := by
  cases work with
  | nil => exact (hwork rfl).elim
  | cons x xs => rfl

theorem rowStep_empty (original target scratch count spare : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (program (σ := σ))
      ⟨some .row, ((ambient, flag), register), memory original [] target scratch count spare⟩ =
      some ⟨none, ((ambient, false), none), memory original [] target scratch count spare⟩ := rfl

def rowTime (v : Nat) (r : Row) : Nat :=
  (encodeWords (rowWords r)).length + min r.1 v + 2

/-- One complete stored row is consumed; the target and original are restored. -/
theorem rowTrace (r : Row) (hwidth : r.2.length = 4097) (v : Nat)
    (original suffix targetSuffix count spare : List Bool) (ambient : σ)
    (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[rowTime v r]
      (some ⟨some .row, ((ambient, false), register),
        memory original (encodeWords (rowWords r) ++ suffix) (encodeWord v ++ targetSuffix)
          [] count spare⟩) =
      some ⟨some .row, ((ambient, false), none),
        memory original suffix (encodeWord v ++ targetSuffix) []
          (List.replicate (if r.1 = v then 1 else 0) true ++ count) spare⟩ := by
  have hfield := preservingFieldTrace Label.field Label.restore (skipLabel 0)
    program rfl rfl original (encodeWords r.2 ++ suffix) targetSuffix count spare r.1 v ambient none
  have hskip := discardFieldsTrace skipLabel (program (σ := σ)) r.2 0
    (by intro i hi; simpa only [Nat.zero_add] using program_skip (hwidth ▸ hi))
    original suffix (encodeWord v ++ targetSuffix) []
    (List.replicate (if r.1 = v then 1 else 0) true ++ count) spare ambient false none
  have hnonempty : r.2 ≠ [] := by intro h; simp [h] at hwidth
  simp only [Nat.zero_add, hwidth, skipLabel, lt_self_iff_false, ↓reduceDIte,
    hnonempty, ite_false, if_false] at hskip
  have htime : rowTime v r = (encodeWords r.2).length + (r.1 + min r.1 v + 2) + 1 := by
    simp only [rowTime, rowWords, encodeWords, List.length_append, encodeWord_length]
    omega
  rw [htime, Function.iterate_succ_apply]
  change (advance (TM2.step (program (σ := σ))))^[
      (encodeWords r.2).length + (r.1 + min r.1 v + 2)]
    (TM2.step program ⟨some .row, ((ambient, false), register),
      memory original (encodeWords (rowWords r) ++ suffix) (encodeWord v ++ targetSuffix)
        [] count spare⟩) = _
  rw [rowStep_nonempty original _ _ [] count spare
    (by simp [rowWords, encodeWords, encodeWord]) ambient false register,
    Function.iterate_add_apply]
  simp only [rowWords, encodeWords, List.append_assoc]
  rw [hfield]
  exact hskip

def rowsTime (v : Nat) : List Row → Nat
  | [] => 1
  | r :: rs => rowsTime v rs + rowTime v r

/-- The complete actual row scan halts with the number of matching tails. -/
theorem rowsTrace (rs : List Row) (hwidth : ∀ r ∈ rs, r.2.length = 4097) (v : Nat)
    (original targetSuffix count spare : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[rowsTime v rs]
      (some ⟨some .row, ((ambient, false), register),
        memory original (encodeWords (rs.flatMap rowWords)) (encodeWord v ++ targetSuffix)
          [] count spare⟩) =
      some ⟨none, ((ambient, false), none),
        memory original [] (encodeWord v ++ targetSuffix) []
          (List.replicate (rowsHits v rs) true ++ count) spare⟩ := by
  induction rs generalizing count register with
  | nil =>
      simpa only [rowsTime, List.flatMap_nil, encodeWords, Function.iterate_one, advance_some,
        rowsHits, List.replicate_zero, List.nil_append] using
        rowStep_empty original (encodeWord v ++ targetSuffix) [] count spare ambient false register
  | cons r rs ih =>
      have hrow := rowTrace r (hwidth r (by simp)) v original
        (encodeWords (rs.flatMap rowWords)) targetSuffix count spare ambient register
      have hrest := ih (by intro x hx; exact hwidth x (by simp [hx]))
        (List.replicate (if r.1 = v then 1 else 0) true ++ count) none
      simp only [rowsTime, List.flatMap_cons, encodeWords_append]
      rw [Function.iterate_add_apply, hrow]
      simpa only [rowsHits, ← List.append_assoc, List.replicate_append_replicate,
        Nat.add_comm] using hrest

theorem rowTime_le (v : Nat) (r : Row) :
    rowTime v r ≤ 3 * (encodeWords (rowWords r)).length := by
  have hmin := Nat.min_le_left r.1 v
  have hlen : r.1 + 1 ≤ (encodeWords (rowWords r)).length := by
    simp only [rowWords, encodeWords, List.length_append, encodeWord_length]
    omega
  unfold rowTime
  omega

theorem rowsTime_le (v : Nat) (rs : List Row) :
    rowsTime v rs ≤ 3 * (encodeWords (rs.flatMap rowWords)).length + 1 := by
  induction rs with
  | nil => simp only [rowsTime, List.flatMap_nil, encodeWords, List.length_nil,
      Nat.mul_zero, Nat.zero_add, le_refl]
  | cons r rs ih =>
      have hr := rowTime_le v r
      simp only [rowsTime, List.flatMap_cons, encodeWords_append, List.length_append]
      omega

def inputWord (n m : Nat) (rs : List Row) : List Bool :=
  encodeWords ([n, m] ++ rs.flatMap rowWords)

theorem inputWord_eq (n m : Nat) (rs : List Row) :
    inputWord n m rs = encodeWord n ++ (encodeWord m ++ encodeWords (rs.flatMap rowWords)) := by
  simp only [inputWord, encodeWords_append, encodeWords, List.append_nil, List.append_assoc]

theorem inputWord_length (n m : Nat) (rs : List Row) :
    (inputWord n m rs).length = n + 1 + (m + 1) +
      (encodeWords (rs.flatMap rowWords)).length := by
  rw [inputWord_eq]
  simp only [List.length_append, encodeWord_length]
  omega

def totalSteps (n m v : Nat) (rs : List Row) : Nat :=
  2 * ((inputWord n m rs).length + 1) + (n + 1) + (m + 1) + rowsTime v rs

/-- One preserving copy, the two concrete header discards, and the proved row
scan form the complete execution. The input and target tapes are unchanged. -/
theorem countTrace (n m v : Nat) (rs : List Row)
    (hwidth : ∀ r ∈ rs, r.2.length = 4097)
    (targetSuffix count : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[totalSteps n m v rs]
      (some ⟨some .copyFirst, ((ambient, false), register),
        memory (inputWord n m rs) [] (encodeWord v ++ targetSuffix) [] count []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (inputWord n m rs) [] (encodeWord v ++ targetSuffix) []
          (List.replicate (rowsHits v rs) true ++ count) []⟩ := by
  have hcopy := MachineCopy.copyTrace Tape.original Tape.work Tape.spare
    (by decide) (by decide) (by decide) false Label.copyFirst Label.copySecond
    (some Label.headerFirst) program rfl rfl
    (memory (inputWord n m rs) [] (encodeWord v ++ targetSuffix) [] count [])
    rfl (ambient, false) register
  simp only [memory_original, memory_work, List.append_nil, update_memory_work] at hcopy
  have hfirst := MachineLookup.discardTrace Tape.work Label.headerFirst Label.headerSecond
    program rfl
    (memory (inputWord n m rs) (inputWord n m rs) (encodeWord v ++ targetSuffix) [] count [])
    n (encodeWord m ++ encodeWords (rs.flatMap rowWords))
    (by exact inputWord_eq n m rs) (ambient, false) none
  simp only [update_memory_work] at hfirst
  have hsecond := MachineLookup.discardTrace Tape.work Label.headerSecond Label.row
    program rfl
    (memory (inputWord n m rs) (encodeWord m ++ encodeWords (rs.flatMap rowWords))
      (encodeWord v ++ targetSuffix) [] count [])
    m (encodeWords (rs.flatMap rowWords)) rfl (ambient, false) none
  simp only [update_memory_work] at hsecond
  have hrows := rowsTrace rs hwidth v (inputWord n m rs) targetSuffix count [] ambient none
  rw [show totalSteps n m v rs = rowsTime v rs + ((m + 1) + ((n + 1) +
      2 * ((inputWord n m rs).length + 1))) by unfold totalSteps; omega,
    Function.iterate_add_apply _ (rowsTime v rs),
    Function.iterate_add_apply _ (m + 1), Function.iterate_add_apply _ (n + 1),
    hcopy, hfirst, hsecond]
  exact hrows

theorem totalSteps_le (n m v : Nat) (rs : List Row) :
    totalSteps n m v rs ≤ 5 * (inputWord n m rs).length + 3 := by
  have hrows := rowsTime_le v rs
  have hlen := inputWord_length n m rs
  unfold totalSteps
  omega

open UniqueGamesTheorem.Foundations.PCP

theorem rowsHits_eq_filter (v : Nat) (rs : List Row) :
    rowsHits v rs = (rs.filter (fun r => decide (r.1 = v))).length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      by_cases h : r.1 = v <;> simp [rowsHits, h, ih, Nat.add_comm]

end UniqueGamesTheorem.Foundations.Complexity.MachineCloudCount

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineCloudPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual cloud counting, geometric padding, and unary subtraction

One finite program places the checked cloud counter and geometric search on
shared tapes. Its final phase physically subtracts the preserved cloud size
from the computed power. A head test handles the empty cloud separately.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCloudPadding

open Turing
open MachineComposition
open UniqueGamesTheorem.Foundations.PCP

/- Static placement of homogeneous tapes, with an explicit finite partial
inverse. Complement tapes are preserved by every simulated transition. -/

abbrev Alphabet (_ : Tape) := Bool

def countTape : MachineCloudCount.Tape → Tape
  | .original => .table
  | .target => .query
  | .count => .count
  | .work => .work
  | .scratch => .scratch
  | .spare => .spare

theorem countView_left (k : MachineCloudCount.Tape) : countView (countTape k) = some k := by
  cases k <;> rfl
theorem countView_right (j : Tape) (k : MachineCloudCount.Tape)
    (h : countView j = some k) : countTape k = j := by
  cases j <;> cases k <;> simp_all [countView, countTape]

def powerTape : MachineCeilingPower.Tape → Tape
  | .input => .count
  | .work => .work
  | .power => .power
  | .saved => .scratch
  | .level => .level
  | .fuel => .fuel
  | .spare => .spare
  | .product => .product

variable {σ : Type}

def postTime (k : Nat) : Nat :=
  1 + if k = 0 then 0 else MachineCeilingPower.totalTime ExpanderFamily.growth k + (2 * k + 2)

theorem postTime_le (k : Nat) :
    postTime k ≤ 1 + MachineCeilingPower.timeBound ExpanderFamily.growth k + (2 * k + 2) := by
  have h := MachineCeilingPower.totalTime_le ExpanderFamily.growth k
  unfold postTime
  split_ifs <;> omega

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C (ExpanderFamily.growth + 8) * Polynomial.X ^ 2 + 25 * Polynomial.X + 10

end UniqueGamesTheorem.Foundations.Complexity.MachineCloudPadding

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_TensorBucketEvaluationLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.TensorProjectedSlice

noncomputable section

open scoped TensorProduct
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

variable {K H H' : Type*} [AddCommGroup K] [Module F2 K]
  [AddCommGroup H] [Module F2 H] [AddCommGroup H'] [Module F2 H']
  [FiniteDimensional F2 H']
  (i : H' →ₗ[F2] H) (W : Submodule F2 K)

def totalMatrix (X₀ : Module.Dual F2 H →ₗ[F2] K) (T : W ⊗[F2] H') :
    Module.Dual F2 H →ₗ[F2] K :=
  X₀ + W.subtype.comp ((TensorRestriction.tensorEquivHom T).comp i.dualMap)

@[simp] theorem totalMatrix_apply (X₀ : Module.Dual F2 H →ₗ[F2] K)
    (T : W ⊗[F2] H') (z : Module.Dual F2 H) :
    totalMatrix i W X₀ T z =
      X₀ z + (TensorRestriction.tensorEquivHom T (i.dualMap z) : K) := rfl

end
end PerfectCompleteness.TensorProjectedSlice



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CollisionAveragingLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.ProjectionPosterior

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness SmallBias SparseProjection CleanConditioning

noncomputable section

def bernoulli (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) : FiniteDistribution Bool where
  weight b := if b then p else 1 - p
  nonnegative b := by cases b <;> simp [hp, sub_nonneg.mpr hp']
  normalized := by simp

end
end PerfectCompleteness.ProjectionPosterior


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalFrozenTablesLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.GeometricCutSplit

open RecursiveSpaces DescendantSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

variable {branch : Nat → Nat}

instance prefixDepthFintype (branch : Nat → Nat) (cutoff depth : Nat) :
    Fintype (PrefixDepth branch cutoff depth) := by
  induction depth with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ depth ih =>
      letI : Fintype (PrefixDepth branch cutoff depth) := ih
      exact inferInstanceAs (Fintype
        (Fin (branch (cutoff + depth)) × PrefixDepth branch cutoff depth))

end PerfectCompleteness.GeometricCutSplit



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_GeometricPrefixSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.GeometricPrefixSplit

open RecursiveSpaces DescendantSpaces
open GeometricCutSplit (Prefix PrefixDepth )
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

variable {branch : Nat → Nat}

def depthEquiv (low b : Nat) : (a : Nat) →
    PrefixDepth branch low (b + a) ≃
      PrefixDepth branch (low + b) a × PrefixDepth branch low b
  | 0 =>
      { toFun := fun x => ((), x)
        invFun := Prod.snd
        left_inv := fun _ => rfl
        right_inv := by rintro ⟨⟨⟩, x⟩; rfl }
  | a + 1 =>
      ((Equiv.cast (congrArg (fun h => Fin (branch h))
        (Nat.add_assoc low b a).symm)).prodCongr (depthEquiv low b a)).trans
          (Equiv.prodAssoc _ _ _).symm

end PerfectCompleteness.GeometricPrefixSplit

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PoweringOpinionsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTables.graph_ofGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTables.graph_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTables.lookup_ofGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.accepts_ofPortGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.portGraph_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.rotation_ofPortGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables.labelTable_get _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables.walkRows_edge _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables.walkRows_head_value _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables.walkRows_tail_value _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_reverse_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_reverse_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.paddedG_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs.square_next _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs.square_rot_apply _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs.zigzag_rot_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Actual local-label opinions, modal decoding at the reference length, and
its proved persistence at nearby lazy-walk lengths. -/

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.PoweringOpinions

open PoweringWalks PoweringLabels SpectralReturn
open PoweringMoment (bit)

variable {V D A : Type*}

/-- Outside the full-radius neighborhood a fixed fallback makes the opinion
function total. Actual tested path vertices will be certified inside it. -/
def opinionAt (G : PortGraph V D) (t : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u v : V) : A := by
  classical
  exact if h : ∃ n, n ≤ t ∧ ∃ p : Fin n → D, wordEnd G n v p = u then
    decode (selectors v) (labels v) ⟨u, h⟩ else fallback

theorem opinionAt_eq_decode (G : PortGraph V D) (t : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (v : V) (u : Ball G t v) :
    opinionAt G t selectors labels fallback u.val v = decode (selectors v) (labels v) u := by
  classical
  simp [opinionAt, u.property]
  rfl

def honestLabels (G : PortGraph V D) (t : Nat) (assignment : V → A) :
    V → PaddedLabel D t A := fun v => encode G t v (fun u => assignment u.val)

variable [Fintype D] [Nonempty D] [Fintype A] [Nonempty A]

def sampleOpinion (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u : V) (p : Fin N → D) : A :=
  opinionAt G t selectors labels fallback u (wordEnd G N u p)

def decoded (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u : V) : A :=
  PoweringDecoding.mode (sampleOpinion G t N selectors labels fallback u)

def matchFn (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u v : V) : ℝ :=
  bit (opinionAt G t selectors labels fallback u v = decoded G t N selectors labels fallback u)

omit [Nonempty D] in
theorem matchFn_mem_Icc (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u v : V) :
    matchFn G t N selectors labels fallback u v ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  constructor
  · exact PoweringMoment.bit_nonneg _
  · unfold matchFn bit
    split <;> simp

/-- The reference-length modal lower bound is proved from actual port samples. -/
theorem decoded_modal_baseline (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u : V) :
    1 / (Fintype.card A : ℝ) ≤
      iterateOperator G N (matchFn G t N selectors labels fallback u) u := by
  have h := PoweringDecoding.mode_mass_lower (sampleOpinion G t N selectors labels fallback u)
  change 1 / (Fintype.card A : ℝ) ≤ mean (fun p : Fin N → D =>
    matchFn G t N selectors labels fallback u (wordEnd G N u p)) at h
  rwa [PoweringReturn.mean_wordEnd] at h

end UniqueGamesTheorem.Foundations.PCP.PoweringOpinions

end

end

section

/-!
# The actual constraint-graph powering test

Every recorded port walk gives two directed darts. Reversal flips an
orientation bit while preserving the recorded walk. The common vertex
alphabet is the full-radius padded local-label alphabet. The test checks the
actual base constraint at every traversed edge using the two endpoint labels.

Honest local encodings give perfect completeness. A decoded bad edge together
with the two matching local opinions forces rejection of the actual test.
Neither conclusion is assumed as a rejection-inclusion or distribution law.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringTest

open PoweringWalks PoweringLabels PoweringReach PoweringOpinions

variable {V D A : Type*}

/-- The base port predicates packaged as a constraint graph. -/
def baseGraph (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b) :
    ConstraintGraph V (Edge V D) A where
  reverse := G.rot
  reverse_involutive := G.rot_involutive
  tail := Prod.fst
  accepts := accepts
  reverse_accepts := reverse_accepts

theorem pathAccepts_eq_true_iff (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (w : Walk V D (n + 1)) (a b : PaddedLabel D (n + 1) A) :
    pathAccepts G accepts n selectors w a b = true ↔
      ∀ k : Fin (n + 1),
        accepts (edgeAt G n w k)
          (decode (selectors w.1) a (tailFromStart G n w k))
          (decode (selectors (endpoint G w)) b (headFromEnd G n w k)) = true := by
  simp [pathAccepts]

/-- Both directed copies evaluate the same original-start/original-end path
test. Uniformly doubling the darts therefore introduces no change of event. -/
theorem poweredGraph_edgeSatisfied (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A)
    (direction : Bool) (w : Walk V D (n + 1)) :
    (poweredGraph G accepts n selectors).edgeSatisfied labels (direction, w) =
      pathAccepts G accepts n selectors w (labels w.1) (labels (endpoint G w)) := by
  cases direction <;> rfl

/-- The actual directed-dart rejection average is exactly the recorded-walk
rejection average. Only the orientation-bit average is removed, so the vertex
type and the walk type are allowed to be empty. -/
theorem rejection_mean_eq_path_mean [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) :
    SpectralReturn.mean (fun d : Dart V D n => PoweringMoment.bit
      ((poweredGraph G accepts n selectors).edgeSatisfied labels d = false)) =
      SpectralReturn.mean (fun w : Walk V D (n + 1) => PoweringMoment.bit
        (pathAccepts G accepts n selectors w (labels w.1) (labels (endpoint G w)) = false)) := by
  rw [SpectralReturn.mean_prod]
  simp only [poweredGraph_edgeSatisfied, SpectralReturn.mean_const]

theorem pathAccepts_honest (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (assignment : V → A)
    (satisfies : ∀ e, accepts e (assignment e.1) (assignment (G.rot e).1) = true)
    (w : Walk V D (n + 1)) :
    pathAccepts G accepts n selectors w
      (honestLabels G (n + 1) assignment w.1)
      (honestLabels G (n + 1) assignment (endpoint G w)) = true := by
  apply (pathAccepts_eq_true_iff G accepts n selectors w _ _).2
  intro k
  simpa only [honestLabels, decode_encode, tailFromStart_val, headFromEnd_val] using
    satisfies (edgeAt G n w k)

/-- Perfect completeness for the actual powered graph and its common alphabet. -/
theorem perfect_completeness (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (assignment : V → A)
    (satisfies : ∀ e, accepts e (assignment e.1) (assignment (G.rot e).1) = true) :
    ∀ d, (poweredGraph G accepts n selectors).edgeSatisfied
      (honestLabels G (n + 1) assignment) d = true := by
  rintro ⟨direction, w⟩
  rw [poweredGraph_edgeSatisfied]
  exact pathAccepts_honest G accepts n selectors assignment satisfies w

theorem preserves_satisfiability (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (h : (baseGraph G accepts reverse_accepts).Satisfiable) :
    (poweredGraph G accepts n selectors).Satisfiable := by
  obtain ⟨assignment, satisfies⟩ := h
  refine ⟨honestLabels G (n + 1) assignment, ?_⟩
  apply perfect_completeness G accepts n selectors assignment
  intro e
  exact satisfies e

/-- Badness is computed from the actual base predicate and the decoded labels. -/
def decodedBad (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (assignment : V → A) (e : Edge V D) : Bool :=
  !(accepts e (assignment e.1) (assignment (G.rot e).1))

theorem decodedBad_eq_true_iff (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (assignment : V → A) (e : Edge V D) :
    decodedBad G accepts assignment e = true ↔
      accepts e (assignment e.1) (assignment (G.rot e).1) = false := by
  simp [decodedBad]

/-- The base reversal law makes the decoded bad-edge event rotor-invariant. -/
theorem decodedBad_rot (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (assignment : V → A) (e : Edge V D) :
    decodedBad G accepts assignment (G.rot e) = decodedBad G accepts assignment e := by
  have h := congrArg Bool.not
    (reverse_accepts e (assignment e.1) (assignment (G.rot e).1))
  simpa only [decodedBad, G.rot_involutive e] using h

/-- A bad decoded edge with matching opinions at its two true endpoints. -/
noncomputable def witness (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A)
    (assignment : V → A) (w : Walk V D (n + 1)) (k : Fin (n + 1)) : Prop :=
  decodedBad G accepts assignment (edgeAt G n w k) = true ∧
    opinionAt G (n + 1) selectors labels fallback (edgeAt G n w k).1 w.1 =
      assignment (edgeAt G n w k).1 ∧
    opinionAt G (n + 1) selectors labels fallback
      (G.rot (edgeAt G n w k)).1 (endpoint G w) =
        assignment (G.rot (edgeAt G n w k)).1

/-- The witness forces failure of the actual kth checked path constraint.
The opinion/decode identities use the genuine reach certificates. -/
theorem witness_implies_path_rejection (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A)
    (assignment : V → A) (w : Walk V D (n + 1)) (k : Fin (n + 1))
    (h : witness G accepts n selectors labels fallback assignment w k) :
    pathAccepts G accepts n selectors w (labels w.1) (labels (endpoint G w)) = false := by
  obtain ⟨hBad, hTail, hHead⟩ := h
  have hTailDecode :
      decode (selectors w.1) (labels w.1) (tailFromStart G n w k) =
        assignment (edgeAt G n w k).1 :=
    (opinionAt_eq_decode G (n + 1) selectors labels fallback w.1
      (tailFromStart G n w k)).symm.trans hTail
  have hHeadDecode :
      decode (selectors (endpoint G w)) (labels (endpoint G w))
          (headFromEnd G n w k) = assignment (G.rot (edgeAt G n w k)).1 :=
    (opinionAt_eq_decode G (n + 1) selectors labels fallback (endpoint G w)
      (headFromEnd G n w k)).symm.trans hHead
  have hFalse := (decodedBad_eq_true_iff G accepts assignment (edgeAt G n w k)).1 hBad
  cases hPath : pathAccepts G accepts n selectors w
      (labels w.1) (labels (endpoint G w)) with
  | false => rfl
  | true =>
      have hChecked := (pathAccepts_eq_true_iff G accepts n selectors w _ _).1 hPath k
      rw [hTailDecode, hHeadDecode, hFalse] at hChecked
      exact False.elim (Bool.noConfusion hChecked)

end UniqueGamesTheorem.Foundations.PCP.PoweringTest

end

section

/-!
# Actual rejection counts and sizes for the powering construction

Normalized rejection averages are the cardinal ratios of the corresponding
rejected-dart sets. These identities include empty finite types. Positivity
of the dart cardinality is required only when translating inequalities by
division. The powered dart count and common alphabet size are computed from
their actual product and function types.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringCounting

open PoweringWalks PoweringLabels PoweringTest
open scoped BigOperators

variable {V D A E : Type*}

/-- An arbitrary constraint graph's rejection probability is its actual
rejected-dart cardinal ratio, including the empty-dart case. -/
theorem constraint_rejection_mean_eq_count [Fintype E]
    (H : ConstraintGraph V E A) (labels : V → A) :
    SpectralReturn.mean (fun e : E => PoweringMoment.bit
      (H.edgeSatisfied labels e = false)) =
      (H.rejectionCount labels : ℝ) / (Fintype.card E : ℝ) := by
  classical
  rw [SpectralReturn.mean_eq_sum_div_card]
  simp only [PoweringMoment.bit, ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts]
  apply congrArg (fun x : ℝ => x / (Fintype.card E : ℝ))
  convert (Finset.sum_boole (R := ℝ)
    (fun e => H.edgeSatisfied labels e = false) Finset.univ) using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : H.edgeSatisfied labels e = false <;> simp [h]

/-- Multiplying a normalized lower bound by the actual positive dart count. -/
theorem constraint_rejection_lower_iff [Fintype E]
    (H : ConstraintGraph V E A) (labels : V → A)
    (hcard : 0 < Fintype.card E) (ε : ℝ) :
    ε ≤ SpectralReturn.mean (fun e : E => PoweringMoment.bit
      (H.edgeSatisfied labels e = false)) ↔
      ε * (Fintype.card E : ℝ) ≤ (H.rejectionCount labels : ℝ) := by
  rw [constraint_rejection_mean_eq_count]
  exact le_div_iff₀ (Nat.cast_pos.mpr hcard)

/-- The edge-profile definition equals its actual directed-edge indicator
mean without any nonemptiness assumption on vertices or ports. -/
theorem edgeDensity_eq_bit_mean [Fintype V] [Fintype D]
    (bad : Edge V D → Bool) :
    SpectralReturn.edgeDensity bad =
      SpectralReturn.mean (fun e : Edge V D => PoweringMoment.bit (bad e = true)) := by
  convert (SpectralReturn.mean_prod
    (fun e : Edge V D => PoweringMoment.bit (bad e = true))).symm using 1
  all_goals try with_reducible_and_instances rfl
  change SpectralReturn.mean (fun v => SpectralReturn.mean
    (fun d => if bad (v, d) then (1 : ℝ) else 0)) = _
  apply congrArg SpectralReturn.mean
  funext v
  apply congrArg SpectralReturn.mean
  funext d
  cases bad (v, d) <;> simp [PoweringMoment.bit]

/-- Decoded badness is exactly rejection in the actual base constraint graph. -/
theorem base_edgeDensity_eq_rejection_count [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (assignment : V → A) :
    SpectralReturn.edgeDensity (decodedBad G accepts assignment) =
      ((baseGraph G accepts reverse_accepts).rejectionCount assignment : ℝ) /
        (Fintype.card (Edge V D) : ℝ) := by
  calc
    _ = SpectralReturn.mean (fun e : Edge V D => PoweringMoment.bit
        (decodedBad G accepts assignment e = true)) := edgeDensity_eq_bit_mean _
    _ = SpectralReturn.mean (fun e : Edge V D => PoweringMoment.bit
        ((baseGraph G accepts reverse_accepts).edgeSatisfied assignment e = false)) := by
      apply congrArg SpectralReturn.mean
      funext e
      exact congrArg PoweringMoment.bit
        (propext (decodedBad_eq_true_iff G accepts assignment e))
    _ = _ := constraint_rejection_mean_eq_count _ _

theorem base_count_lower_to_density [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (assignment : V → A) (hcard : 0 < Fintype.card (Edge V D)) (ε : ℝ)
    (hcount : ε * (Fintype.card (Edge V D) : ℝ) ≤
      ((baseGraph G accepts reverse_accepts).rejectionCount assignment : ℝ)) :
    ε ≤ SpectralReturn.edgeDensity (decodedBad G accepts assignment) := by
  rw [base_edgeDensity_eq_rejection_count G accepts reverse_accepts assignment]
  exact (le_div_iff₀ (Nat.cast_pos.mpr hcard)).2 hcount

end UniqueGamesTheorem.Foundations.PCP.PoweringCounting

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_PoweringMachineRow
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec.decodeWords_encodeWord _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter.counterTapes_counter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Finite tape program for a powered relation row

The radius, address count, and powered alphabet size are fixed machine
parameters. The machine consumes live base predicate bits and endpoint-match
bits. Its finite register selects the first matching address, looks up the two
fixed powered labels, and conjoins the bounded list of base predicates.

Both input and output bits use the graph-table unary natural-word codec.
The theorems below describe actual TM2 transitions, not assumed execution
costs. Producing this input block from live graph rotor lookups is a separate
frontend composition obligation; no graph table occurs in the machine's
finite transition function.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRow

open Turing
open MachineFixedBlockMap
open UniqueGamesTheorem.Foundations.PCP

theorem encodeBits_graphWords (bits : List Bool) :
    encodeBits bits = encodeWords (bits.map GraphTables.bitWord) := by
  induction bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp [encodeBits, encodeBit, encodeWords,
      GraphTables.bitWord, encodeWord, ih]

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRow

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_CloudRoundingLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetRetraction.edgeSatisfied_pullback _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetRetraction.rejectionCount_pullback _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTables.graph_ofGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTables.graph_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTables.lookup_ofGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.acceptsAt_graphRows _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.reverseAt_graphRows _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_accepts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph_rejectionCount _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GraphTransport.reindex_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables.walkRows_edge _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables.walkRows_head_value _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables.walkRows_tail_value _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringReach.headFromEnd_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringReach.tailFromStart_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringWalks.lazyGraph_rot_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringWalks.lazyGraph_rot_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_reverse_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_reverse_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.paddedG_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs.square_next _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs.square_rot_apply _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs.zigzag_rot_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Actual finite counting for rounding copied dart labels. Minority color classes
are small enough for the cloud's directed-cut expansion. Their boundary darts
inject into all label disagreements. A separate endpoint charge counts at
most two affected original darts per changed copied label.
-/

namespace UniqueGamesTheorem.Foundations.PCP.CloudRounding

open scoped BigOperators

section GraphRounding

open DegreeReplacement PoweringWalks

variable {V E A D : Type*} [Fintype V] [Fintype E] [Fintype A] [Fintype D]
variable [DecidableEq V] [DecidableEq E] [DecidableEq A]

def mismatchSet (G : ConstraintGraph V E A) (ell : E → A) (rounded : V → A) :
    Finset E :=
  Finset.univ.filter (fun e => ell e ≠ rounded (G.tail e))

def copiedRejectionCount (G : ConstraintGraph V E A) (ell : E → A) : Nat :=
  (Finset.univ.filter (fun e => G.accepts e (ell e) (ell (G.reverse e)) = false)).card

def innerDisagreementSet (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) : Finset (E × D) :=
  Finset.univ.filter (fun ed => ell ed.1 ≠ ell (innerRotation G H ed).1)

noncomputable def roundLabels [Nonempty A]
    (G : ConstraintGraph V E A) (ell : E → A) : V → A :=
  fun v => majority (fun e : Cloud G v => ell e.val)

/-- Every changed dart belongs to precisely one tail fiber. -/
def mismatchFiberEquiv (G : ConstraintGraph V E A) (ell : E → A)
    (rounded : V → A) :
    (Σ v, ↥(minoritySet (fun e : Cloud G v => ell e.val) (rounded v))) ≃
      ↥(mismatchSet G ell rounded) where
  toFun := by
    rintro ⟨v, ⟨⟨e, he⟩, hbad⟩⟩
    cases he
    exact ⟨e, by simpa [mismatchSet, minoritySet] using hbad⟩
  invFun e :=
    ⟨G.tail e.val, ⟨⟨e.val, rfl⟩, by
      simpa [mismatchSet, minoritySet] using e.property⟩⟩
  left_inv := by
    rintro ⟨v, ⟨⟨e, he⟩, hbad⟩⟩
    cases he
    rfl
  right_inv := by intro e; apply Subtype.ext; rfl

omit [Fintype A] [DecidableEq E] in
theorem mismatch_card_eq_sum (G : ConstraintGraph V E A) (ell : E → A)
    (rounded : V → A) :
    (mismatchSet G ell rounded).card =
      ∑ v, (minoritySet (fun e : Cloud G v => ell e.val) (rounded v)).card := by
  have h := Fintype.card_congr (mismatchFiberEquiv G ell rounded)
  simpa only [Fintype.card_sigma, Fintype.card_coe] using h.symm

/-- A cloud disagreement is the same actual internal dart in global coordinates. -/
def disagreementFiberEquiv (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) :
    (Σ v, ↥(disagreementSet (fun e : Cloud G v => ell e.val)
      (fun ed => ((H v).rot ed).1))) ≃ ↥(innerDisagreementSet G H ell) where
  toFun := by
    rintro ⟨v, ⟨⟨⟨e, he⟩, d⟩, hbad⟩⟩
    cases he
    refine ⟨(e, d), ?_⟩
    simpa [disagreementSet, innerDisagreementSet, innerRotation,
      cloudIndexEquiv, cloudRotation] using hbad
  invFun := by
    rintro ⟨⟨e, d⟩, hbad⟩
    refine ⟨G.tail e, ⟨(⟨e, rfl⟩, d), ?_⟩⟩
    simpa [disagreementSet, innerDisagreementSet, innerRotation,
      cloudIndexEquiv, cloudRotation] using hbad
  left_inv := by
    rintro ⟨v, ⟨⟨⟨e, he⟩, d⟩, hbad⟩⟩
    cases he
    rfl
  right_inv := by intro ed; apply Subtype.ext; rfl

omit [Fintype A] [DecidableEq E] in
theorem disagreement_card_eq_sum (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) :
    (innerDisagreementSet G H ell).card =
      ∑ v, (disagreementSet (fun e : Cloud G v => ell e.val)
        (fun ed => ((H v).rot ed).1)).card := by
  have h := Fintype.card_congr (disagreementFiberEquiv G H ell)
  simpa only [Fintype.card_sigma, Fintype.card_coe] using h.symm

/-- No uniform cloud-size hypothesis occurs in this finite sum. -/
theorem rounded_mismatch_expansion [Nonempty A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (ell : E → A) (h : ℚ)
    (expansion : ∀ v (S : Finset (Cloud G v)),
      S.card ≤ Fintype.card (Cloud G v) / 2 →
      h * (S.card : ℚ) ≤ ((directedCut (fun ed => ((H v).rot ed).1) S).card : ℚ)) :
    h * ((mismatchSet G ell (roundLabels G ell)).card : ℚ) ≤
      ((innerDisagreementSet G H ell).card : ℚ) := by
  rw [mismatch_card_eq_sum, disagreement_card_eq_sum, Nat.cast_sum, Nat.cast_sum,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  exact minority_expansion_bound (fun e : Cloud G v => ell e.val)
    (fun ed => ((H v).rot ed).1) (roundLabels G ell v) h
    (majority_maximal (fun e : Cloud G v => ell e.val)) (expansion v)

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq E] in
theorem rounded_endpoint_bound (G : ConstraintGraph V E A)
    (ell : E → A) (rounded : V → A) :
    G.rejectionCount rounded ≤ copiedRejectionCount G ell +
      2 * (mismatchSet G ell rounded).card :=
  dart_rejection_count_le G.tail G.reverse G.accepts ell rounded

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq E] in
/-- Exact rejection count for arbitrary copied labels, including cloud violations. -/
theorem replacement_rejection_split (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) :
    (replacementGraph G H).rejectionCount ell =
      copiedRejectionCount G ell + (innerDisagreementSet G H ell).card := by
  classical
  simp only [rejectionCount_eq_sum, Fintype.sum_prod_type, Fintype.sum_sum_type,
    copied_satisfied_inl, copied_satisfied_inr, decide_eq_false_iff_not,
    Fintype.sum_unique, Finset.sum_add_distrib]
  simp only [copiedRejectionCount, innerDisagreementSet, Finset.card_eq_sum_ones,
    Finset.sum_filter, Fintype.sum_prod_type]
  exact Nat.add_comm _ _

/-- Directed expansion by two pays for both changed endpoints exactly. -/
theorem replacement_soundness [Nonempty A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (expansion : ∀ v (S : Finset (Cloud G v)),
      S.card ≤ Fintype.card (Cloud G v) / 2 →
      2 * S.card ≤ (directedCut (fun ed => ((H v).rot ed).1) S).card)
    (ell : E → A) :
    G.rejectionCount (roundLabels G ell) ≤ (replacementGraph G H).rejectionCount ell := by
  have hc := rounded_mismatch_expansion G H ell 2 (by
    intro v S hS
    exact_mod_cast expansion v S hS)
  have hcNat : 2 * (mismatchSet G ell (roundLabels G ell)).card ≤
      (innerDisagreementSet G H ell).card := by exact_mod_cast hc
  rw [replacement_rejection_split]
  exact (rounded_endpoint_bound G ell (roundLabels G ell)).trans
    (Nat.add_le_add_left hcNat _)

/-- Padding changes the normalization, but never the rounded absolute rejection count. -/
theorem padded_replacement_soundness [Nonempty A]
    (G : ConstraintGraph V E A) (dummy : V → Type*) [∀ v, Fintype (dummy v)]
    [∀ v, DecidableEq (dummy v)]
    (H : ∀ v, PortGraph (Cloud (paddedGraph G dummy) v) D)
    (expansion : ∀ v (S : Finset (Cloud (paddedGraph G dummy) v)),
      S.card ≤ Fintype.card (Cloud (paddedGraph G dummy) v) / 2 →
      2 * S.card ≤ (directedCut (fun ed => ((H v).rot ed).1) S).card)
    (ell : PaddedDart G dummy → A) :
    G.rejectionCount (roundLabels (paddedGraph G dummy) ell) ≤
      (paddedReplacementGraph G dummy H).rejectionCount ell := by
  simpa only [paddedReplacementGraph, padded_rejectionCount] using
    replacement_soundness (paddedGraph G dummy) H expansion ell

end GraphRounding

end UniqueGamesTheorem.Foundations.PCP.CloudRounding

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PoweringOpinionTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Bounded first-address tables for actual powering constraints

For a graph with numbered vertices and ports, each stored local-opinion index
is the first address in `allAddresses` that reaches the requested vertex.
The search traverses bounded port words, never the ambient vertex set.

The walk table stores one base dart and two address indices per traversed
edge. Looking up the endpoint labels at those indices gives exactly the
existing `finitePortSelector` decoders, including when addresses collide.
The resulting finite table predicate equals the actual powering predicate.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables

open PoweringWalks PoweringLabels PoweringAddresses PoweringReach
open scoped BigOperators

variable {X A : Type*}

theorem firstIndex_matches (p : X → Prop) [DecidablePred p]
    (xs : List X) (h : ∃ a ∈ xs, p a) : p (xs.get (firstIndex p xs h)) := by
  rw [get_firstIndex]
  exact (scanWitness p xs h).property

/-- Every earlier stored address fails the matching predicate. -/
theorem firstIndex_is_first (p : X → Prop) [DecidablePred p] :
    ∀ (xs : List X) (h : ∃ a ∈ xs, p a) (j : Fin xs.length),
      j.val < (firstIndex p xs h).val → ¬p (xs.get j) := by
  intro xs
  induction xs with
  | nil => intro h; simp at h
  | cons a xs ih =>
    intro h j
    by_cases ha : p a
    · simp [firstIndex, ha]
    · refine Fin.cases (by intro _; exact ha) (fun i => ?_) j
      intro hi
      apply ih (match_in_tail p h ha) i
      exact Nat.lt_of_succ_lt_succ (by
        simpa only [firstIndex, ha, dite_false, Fin.val_succ] using hi)

variable {vertices d : Nat}

/-- Evaluate an already stored row vector by finite label lookups. The only
quantified type is the bounded set of walk positions. -/
def rowsAccepts {n : Nat} (accepts : Edge (Fin vertices) (Fin d) → A → A → Bool)
    (rows : WalkRows vertices d n) (a b : LabelTable d (n + 1) A) : Bool :=
  decide (∀ k : Fin (n + 1), accepts rows[k].edge a[rows[k].tailIndex]
    b[rows[k].headIndex] = true)

/-- The stored finite lookup predicate implements the actual powering test. -/
theorem rowsAccepts_walkRows (G : PortGraph (Fin vertices) (Fin d))
    (accepts : Edge (Fin vertices) (Fin d) → A → A → Bool) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1))
    (a b : PaddedLabel (Fin d) (n + 1) A) :
    rowsAccepts accepts (walkRows G n w) (labelTable a) (labelTable b) =
      PoweringTest.pathAccepts G accepts n (finitePortSelector G (n + 1)) w a b := by
  apply Bool.eq_iff_iff.mpr
  simp only [rowsAccepts, decide_eq_true_iff, PoweringTest.pathAccepts_eq_true_iff,
    walkRows_edge, walkRows_tail_value, walkRows_head_value]

end UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PoweringTableSemanticsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
# Exact semantics of the executable powering tables

The explicit label and dart bijections preserve every actual edge test and
every rejected directed occurrence. The inverse label map covers all encoded
assignments, so satisfiability and uniform rejection-count bounds transport
without any consistency restriction on padded labels.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringTableSemantics

open PoweringWalks PoweringLabels PoweringAddresses PoweringEnumeration PoweringTables

abbrev RawLabeling (vertices d n : Nat) :=
  Fin vertices → PaddedLabel (Fin d) (n + 1) (Fin 64)

end UniqueGamesTheorem.Foundations.PCP.PoweringTableSemantics

/-!
# The actual first moment of an endpoint-opinion witness

The pivot factorization is applied to actual finite walks. Its two endpoint
operator bounds are obtained from the proved lazy-graph mixture and smoothing
theorem. No witness-event probability law is assumed.
-/

/-! The actual graph-powering soundness bound. Modal endpoint opinions give
the first moment, spectral return gives the second moment, and an actual
checked path constraint turns each witness into rejection. -/

/-! Actual directed-cut expansion from the graph's zero-mean spectral
certificate. Parallel edges and loops retain their indexed port multiplicities. -/
namespace UniqueGamesTheorem.Foundations.PCP.SpectralCut

open scoped BigOperators
open PoweringWalks SpectralReturn

section Indicators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mean_indicator (S : Finset V) :
    mean (indicator S) = (S.card : ℝ) / (Fintype.card V : ℝ) := by
  have hf : Finset.univ.filter (fun v : V => v ∈ S) = S := by
    ext v
    simp
  rw [mean_eq_sum_div_card]
  simp only [indicator, Finset.sum_boole, hf]

theorem energy_indicator (S : Finset V) : energy (indicator S) = mean (indicator S) := by
  unfold energy
  congr 1
  funext v
  unfold indicator
  split_ifs <;> norm_num

end Indicators

end UniqueGamesTheorem.Foundations.PCP.SpectralCut

/-!
# Uniform restriction of Boolean tapes

Restricting a uniformly sampled Boolean function to a decidable subset gives
the uniform law on functions on that subset.  The subset and its complement
may be empty: their Boolean function spaces still contain the constant-false
function.  Extending by false gives a canonical full-domain oracle address.
-/

namespace UniqueGamesTheorem.Foundations.PCP.UniformRestriction

open scoped BigOperators

variable {B : Type*} (p : B → Prop)

variable [DecidablePred p]

variable [Fintype B] [DecidableEq B]

/-- Uniform full tapes induce exactly uniform legal-coordinate tapes. -/
theorem expect_restrict (h : ({b // p b} → Bool) → ℝ) :
    (𝔼 f : B → Bool, h (restrict p f)) = 𝔼 g : {b // p b} → Bool, h g := by
  calc
    (𝔼 f : B → Bool, h (restrict p f)) =
        𝔼 g : ({b // p b} → Bool) × ({b // ¬ p b} → Bool), h g.1 :=
      Fintype.expect_equiv (Equiv.piEquivPiSubtypeProd p (fun _ => Bool))
        _ _ (fun _ => rfl)
    _ = 𝔼 g : {b // p b} → Bool, 𝔼 _k : {b // ¬ p b} → Bool, h g := by
      simpa only [Finset.univ_product_univ] using
        Finset.expect_product
          (Finset.univ : Finset ({b // p b} → Bool))
          (Finset.univ : Finset ({b // ¬ p b} → Bool))
          (fun g : ({b // p b} → Bool) × ({b // ¬ p b} → Bool) => h g.1)
    _ = 𝔼 g : {b // p b} → Bool, h g := by
      simp only [Fintype.expect_const]

end UniqueGamesTheorem.Foundations.PCP.UniformRestriction

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_AlphabetGraphLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Relations.repeatedConsistentDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetGraph

open UniqueGamesTheorem.Foundations.Hastad
open scoped BigOperators

variable {V E A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def edgeOracle (G : ConstraintGraph V E A) (assignment : Address V E A → Bool) (e : E) :
    Cube (AlphabetReduction.LegalPair (G.accepts e)) → Bool :=
  fun tape => assignment (.inr (e, extendTape G e tape))

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem oracleAnswer_globalize (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) (e : E)
    (x : AlphabetReduction.InputCoordinate A ⊕ Cube (AlphabetReduction.LegalPair (G.accepts e))) :
    assignment (globalizeQuery G e x) =
      AssignmentTester.oracleAnswer
        (CodeComposition.pairWord (vertexBlock assignment (G.tail e))
          (vertexBlock assignment (G.head e))) (edgeOracle G assignment e) x := by
  rcases x with ⟨side, tape⟩ | tape
  · cases side <;> rfl
  · rfl

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem response_eq_local (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) (e : E) (kind : Fin 4)
    (k : AlphabetReduction.InputCoordinate A) (f g r₀ r₁ r₂ : Cube (A × A)) :
    QueryIncidence.response (verifier G) assignment (e, kind, k, f, g, r₀, r₁, r₂) =
      fun slot => AssignmentTester.oracleAnswer
        (CodeComposition.pairWord (vertexBlock assignment (G.tail e))
          (vertexBlock assignment (G.head e))) (edgeOracle G assignment e)
        (AssignmentTester.eventQueries (AlphabetReduction.pairEncoding (G.accepts e)) kind k
          (restrictTape G e f) (restrictTape G e g) (restrictTape G e r₀)
          (restrictTape G e r₁) (restrictTape G e r₂) slot) := by
  funext slot
  exact oracleAnswer_globalize G assignment e _

def eventReject (G : ConstraintGraph V E A) (assignment : Address V E A → Bool)
    (event : Event E A) : ℝ :=
  AssignmentTester.truth (!((verifier G).accepts event (QueryIncidence.response (verifier G) assignment event)))

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem eventReject_eq_local (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) (e : E) (kind : Fin 4)
    (k : AlphabetReduction.InputCoordinate A) (f g r₀ r₁ r₂ : Cube (A × A)) :
    eventReject G assignment (e, kind, k, f, g, r₀, r₁, r₂) =
      AssignmentTester.eventReject (AlphabetReduction.pairEncoding (G.accepts e))
        (CodeComposition.pairWord (vertexBlock assignment (G.tail e))
          (vertexBlock assignment (G.head e))) (edgeOracle G assignment e) kind k
        (restrictTape G e f) (restrictTape G e g) (restrictTape G e r₀)
        (restrictTape G e r₁) (restrictTape G e r₂) := by
  unfold eventReject
  rw [response_eq_local]
  rfl

def localAverage (G : ConstraintGraph V E A) (assignment : Address V E A → Bool)
    (e : E) : ℝ := 𝔼 sample : LocalEvent A, eventReject G assignment (e, sample)

/-- Iterating the checked one-tape restriction identity preserves independence. -/
theorem expect_restrict_five {B : Type*} [Fintype B] [DecidableEq B]
    (p : B → Prop) [DecidablePred p]
    (h : ({b // p b} → Bool) → ({b // p b} → Bool) → ({b // p b} → Bool) →
      ({b // p b} → Bool) → ({b // p b} → Bool) → ℝ) :
    (𝔼 f : B → Bool, 𝔼 g : B → Bool, 𝔼 r₀ : B → Bool,
      𝔼 r₁ : B → Bool, 𝔼 r₂ : B → Bool,
        h (UniformRestriction.restrict p f) (UniformRestriction.restrict p g)
          (UniformRestriction.restrict p r₀) (UniformRestriction.restrict p r₁)
          (UniformRestriction.restrict p r₂)) =
    𝔼 f : {b // p b} → Bool, 𝔼 g : {b // p b} → Bool,
      𝔼 r₀ : {b // p b} → Bool, 𝔼 r₁ : {b // p b} → Bool,
        𝔼 r₂ : {b // p b} → Bool, h f g r₀ r₁ r₂ := by
  rw [UniformRestriction.expect_restrict p
    (fun f => 𝔼 g : B → Bool, 𝔼 r₀ : B → Bool, 𝔼 r₁ : B → Bool,
      𝔼 r₂ : B → Bool, h f (UniformRestriction.restrict p g)
        (UniformRestriction.restrict p r₀) (UniformRestriction.restrict p r₁)
        (UniformRestriction.restrict p r₂))]
  apply Finset.expect_congr rfl
  intro f _
  rw [UniformRestriction.expect_restrict p
    (fun g => 𝔼 r₀ : B → Bool, 𝔼 r₁ : B → Bool, 𝔼 r₂ : B → Bool,
      h f g (UniformRestriction.restrict p r₀) (UniformRestriction.restrict p r₁)
        (UniformRestriction.restrict p r₂))]
  apply Finset.expect_congr rfl
  intro g _
  rw [UniformRestriction.expect_restrict p
    (fun r₀ => 𝔼 r₁ : B → Bool, 𝔼 r₂ : B → Bool,
      h f g r₀ (UniformRestriction.restrict p r₁) (UniformRestriction.restrict p r₂))]
  apply Finset.expect_congr rfl
  intro r₀ _
  rw [UniformRestriction.expect_restrict p
    (fun r₁ => 𝔼 r₂ : B → Bool, h f g r₀ r₁ (UniformRestriction.restrict p r₂))]
  apply Finset.expect_congr rfl
  intro r₁ _
  exact UniformRestriction.expect_restrict p (h f g r₀ r₁)

omit [Nonempty A] in
/-- Five independent full tapes restrict to five independent uniform legal tapes. -/
theorem localAverage_eq_tester (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) (e : E) :
    localAverage G assignment e = AlphabetReduction.edgeTesterReject (G.accepts e)
      (vertexBlock assignment (G.tail e)) (vertexBlock assignment (G.head e))
      (edgeOracle G assignment e) := by
  unfold localAverage AlphabetReduction.edgeTesterReject AssignmentTester.explicitTesterReject
  simp only [LocalEvent, expect_prod, eventReject_eq_local, restrictTape]
  apply Finset.expect_congr rfl
  intro kind _
  apply Finset.expect_congr rfl
  intro side _
  apply Finset.expect_congr rfl
  intro tape _
  exact expect_restrict_five (legal G e)
    (AssignmentTester.eventReject (AlphabetReduction.pairEncoding (G.accepts e))
      (CodeComposition.pairWord (vertexBlock assignment (G.tail e))
        (vertexBlock assignment (G.head e))) (edgeOracle G assignment e) kind (side, tape))

def average [Fintype E] (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) : ℝ :=
  𝔼 event : Event E A, eventReject G assignment event

def decodedLabeling (assignment : Address V E A → Bool) : V → A :=
  fun v => CodeComposition.nearest (vertexBlock assignment v)

omit [Nonempty A] in
theorem average_eq_count [Fintype E] (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) :
    average G assignment = (QueryIncidence.verifierRejectionCount (verifier G) assignment : ℝ) /
      Fintype.card (Event E A) :=
  expect_rejection_eq_count _

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem honest_edgeOracle (G : ConstraintGraph V E A) (labeling : V → A) (e : E)
    (h : G.edgeSatisfied labeling e = true) :
    edgeOracle G (honestAssignment G labeling) e =
      fun tape => tape ⟨(labeling (G.tail e), labeling (G.head e)), h⟩ := by
  funext tape
  exact UniformRestriction.extend_apply_of_mem (legal G e) tape
    (labeling (G.tail e), labeling (G.head e)) h

end UniqueGamesTheorem.Foundations.PCP.AlphabetGraph

end

/-!
# Real gap and exact size of the alphabet graph

The gap bound is obtained directly from the two checked rejection-count
inequalities. The finite graph's size is linear in the old vertices and darts,
with an explicit coefficient determined only by the old alphabet cardinality.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetGraphBounds

open scoped BigOperators

abbrev OutputVertex (V E A : Type*) :=
  QueryIncidence.Vertex (AlphabetGraph.Event E A) (AlphabetGraph.Address V E A)

abbrev OutputDart (E A : Type*) := QueryIncidence.Dart (AlphabetGraph.Event E A) 6

def vertexFactor (q : Nat) : Nat := localEventFactor q + 2 ^ (q * q)

def sizeFactor (q : Nat) : Nat := 2 ^ q + vertexFactor q + dartFactor q

theorem sizeFactor_positive (q : Nat) : 0 < sizeFactor q := by
  have hp : (0 : Nat) < 2 ^ q := pow_pos (by decide) q
  unfold sizeFactor
  omega

end UniqueGamesTheorem.Foundations.PCP.AlphabetGraphBounds

/-!
# Explicit orders for the alphabet-reduction table

All executable maps use Boolean digits, finite sums, and division/remainder.
No enumeration is chosen from a cardinality proof. Cube coordinate zero is the
least significant bit; pairs of coordinates use row-major order. Event blocks
are ordered by their original dart, followed by the local event. Vertices put
events before vertex addresses before edge addresses. Each event has twelve
ordered darts: six slots, with false then true orientation at each slot.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration

open UniqueGamesTheorem.Foundations.Hastad
open scoped BigOperators

theorem dartEquiv_reverse_val (m q : Nat)
    (event : AlphabetGraph.Event (Fin m) (Fin q)) (slot : Fin 6) (orientation : Bool) :
    (dartEquiv m q (QueryIncidence.reverse ((event, slot), orientation))).val =
      (eventEquiv m q event).val * 12 + slot.val * 2 + bitValue (!orientation) :=
  dartEquiv_val m q event slot (!orientation)

theorem ordered_trans_finCongr {A : Type*} {a b : Nat}
    (order : A ≃ Fin a) (sameCount : a = b) :
    ordered (order.trans (finCongr sameCount)) = ordered order := by
  cases sameCount
  rfl

/-- Product enumeration visits the right factor completely at each left index. -/
theorem ordered_product {A B : Type*} {a b : Nat}
    (left : A ≃ Fin a) (right : B ≃ Fin b) :
    ordered (productEquiv left right) =
      (ordered left).flatMap (fun x => (ordered right).map (fun y => (x, y))) := by
  have atIndex (i : Fin a) (j : Fin b) (h : i.val * b + j.val < a * b) :
      (productEquiv left right).symm ⟨i.val * b + j.val, h⟩ =
        (left.symm i, right.symm j) := by
    have same : (⟨i.val * b + j.val, h⟩ : Fin (a * b)) = finProdFinEquiv (i, j) := by
      apply Fin.ext
      simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
    rw [same]
    simp [productEquiv]
  unfold ordered
  rw [List.ofFn_mul]
  simp only [atIndex, List.flatMap_def, List.map_ofFn, Function.comp_def]

theorem ordered_event (m q : Nat) :
    ordered (eventEquiv m q) =
      (List.finRange m).flatMap (fun edge => (localEvents q).map (fun event => (edge, event))) := by
  change ordered (productEquiv (Equiv.refl (Fin m)) (localEventEquiv q)) = _
  rw [ordered_product, ordered_refl]
  rfl

/-- Exact serialized occurrence order, including both orientations and every
repeated local query: edge, local event, slot, then false and true. -/
theorem ordered_dart (m q : Nat) :
    ordered (dartEquiv m q) =
      (List.finRange m).flatMap (fun edge =>
        (localEvents q).flatMap (fun event =>
          (List.finRange 6).flatMap (fun slot =>
            [(((edge, event), slot), false), (((edge, event), slot), true)]))) := by
  rw [dartEquiv]
  erw [ordered_trans_finCongr]
  rw [ordered_product, ordered_product, ordered_event]
  simp only [ordered_refl, ordered_bool, List.flatMap_assoc, List.flatMap_map,
    List.map_cons, List.map_nil]

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_AlphabetTableBoundsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.VerifierToCNF

open Target

theorem chainView_sound (bits ys : List Bool)
    (size : bits.length = ys.length + 3)
    (accepted : (chainView bits ys).all tripleValue = true) : bits.any id = true := by
  induction ys generalizing bits with
  | nil =>
    match bits with
    | [a, b, c] => simpa [chainView, tripleValue, Bool.or_assoc] using accepted
    | [] => simp at size
    | [_] => simp at size
    | [_, _] => simp at size
    | _ :: _ :: _ :: _ :: rest =>
      simp only [List.length_cons, List.length_nil] at size
      omega
  | cons y ys ih =>
    match bits with
    | [] => simp at size
    | [_] => simp only [List.length_cons, List.length_nil] at size; omega
    | a :: b :: rest =>
      have smaller : ((!y) :: rest).length = ys.length + 3 := by
        simp only [List.length_cons] at *
        omega
      have accepted' : tripleValue (a, b, y) = true ∧
          (chainView ((!y) :: rest) ys).all tripleValue = true := by
        simpa only [chainView, List.all_cons, Bool.and_eq_true] using accepted
      have tailAccepted := ih ((!y) :: rest) smaller accepted'.2
      cases a <;> cases b <;> cases y <;> simp_all [tripleValue]

theorem fillBits_correct (bits : List Bool) (size : 3 ≤ bits.length) :
    (chainView bits (fillBits bits)).all tripleValue = true ↔ bits.any id = true := by
  match bits with
  | [] => simp at size
  | [_] => simp at size
  | [_, _] => simp at size
  | [a, b, c] => simp [fillBits, chainView, tripleValue, Bool.or_assoc]
  | a :: b :: c :: d :: rest =>
    have ih := fillBits_correct ((a || b) :: c :: d :: rest) (by simp)
    have tautology : tripleValue (a, b, !(a || b)) = true := by
      cases a <;> cases b <;> rfl
    rw [fillBits]
    simp only [chainView, List.all_cons, Bool.not_not]
    rw [tautology]
    simp only [Bool.true_and]
    simpa [Bool.or_assoc] using ih
termination_by bits.length
decreasing_by simp_wf

theorem chainView_failed (bits ys : List Bool)
    (size : bits.length = ys.length + 3) (failed : bits.any id = false) :
    1 ≤ ((chainView bits ys).map tripleValue).count false := by
  by_contra none
  have zero : ((chainView bits ys).map tripleValue).count false = 0 := by omega
  have all := (zero_false_count_iff_all _).mp zero
  have accepted : (chainView bits ys).all tripleValue = true := by
    simpa only [List.all_map, Function.comp_def, id_eq] using all
  have impossible := chainView_sound bits ys size accepted
  rw [failed] at impossible
  contradiction

theorem mem_patterns (q : Nat) (p : Pattern q) : p ∈ patterns q := by
  induction q with
  | zero =>
    have h : p = Fin.elim0 := by funext i; exact Fin.elim0 i
    simp [patterns, h]
  | succ q ih =>
    let tail : Pattern q := fun i => p i.succ
    have htail : tail ∈ patterns q := ih tail
    have prefixEquality : Fin.cases (p 0) tail = p := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    apply List.mem_flatMap.mpr
    refine ⟨tail, htail, ?_⟩
    cases h : p 0 with
    | false =>
      have hp : Fin.cases false tail = p := by simpa only [h] using prefixEquality
      exact List.mem_cons.mpr (Or.inl hp.symm)
    | true =>
      have hp : Fin.cases true tail = p := by simpa only [h] using prefixEquality
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl hp.symm)))

theorem patternAt_surjective (q : Nat) (bits : Pattern q) :
    ∃ p : PatternIndex q, patternAt q p = bits := by
  obtain ⟨i, hi, h⟩ := List.getElem_of_mem (mem_patterns q bits)
  exact ⟨⟨i, hi⟩, h⟩

def eventValue {q : Nat} (V : FiniteVerifier q) (A : Fin V.variables → Bool)
    (e : Fin V.events) : Bool := V.accepts e (fun i => A (V.query e i))

def rejectedEventCount {q : Nat} (V : FiniteVerifier q) (A : Fin V.variables → Bool) : Nat :=
  ((List.finRange V.events).map (eventValue V A)).count false

theorem freshIndex_value {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) (j : Fin (q - 3)) :
    (freshIndex V e p j).val =
      V.variables + ((e.val * (patterns q).length + p.val) * (q - 3) + j.val) := by
  simp [freshIndex, Fin.natAdd, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

end UniqueGamesTheorem.Foundations.PCP.VerifierToCNF

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_NormalizationLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.NormalizationWords


open UniqueGamesTheorem.Foundations
open Complexity

def literalBits (signs : Signs) (names : Names) (freshBase : Nat)
    (literal : LiteralRecipe) : List Bool :=
  encodeWords (literalWords signs names freshBase literal)

theorem encodeWords_flatMap {α : Type} (xs : List α) (f : α → List Nat) :
    encodeWords (xs.flatMap f) = xs.flatMap (fun x => encodeWords (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

end PerfectCompleteness.NormalizationWords



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OutputAnnihilator
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.TensorProjectedSlice.totalMatrix_apply _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveEquiv_val _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveMap_val _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.forget_val _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.base_apply _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.compress_apply _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.compress_lift _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.complementParameter_val _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.coordinateEquiv_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.FullCompression.compression_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Fourier.MatrixNoise.dotCharacter_apply _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_firstBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_hBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_secondBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.alphabetEmbedding_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.OutputAnnihilator

noncomputable section

open scoped Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

variable {K : Type*} [AddCommGroup K] [Module F2 K]
  [FiniteDimensional F2 K] [Fintype (Module.Dual F2 K)]

def bad (W : Submodule F2 K) : Finset (Module.Dual F2 K) :=
  Finset.univ.filter (fun σ => σ ∈ W.dualAnnihilator)

omit [FiniteDimensional F2 K] in
@[simp] theorem mem_bad (W : Submodule F2 K) (σ : Module.Dual F2 K) :
    σ ∈ bad W ↔ σ ∈ W.dualAnnihilator := by
  simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]

end
end PerfectCompleteness.OutputAnnihilator

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SignedCostEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SignedCostEnvelope

def endpointBound (w T count : Nat) : Nat :=
  8 * w * (T + 1) + 4 * w + 2 +
    2 * (CanonicalVertexNames.payloadBound w T + 1) +
    3 * (CanonicalDictionaryNames.streamBound w T count) ^ 2 +
    16 * CanonicalDictionaryNames.streamBound w T count + 12

def bodyBound (w d T : Nat) : Nat :=
  72 * w * (T + 1) + d * (2 * endpointBound w T (d * (T + 1) ^ w) + 4) +
    7 * w * (T + 2) + 2

theorem payloadBound_le (w T : Nat) :
    CanonicalVertexNames.payloadBound w T ≤ payloadCoeff w * (T + 1) := by
  have hone : 1 ≤ T + 1 := Nat.succ_le_succ (Nat.zero_le T)
  have hmax : max w (max T 2) + 1 ≤ w + (T + 1) + 2 := by omega
  have hfactor : max w (max T 2) + 1 ≤ (w + 3) * (T + 1) := by
    calc
      max w (max T 2) + 1 ≤ w + (T + 1) + 2 := hmax
      _ ≤ w * (T + 1) + (T + 1) + 2 * (T + 1) :=
        Nat.add_le_add (Nat.add_le_add_right (le_scaled w hone) (T + 1))
          (le_scaled 2 hone)
      _ = (w + 3) * (T + 1) := by ring
  calc
    CanonicalVertexNames.payloadBound w T =
        (1 + 2 ^ (11 ^ w) + 6 * w) * (max w (max T 2) + 1) + 1 := rfl
    _ ≤ (1 + 2 ^ (11 ^ w) + 6 * w) * ((w + 3) * (T + 1)) + (T + 1) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hfactor) hone
    _ = payloadCoeff w * (T + 1) := by unfold payloadCoeff; ring

theorem streamBound_le (w d T : Nat) :
    CanonicalDictionaryNames.streamBound w T (d * (T + 1) ^ w) ≤
      streamCoeff w d * (T + 1) ^ (w + 1) := by
  have hone : 1 ≤ T + 1 := Nat.succ_le_succ (Nat.zero_le T)
  have hfactor : 2 * CanonicalVertexNames.payloadBound w T + 2 ≤
      (2 * payloadCoeff w + 2) * (T + 1) := by
    calc
      2 * CanonicalVertexNames.payloadBound w T + 2 ≤
          2 * (payloadCoeff w * (T + 1)) + 2 * (T + 1) :=
        Nat.add_le_add (Nat.mul_le_mul_left 2 (payloadBound_le w T)) (le_scaled 2 hone)
      _ = (2 * payloadCoeff w + 2) * (T + 1) := by ring
  calc
    CanonicalDictionaryNames.streamBound w T (d * (T + 1) ^ w) =
        (2 * CanonicalVertexNames.payloadBound w T + 2) * (d * (T + 1) ^ w) := rfl
    _ ≤ ((2 * payloadCoeff w + 2) * (T + 1)) * (d * (T + 1) ^ w) :=
      Nat.mul_le_mul_right _ hfactor
    _ = streamCoeff w d * (T + 1) ^ (w + 1) := by
      rw [Nat.pow_succ]
      unfold streamCoeff
      ring

theorem endpointBound_le (w d T : Nat) :
    endpointBound w T (d * (T + 1) ^ w) ≤
      endpointCoeff w d * (T + 1) ^ degree w := by
  have hone := one_le_envelope w T
  have hinput := input_le_envelope w T
  have hpayload : CanonicalVertexNames.payloadBound w T ≤
      payloadCoeff w * (T + 1) ^ degree w :=
    (payloadBound_le w T).trans (Nat.mul_le_mul_left _ hinput)
  have hstream := streamBound_le w d T
  have hstreamLinear : CanonicalDictionaryNames.streamBound w T (d * (T + 1) ^ w) ≤
      streamCoeff w d * (T + 1) ^ degree w :=
    hstream.trans (Nat.mul_le_mul_left _ (streamPower_le_envelope w T))
  have hsquare : (CanonicalDictionaryNames.streamBound w T (d * (T + 1) ^ w)) ^ 2 ≤
      (streamCoeff w d) ^ 2 * (T + 1) ^ degree w := by
    calc
      (CanonicalDictionaryNames.streamBound w T (d * (T + 1) ^ w)) ^ 2 ≤
          (streamCoeff w d * (T + 1) ^ (w + 1)) ^ 2 :=
        Nat.pow_le_pow_left hstream 2
      _ = (streamCoeff w d) ^ 2 * (T + 1) ^ degree w := by
        rw [Nat.mul_pow, ← Nat.pow_mul]
        have hexp : (w + 1) * 2 = degree w := by unfold degree; omega
        rw [hexp]
  have hstart : 8 * w * (T + 1) + 4 * w + 2 ≤
      (12 * w + 2) * (T + 1) ^ degree w := by
    calc
      8 * w * (T + 1) + 4 * w + 2 ≤
          (8 * w) * (T + 1) ^ degree w + (4 * w) * (T + 1) ^ degree w +
            2 * (T + 1) ^ degree w :=
        Nat.add_le_add
          (Nat.add_le_add (Nat.mul_le_mul_left (8 * w) hinput) (le_scaled (4 * w) hone))
          (le_scaled 2 hone)
      _ = (12 * w + 2) * (T + 1) ^ degree w := by ring
  have hpayloadTerm : 2 * (CanonicalVertexNames.payloadBound w T + 1) ≤
      (2 * payloadCoeff w + 2) * (T + 1) ^ degree w := by
    calc
      2 * (CanonicalVertexNames.payloadBound w T + 1) ≤
          2 * (payloadCoeff w * (T + 1) ^ degree w + (T + 1) ^ degree w) :=
        Nat.mul_le_mul_left 2 (Nat.add_le_add hpayload hone)
      _ = (2 * payloadCoeff w + 2) * (T + 1) ^ degree w := by ring
  calc
    endpointBound w T (d * (T + 1) ^ w) ≤
        (12 * w + 2) * (T + 1) ^ degree w +
          (2 * payloadCoeff w + 2) * (T + 1) ^ degree w +
          3 * ((streamCoeff w d) ^ 2 * (T + 1) ^ degree w) +
          16 * (streamCoeff w d * (T + 1) ^ degree w) + 12 * (T + 1) ^ degree w :=
      Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add (Nat.add_le_add hstart hpayloadTerm) (Nat.mul_le_mul_left 3 hsquare))
          (Nat.mul_le_mul_left 16 hstreamLinear))
        (le_scaled 12 hone)
    _ = endpointCoeff w d * (T + 1) ^ degree w := by unfold endpointCoeff; ring

theorem bodyBound_le (w d T : Nat) :
    bodyBound w d T ≤ bodyCoeff w d * (T + 1) ^ degree w := by
  have hone := one_le_envelope w T
  have hinput := input_le_envelope w T
  have hendpoint := endpointBound_le w d T
  have hbody : d * (2 * endpointBound w T (d * (T + 1) ^ w) + 4) ≤
      (d * (2 * endpointCoeff w d + 4)) * (T + 1) ^ degree w := by
    calc
      d * (2 * endpointBound w T (d * (T + 1) ^ w) + 4) ≤
          d * (2 * (endpointCoeff w d * (T + 1) ^ degree w) + 4 * (T + 1) ^ degree w) :=
        Nat.mul_le_mul_left d
          (Nat.add_le_add (Nat.mul_le_mul_left 2 hendpoint) (le_scaled 4 hone))
      _ = (d * (2 * endpointCoeff w d + 4)) * (T + 1) ^ degree w := by ring
  have hcleanup : 7 * w * (T + 2) ≤ (14 * w) * (T + 1) ^ degree w := by
    calc
      7 * w * (T + 2) = (7 * w) * ((T + 1) + 1) := rfl
      _ ≤ (7 * w) * ((T + 1) ^ degree w + (T + 1) ^ degree w) :=
        Nat.mul_le_mul_left (7 * w) (Nat.add_le_add hinput hone)
      _ = (14 * w) * (T + 1) ^ degree w := by ring
  calc
    bodyBound w d T ≤ (72 * w) * (T + 1) ^ degree w +
        (d * (2 * endpointCoeff w d + 4)) * (T + 1) ^ degree w +
        (14 * w) * (T + 1) ^ degree w + 2 * (T + 1) ^ degree w :=
      Nat.add_le_add
        (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left (72 * w) hinput) hbody) hcleanup)
        (le_scaled 2 hone)
    _ = bodyCoeff w d * (T + 1) ^ degree w := by unfold bodyCoeff; ring

end PerfectCompleteness.SignedCostEnvelope

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_SourceAmplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceAmplification

open SourceClause UniqueGamesTheorem.Foundations Games
open UniqueGamesTheorem.Integration

theorem exists_repetition_length {γ σ : ℚ}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hσ : 0 < σ) :
    ∃ k : Nat, 0 < k ∧ SourceParameters.rate (γ / 3) ^ k < σ := by
  have hthird : (0 : ℚ) < γ / 3 := div_pos hγ (by norm_num)
  have hthird1 : γ / 3 ≤ (1 : ℚ) := by linarith
  have hr := SourceParameters.rate_bounds hthird hthird1
  exact UniqueGamesTheorem.Soundness.RepetitionUpper.exists_power_lt
    (SourceParameters.rate (γ / 3)) σ hr.1.le hr.2 hσ

def repetitionLength (γ σ : ℚ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hσ : 0 < σ) : Nat :=
  Nat.find (exists_repetition_length hγ hγ1 hσ)

end PerfectCompleteness.SourceAmplification

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceOddListsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceOddLists

open SourceClause OddLists
open UniqueGamesTheorem.Foundations.Games

noncomputable section

def repetitionLength (γ : ℚ) (s : Nat) [NeZero s]
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) : Nat :=
  SourceAmplification.repetitionLength γ (tolerance s) hγ hγ1 (tolerance_positive s)

end
end PerfectCompleteness.SourceOddLists



end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineTupleOdometer
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCompare.compareInTime_steps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineTupleOdometer

open Turing
open Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K]

theorem update_current (current remaining : K) (distinct : current ≠ remaining)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt current remaining base input output) current replacement =
      tapesAt current remaining base replacement output := by
  funext k
  by_cases hc : k = current
  · subst k; simp [tapesAt, distinct]
  · by_cases hr : k = remaining
    · subst k; simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hc, hr]

theorem update_remaining (current remaining : K)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt current remaining base input output) remaining replacement =
      tapesAt current remaining base input replacement := by
  simp [tapesAt]

end UniqueGamesTheorem.Foundations.Complexity.MachineTupleOdometer

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_TupleInitializationMachine
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec.decodeWords_encodeWord _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter.counterTapes_counter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.TupleInitializationMachine


open Turing UniqueGamesTheorem.Foundations.Complexity
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

omit [DecidableEq K] in
@[simp] theorem finish_pushBound (exit : Option Λ) :
    Runtime.statementPushBound (finish (K := K) (σ := σ) exit) = 0 := by
  cases exit <;> rfl

def instruction (src : K) (currents remaining : List K)
    (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .seed => pushEach (currents ++ remaining) false
      (.pop src (fun state _ => clean state.1) (.goto (fun _ => labels .scan)))
  | .scan => .pop src (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (pushEach remaining true (finish (some (labels .scan)))) (finish exit))

theorem scanStep_false (src : K) (currents remaining : List K)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program (labels .scan) = instruction src currents remaining labels exit .scan)
    (base : K → List Bool) (suffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some (labels .scan), (ambient, register), Function.update base src (false :: suffix)⟩ =
    some ⟨exit, clean ambient, Function.update base src suffix⟩ := by
  change some (TM2.stepAux (program (labels .scan)) _ _) = _
  rw [atScan]
  cases exit <;> simp [instruction, TM2.stepAux, finish, clean]

theorem scanStep_true (src : K) (currents remaining : List K)
    (hn : remaining.Nodup) (hsrc : src ∉ remaining)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program (labels .scan) = instruction src currents remaining labels exit .scan)
    (base : K → List Bool) (rest : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some (labels .scan), (ambient, register), Function.update base src (true :: rest)⟩ =
    some ⟨some (labels .scan), clean ambient,
      Function.update (prefixOn remaining [true] base) src rest⟩ := by
  change some (TM2.stepAux (program (labels .scan)) _ _) = _
  rw [atScan]
  simp only [instruction, TM2.stepAux.eq_3, TM2.stepAux.eq_5, Function.update_self,
    List.head?_cons, List.tail_cons, Option.getD_some, Bool.cond_true, Function.update_idem]
  rw [stepAux_pushEach remaining hn, stepAux_finish,
    prefixOn_update remaining src hsrc]

theorem scanTrace (src : K) (currents remaining : List K)
    (hn : remaining.Nodup) (hsrc : src ∉ remaining)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program (labels .scan) = instruction src currents remaining labels exit .scan)
    (base : K → List Bool) (count : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[count + 1]
      (some ⟨some (labels .scan), (ambient, register),
        Function.update base src (encodeWord count ++ suffix)⟩) =
    some ⟨exit, clean ambient,
      Function.update (prefixOn remaining (List.replicate count true) base) src suffix⟩ := by
  induction count generalizing base register with
  | zero =>
    simpa [encodeWord] using
      scanStep_false src currents remaining labels exit program atScan base suffix ambient register
  | succ count ih =>
    rw [Function.iterate_succ_apply]
    change (advance (TM2.step program))^[count + 1]
      (TM2.step program ⟨some (labels .scan), (ambient, register),
        Function.update base src (encodeWord (count + 1) ++ suffix)⟩) = _
    rw [show encodeWord (count + 1) ++ suffix =
      true :: (encodeWord count ++ suffix) by
        simp [encodeWord, List.replicate_succ, List.append_assoc]]
    rw [scanStep_true src currents remaining hn hsrc labels exit program atScan]
    change (advance (TM2.step program))^[count + 1]
      (some ⟨some (labels .scan), (ambient, none),
        Function.update (prefixOn remaining [true] base) src (encodeWord count ++ suffix)⟩) = _
    rw [ih, prefixOn_comp]
    simp only [List.replicate_succ']

theorem seedStep (src : K) (currents remaining : List K)
    (hn : (currents ++ remaining).Nodup) (hsrc : src ∉ currents ++ remaining)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atSeed : program (labels .seed) = instruction src currents remaining labels exit .seed)
    (base : K → List Bool) (rest : List Bool) (ambient : σ) (register : Option Bool)
    (sourceWord : base src = true :: rest) :
    TM2.step program ⟨some (labels .seed), (ambient, register), base⟩ =
      some ⟨some (labels .scan), clean ambient,
        Function.update (prefixOn (currents ++ remaining) [false] base) src rest⟩ := by
  change some (TM2.stepAux (program (labels .seed)) _ _) = _
  rw [atSeed]
  simp only [instruction]
  rw [stepAux_pushEach (currents ++ remaining) hn]
  simp [TM2.stepAux, prefixOn, hsrc, sourceWord, clean]

theorem initializeTrace (src : K) (currents remaining : List K)
    (hn : (currents ++ remaining).Nodup) (hsrc : src ∉ currents ++ remaining)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, program (labels label) = instruction src currents remaining labels exit label)
    (base : K → List Bool) (ambient : σ) (m : Nat) (hm : 0 < m) (suffix : List Bool)
    (sourceWord : base src = encodeWord m ++ suffix) :
    (advance (TM2.step program))^[m + 1]
      (some ⟨some (labels .seed), clean ambient, base⟩) =
      some ⟨exit, clean ambient, initializedTapes src currents remaining base (m - 1) suffix⟩ := by
  have hrem : remaining.Nodup := (List.nodup_append.mp hn).2.1
  have hsrem : src ∉ remaining := fun h => hsrc (List.mem_append_right _ h)
  cases m with
  | zero => omega
  | succ n =>
    have first : (advance (TM2.step program))^[1]
        (some ⟨some (labels .seed), clean ambient, base⟩) =
        some ⟨some (labels .scan), clean ambient,
          Function.update (prefixOn (currents ++ remaining) [false] base) src
            (encodeWord n ++ suffix)⟩ := by
      rw [Function.iterate_one, advance_some]
      apply seedStep src currents remaining hn hsrc labels exit program (atLabels .seed)
      simpa [encodeWord, List.replicate_succ, List.append_assoc] using sourceWord
    have rest := scanTrace src currents remaining hrem hsrem labels exit program (atLabels .scan)
      (prefixOn (currents ++ remaining) [false] base) n suffix ambient none
    have joined := joinTrace first rest
    rw [show 1 + (n + 1) = n + 1 + 1 by omega] at joined
    simpa only [initializedTapes, Nat.add_sub_cancel] using joined

def initializeInTime (src : K) (currents remaining : List K)
    (hn : (currents ++ remaining).Nodup) (hsrc : src ∉ currents ++ remaining)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, program (labels label) = instruction src currents remaining labels exit label)
    (base : K → List Bool) (ambient : σ) (m : Nat) (hm : 0 < m) (suffix : List Bool)
    (sourceWord : base src = encodeWord m ++ suffix) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .seed), clean ambient, base⟩
      (some ⟨exit, clean ambient, initializedTapes src currents remaining base (m - 1) suffix⟩)
      (m + 1) where
  steps := m + 1
  evals_in_steps := initializeTrace src currents remaining hn hsrc labels exit program atLabels
    base ambient m hm suffix sourceWord
  steps_le_m := Nat.le_refl _

end PerfectCompleteness.TupleInitializationMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_NormalizationReadMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.NormalizationReadMachine


open Turing
open UniqueGamesTheorem.Foundations
open Complexity Complexity.MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

theorem steps_le_encoded_length {n : Nat} (clause : Target.Clause n) :
    clause[0].variableIndex.val + clause[1].variableIndex.val + clause[2].variableIndex.val + 6 ≤
      (encodeWords (clauseWords clause)).length := by
  simp only [clauseWords, encodeWords_append, List.length_append,
    literalWords, encodeWords, List.length_append, encodeWord_length, List.length_nil]
  omega

end PerfectCompleteness.NormalizationReadMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineLogCounter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
An actual logarithmic-round counter. Unary input is stripped to a raw tally;
each positive round emits one tally and halves the remaining input by pairing
symbols. The zero input emits one round explicitly. All tapes except the
canonical output are empty at termination.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineLogCounter

open Turing

theorem bitLength_half {n : Nat} (h : n ≠ 0) : bitLength n = bitLength (n / 2) + 1 := by
  by_cases hone : n = 1
  · subst n; rfl
  have hn : 2 ≤ n := by omega
  have hh : n / 2 ≠ 0 := by omega
  rw [bitLength_positive h, bitLength_positive hh, Nat.log2_def n, ite_eq_left hn]

theorem increments_half {n : Nat} (h : n ≠ 0) (started : Bool) :
    increments n started = increments (n / 2) true + 1 := by
  rw [increments, ite_eq_right h, increments_true, bitLength_half h]

theorem coreTime_positive {n : Nat} (h : n ≠ 0) :
    coreTime n = n + n / 2 + 3 + coreTime (n / 2) := by
  rw [coreTime, dite_eq_right h]

theorem coreTime_bound (n : Nat) : coreTime n ≤ 6 * n + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n; simp
    · rw [coreTime_positive hn]
      have smaller : n / 2 < n := by omega
      have bound := ih (n / 2) smaller
      omega

def program : Fin 5 → TM2.Stmt Alphabet (Fin 5) State
  | 0 => .push 2 (fun _ => false) (.goto fun _ => 1)
  | 1 => stripLoop
  | 2 => guardLoop
  | 3 => halfLoop
  | 4 => Reduction.MachineTransfer.loopAt 1 0 id false 4 (some 2)

def machine : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 2
  Γ := Alphabet
  Λ := Fin 5
  main := 0
  σ := State
  initialState := initialState
  m := program

def configuration (label : Option (Fin 5)) (state : State)
    (input scratch output : List Bool) : machine.Cfg :=
  ⟨label, state, rawTapes input scratch output⟩

def next := MachineComposition.advance machine.step

theorem stripStep_true (input scratch output : List Bool) (state : State) :
    machine.step (configuration (some 1) state (true :: input) scratch output) =
      some (configuration (some 1) (state.1, some true) input (true :: scratch) output) := by
  change some (TM2.stepAux stripLoop state (rawTapes (true :: input) scratch output)) = _
  simp [stripLoop, TM2.stepAux, rawTapes, configuration]
  rw [update_input, update_scratch]
  rfl

theorem stripStep_false (scratch output : List Bool) (state : State) :
    machine.step (configuration (some 1) state [false] scratch output) =
      some (configuration (some 4) initialState [] scratch output) := by
  change some (TM2.stepAux stripLoop state (rawTapes [false] scratch output)) = _
  simp [stripLoop, TM2.stepAux, rawTapes, configuration]
  rw [update_input]
  rfl

theorem stripTrace (n : Nat) (scratch output : List Bool) (state : State) :
    next^[n + 1] (some (configuration (some 1) state (encodeWord n) scratch output)) =
      some (configuration (some 4) initialState [] (List.replicate n true ++ scratch) output) := by
  induction n generalizing scratch state with
  | zero =>
    simpa only [encodeWord, List.replicate_zero, List.nil_append, Nat.zero_add,
      Function.iterate_one, next, MachineComposition.advance_some] using
      stripStep_false scratch output state
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change next^[n + 1]
      (machine.step (configuration (some 1) state (true :: encodeWord n) scratch output)) = _
    rw [stripStep_true, ih]
    congr 2
    simp only [List.replicate_add, List.replicate_one, List.append_assoc, List.singleton_append]

theorem halfStep_nil (scratch output : List Bool) (parity started : Bool) (register : Option Bool) :
    machine.step (configuration (some 3) ((parity, started), register) [] scratch output) =
      some (configuration (some 4) ((false, started), none) [] scratch output) := by
  change some (TM2.stepAux halfLoop ((parity, started), register) (rawTapes [] scratch output)) = _
  simp [halfLoop, TM2.stepAux, rawTapes, configuration]
  rw [update_input]
  rfl

theorem halfStep_false (input scratch output : List Bool) (started : Bool) (register : Option Bool) :
    machine.step (configuration (some 3) ((false, started), register) (true :: input) scratch output) =
      some (configuration (some 3) ((true, started), some true) input scratch output) := by
  change some (TM2.stepAux halfLoop ((false, started), register)
    (rawTapes (true :: input) scratch output)) = _
  simp [halfLoop, TM2.stepAux, rawTapes, configuration]
  rw [update_input]
  rfl

theorem halfStep_true (input scratch output : List Bool) (started : Bool) (register : Option Bool) :
    machine.step (configuration (some 3) ((true, started), register) (true :: input) scratch output) =
      some (configuration (some 3) ((false, started), some true) input (true :: scratch) output) := by
  change some (TM2.stepAux halfLoop ((true, started), register)
    (rawTapes (true :: input) scratch output)) = _
  simp [halfLoop, TM2.stepAux, rawTapes, configuration]
  rw [update_input, update_scratch]
  rfl

/-- A parity bit implements division by two using actual pop/push transitions. -/
theorem halfTrace (n m : Nat) (output : List Bool) (parity started : Bool)
    (register : Option Bool) :
    next^[n + 1] (some (configuration (some 3) ((parity, started), register)
      (List.replicate n true) (List.replicate m true) output)) =
      some (configuration (some 4) ((false, started), none) []
        (List.replicate (m + (n + if parity then 1 else 0) / 2) true) output) := by
  induction n generalizing m parity register with
  | zero =>
    cases parity <;>
      simpa only [Nat.zero_add, Function.iterate_one, next, MachineComposition.advance_some,
        List.replicate_zero, Bool.false_eq_true, ite_false, if_false, ite_true, if_true, Nat.zero_div,
        Nat.add_zero, Nat.reduceDiv] using
        halfStep_nil (List.replicate m true) output _ started register
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change next^[n + 1]
      (machine.step (configuration (some 3) ((parity, started), register)
        (true :: List.replicate n true) (List.replicate m true) output)) = _
    cases parity with
    | false =>
      rw [halfStep_false, ih]
      congr 2
    | true =>
      rw [halfStep_true]
      change next^[n + 1] (some (configuration (some 3) ((false, started), some true)
        (List.replicate n true) (List.replicate (m + 1) true) output)) = _
      rw [ih]
      congr 2
      congr 1
      change m + 1 + n / 2 = m + (n + 1 + 1) / 2
      omega

theorem restoreTrace (n : Nat) (output : List Bool) (started : Bool) :
    next^[n + 1] (some (configuration (some 4) ((false, started), none)
      [] (List.replicate n true) output)) =
      some (configuration (some 2) ((false, started), none) (List.replicate n true) [] output) := by
  have run := Reduction.MachineTransfer.transferAt_fromTapes (1 : Fin 3) 0 (by decide)
    id false (4 : Fin 5) (some 2) program rfl
    (rawTapes [] (List.replicate n true) output) (false, started) none
  simp only [rawTapes, List.length_replicate, List.reverse_replicate, List.map_id,
    List.append_nil] at run
  have tapesEq : Reduction.MachineTransfer.tapesAt (1 : Fin 3) 0
      (rawTapes [] (List.replicate n true) output) [] (List.replicate n true) =
      rawTapes (List.replicate n true) [] output := by
    funext k
    fin_cases k <;> rfl
  rw [tapesEq] at run
  exact run

theorem guardStep_zero (output : List Bool) (started : Bool) :
    machine.step (configuration (some 2) ((false, started), none) [] [] output) =
      some (configuration none initialState [] [] (if started then output else true :: output)) := by
  change some (TM2.stepAux guardLoop ((false, started), none) (rawTapes [] [] output)) = _
  cases started with
  | false =>
    simp [guardLoop, TM2.stepAux, rawTapes, configuration]
    rw [update_output]
    rfl
  | true =>
    simp [guardLoop, TM2.stepAux, rawTapes, configuration]
    rfl

theorem guardStep_positive (n : Nat) (output : List Bool) (started : Bool) :
    machine.step (configuration (some 2) ((false, started), none)
      (List.replicate (n + 1) true) [] output) =
      some (configuration (some 3) ((false, true), none)
        (List.replicate (n + 1) true) [] (true :: output)) := by
  change some (TM2.stepAux guardLoop ((false, started), none)
    (rawTapes (true :: List.replicate n true) [] output)) = _
  simp [guardLoop, TM2.stepAux, rawTapes, configuration]
  rw [update_output]
  simp only [List.replicate_succ]
  rfl

/-- The halving rounds are actual guard, scan, and restoration executions. -/
theorem coreTrace (n : Nat) (output : List Bool) (started : Bool) :
    next^[coreTime n] (some (configuration (some 2) ((false, started), none)
      (List.replicate n true) [] output)) =
      some (configuration none initialState [] []
        (List.replicate (increments n started) true ++ output)) := by
  induction n using Nat.strong_induction_on generalizing output started with
  | h n ih =>
    cases n with
    | zero =>
      rw [coreTime_zero, Function.iterate_one]
      cases started with
      | false => exact guardStep_zero output false
      | true => exact guardStep_zero output true
    | succ n =>
      have nonzero : n + 1 ≠ 0 := by omega
      have smaller : (n + 1) / 2 < n + 1 := by omega
      have recursive := ih ((n + 1) / 2) smaller (true :: output) true
      have half := halfTrace (n + 1) 0 (true :: output) false true none
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.zero_add,
        List.replicate_zero] at half
      have restore := restoreTrace ((n + 1) / 2) (true :: output) true
      rw [coreTime_positive nonzero]
      rw [show n + 1 + (n + 1) / 2 + 3 + coreTime ((n + 1) / 2) =
        (coreTime ((n + 1) / 2) + ((n + 1) / 2 + 1) + (n + 1 + 1)) + 1 by omega,
        Function.iterate_succ_apply]
      change next^[coreTime ((n + 1) / 2) + ((n + 1) / 2 + 1) + (n + 1 + 1)]
        (machine.step (configuration (some 2) ((false, started), none)
          (List.replicate (n + 1) true) [] output)) = _
      rw [guardStep_positive, Function.iterate_add_apply, half,
        Function.iterate_add_apply, restore, recursive]
      rw [increments_half nonzero started]
      simp only [List.replicate_add, List.replicate_one, List.append_assoc, List.singleton_append]

theorem initList_eq (input : List Bool) :
    initList machine input = configuration (some 0) initialState input [] [] := by
  unfold initList configuration
  congr 1
  funext k
  change Fin 3 at k
  fin_cases k <;> rfl

theorem haltList_eq (output : List Bool) :
    haltList machine output = configuration none initialState [] [] output := by
  unfold haltList configuration
  congr 1
  funext k
  change Fin 3 at k
  fin_cases k <;> rfl

theorem initialStep (input : List Bool) :
    machine.step (configuration (some 0) initialState input [] []) =
      some (configuration (some 1) initialState input [] [false]) := by
  change some (TM2.stepAux (.push (2 : Fin 3) (fun _ : State => false) (.goto fun _ => (1 : Fin 5)))
    initialState (rawTapes input [] [])) = _
  simp only [TM2.stepAux, rawTapes]
  rw [update_output]
  rfl

theorem totalTime_bound (n : Nat) : totalTime n ≤ 8 * n + 4 := by
  have bound := coreTime_bound n
  unfold totalTime
  omega

theorem machineTrace (n : Nat) :
    next^[totalTime n] (some (initList machine (encodeWord n))) =
      some (haltList machine (encodeWord (n.log2 + 1))) := by
  rw [initList_eq, haltList_eq]
  rw [show totalTime n = (coreTime n + (n + 1) + (n + 1)) + 1 by
    unfold totalTime; omega, Function.iterate_succ_apply]
  change next^[coreTime n + (n + 1) + (n + 1)]
    (machine.step (configuration (some 0) initialState (encodeWord n) [] [])) = _
  rw [initialStep, Function.iterate_add_apply, stripTrace]
  simp only [List.append_nil]
  rw [Function.iterate_add_apply]
  dsimp only [initialState]
  rw [restoreTrace n [false] false, coreTrace, increments_false]
  rfl

def outputsInTime (n : Nat) :
    TM2OutputsInTime machine (encodeWord n) (some (encodeWord (n.log2 + 1))) (8 * n + 4) where
  steps := totalTime n
  evals_in_steps := machineTrace n
  steps_le_m := totalTime_bound n

end UniqueGamesTheorem.Foundations.Complexity.MachineLogCounter

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_GraphCounterModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed Boolean-stack program prepending the logarithmic round count to
a graph table. It copies the original word, adds its two unary header values,
runs the actual logarithm machine, then emits the counter and original word. -/

namespace UniqueGamesTheorem.Foundations.Complexity.GraphCounterModel

open Turing

def program : Label → TM2.Stmt Alphabet Label State
  | .inl l => clockStatement (MachineLogCounter.program l)
  | .inr .copyFirst => Reduction.MachineTransfer.loopAt (.inr .input) (.inr .scratch)
      id false (.inr .copyFirst) (some (.inr .copySecond))
  | .inr .copySecond => MachineCopy.forkLoop (.inr .scratch) (.inr .input) (.inr .archive)
      false (.inr .copySecond) (some (.inr .seed))
  | .inr .seed => .push (.inl 0) (fun _ => false) (.goto fun _ => .inr .headerFirst)
  | .inr .headerFirst => readHeader (.inr .headerFirst) (.inr .headerSecond)
  | .inr .headerSecond => readHeader (.inr .headerSecond) (.inl 0)
  | .inr .clearInput => MachineDrain.drain (.inr .input) (.inr .clearInput)
      (some (.inr .clockCopy))
  | .inr .clockCopy => Reduction.MachineTransfer.loopAt (.inl 2) (.inr .scratch)
      id false (.inr .clockCopy) (some (.inr .archiveCopy))
  | .inr .archiveCopy => Reduction.MachineTransfer.loopAt (.inr .archive) (.inr .scratch)
      id false (.inr .archiveCopy) (some (.inr .finalReverse))
  | .inr .finalReverse => Reduction.MachineTransfer.loopAt (.inr .scratch) (.inr .output)
      id false (.inr .finalReverse) none

def machine : FinTM2 where
  K := Tape
  k₀ := .inr .input
  k₁ := .inr .output
  Γ := Alphabet
  Λ := Label
  main := .inr .copyFirst
  σ := State
  initialState := initialState
  m := program

theorem clockStep (extra : ExtraTape → List Bool) (register : Option Bool)
    (a b : MachineLogCounter.machine.Cfg)
    (h : MachineLogCounter.machine.step a = some b) :
    TM2.step program (clockConfiguration extra register a) =
      some (clockConfiguration extra register b) := by
  cases a with
  | mk label state tapes =>
      cases label with
      | none => cases h
      | some label =>
          have hb := Option.some.inj h
          subst b
          exact congrArg some (clockStatement_simulation extra register
            (MachineLogCounter.program label) state tapes)

def clockInTime (extra : ExtraTape → List Bool) (register : Option Bool) (n : Nat) :
    StateTransition.EvalsToInTime (TM2.step program)
      (clockConfiguration extra register (initList MachineLogCounter.machine (encodeWord n)))
      (some (clockConfiguration extra register
        (haltList MachineLogCounter.machine (encodeWord (n.log2 + 1))))) (8 * n + 4) :=
  MachineComposition.liftExecutionInTime _ _ (clockConfiguration extra register)
    (clockStep extra register) (MachineLogCounter.outputsInTime n)

end UniqueGamesTheorem.Foundations.Complexity.GraphCounterModel

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_GraphCounterFinish
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCompare.compareInTime_steps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual cleanup and emission of the counter followed by the preserved graph. -/

namespace UniqueGamesTheorem.Foundations.Complexity.GraphCounterFinish

open Turing GraphCounterModel

theorem start_eq (counter rest original : List Bool) :
    clockConfiguration (extraTapes rest original) none
      (haltList MachineLogCounter.machine counter) =
      ⟨some (.inr .clearInput), initialState, frame rest original counter [] []⟩ := by
  rw [MachineLogCounter.haltList_eq]
  unfold clockConfiguration
  congr 1
  funext tape
  cases tape with
  | inl i => fin_cases i <;> simp [clockTapes, frame, MachineLogCounter.configuration,
      MachineLogCounter.rawTapes]
  | inr k => cases k <;> rfl

theorem finish_eq (word : List Bool) :
    (⟨none, initialState, frame [] [] [] [] word⟩ : TM2.Cfg Alphabet Label State) =
      haltList machine word := by
  unfold haltList
  congr 1
  funext tape
  cases tape with
  | inl i => simp [machine, frame]
  | inr k => cases k <;> simp [machine, frame]; rfl

theorem clockCopyTrace (original counter : List Bool) :
    (MachineComposition.advance (TM2.step program))^[counter.length + 1]
      (some ⟨some (.inr .clockCopy), initialState, frame [] original counter [] []⟩) =
      some ⟨some (.inr .archiveCopy), initialState, frame [] original [] counter.reverse []⟩ := by
  have h := (Reduction.MachineTransfer.transferAtInTime (Sum.inl (2 : Fin 3))
    (Sum.inr ExtraTape.scratch) (by decide) id false (.inr .clockCopy)
    (some (.inr .archiveCopy)) program rfl (frame [] original counter [] [])
    MachineLogCounter.initialState none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[counter.length + 1]
    (some ⟨some (.inr .clockCopy), initialState, frame [] original counter [] []⟩) = _ at h
  have update : Reduction.MachineTransfer.tapesAt (Sum.inl (2 : Fin 3))
      (Sum.inr ExtraTape.scratch) (frame [] original counter [] []) []
        ((frame [] original counter [] [] (.inl 2)).reverse.map id ++
          frame [] original counter [] [] (.inr .scratch)) =
      frame [] original [] counter.reverse [] := by
    funext tape
    cases tape with
    | inl i => fin_cases i <;> simp [Reduction.MachineTransfer.tapesAt, frame]
    | inr k => cases k <;> simp [Reduction.MachineTransfer.tapesAt, frame]
  simpa only [update, initialState] using h

theorem archiveCopyTrace (original counter : List Bool) :
    (MachineComposition.advance (TM2.step program))^[original.length + 1]
      (some ⟨some (.inr .archiveCopy), initialState, frame [] original [] counter.reverse []⟩) =
      some ⟨some (.inr .finalReverse), initialState,
        frame [] [] [] (original.reverse ++ counter.reverse) []⟩ := by
  have h := (Reduction.MachineTransfer.transferAtInTime (Sum.inr ExtraTape.archive)
    (Sum.inr ExtraTape.scratch) (by decide) id false (.inr .archiveCopy)
    (some (.inr .finalReverse)) program rfl (frame [] original [] counter.reverse [])
    MachineLogCounter.initialState none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[original.length + 1]
    (some ⟨some (.inr .archiveCopy), initialState, frame [] original [] counter.reverse []⟩) = _ at h
  have update : Reduction.MachineTransfer.tapesAt (Sum.inr ExtraTape.archive)
      (Sum.inr ExtraTape.scratch) (frame [] original [] counter.reverse []) []
        ((frame [] original [] counter.reverse [] (.inr .archive)).reverse.map id ++
          frame [] original [] counter.reverse [] (.inr .scratch)) =
      frame [] [] [] (original.reverse ++ counter.reverse) [] := by
    funext tape
    cases tape with
    | inl i => simp [Reduction.MachineTransfer.tapesAt, frame]
    | inr k => cases k <;> simp [Reduction.MachineTransfer.tapesAt, frame]
  simpa only [update, initialState] using h

theorem reverseTrace (original counter : List Bool) :
    (MachineComposition.advance (TM2.step program))^[original.length + counter.length + 1]
      (some ⟨some (.inr .finalReverse), initialState,
        frame [] [] [] (original.reverse ++ counter.reverse) []⟩) =
      some (haltList machine (counter ++ original)) := by
  have h := (Reduction.MachineTransfer.transferAtInTime (Sum.inr ExtraTape.scratch)
    (Sum.inr ExtraTape.output) (by decide) id false (.inr .finalReverse) none program rfl
    (frame [] [] [] (original.reverse ++ counter.reverse) []) MachineLogCounter.initialState none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[
    (original.reverse ++ counter.reverse).length + 1]
    (some ⟨some (.inr .finalReverse), initialState,
      frame [] [] [] (original.reverse ++ counter.reverse) []⟩) = _ at h
  have update : Reduction.MachineTransfer.tapesAt (Sum.inr ExtraTape.scratch)
      (Sum.inr ExtraTape.output) (frame [] [] [] (original.reverse ++ counter.reverse) []) []
        ((frame [] [] [] (original.reverse ++ counter.reverse) [] (.inr .scratch)).reverse.map id ++
          frame [] [] [] (original.reverse ++ counter.reverse) [] (.inr .output)) =
      frame [] [] [] [] (counter ++ original) := by
    funext tape
    cases tape with
    | inl i => simp [Reduction.MachineTransfer.tapesAt, frame]
    | inr k => cases k <;> simp [Reduction.MachineTransfer.tapesAt, frame]
  rw [update] at h
  rw [← finish_eq]
  simp only [List.length_append, List.length_reverse] at h
  exact h

end UniqueGamesTheorem.Foundations.Complexity.GraphCounterFinish

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_GraphCounterStartLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual archive-copy and unary-header addition before the embedded logarithm
machine. The two header values stay on tapes; they never enter finite control. -/

namespace UniqueGamesTheorem.Foundations.Complexity.GraphCounterModel

open Turing

theorem headerStep_zero (again next : Label)
    (atHeader : program again = readHeader again next)
    (suffix archive : List Bool) (sum : Nat)
    (state : MachineLogCounter.State) (register : Option Bool) :
    TM2.step program
      ⟨some again, (state, register), startMemory (encodeWord 0 ++ suffix) archive (encodeWord sum)⟩ =
      some ⟨some next, (state, none), startMemory suffix archive (encodeWord sum)⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atHeader]
  simp only [readHeader, TM2.stepAux, startMemory, startExtra, encodeWord,
    List.replicate_zero, List.nil_append, List.singleton_append, List.head?_cons,
    List.tail_cons, Option.getD_some, Bool.cond_false]
  rw [startMemory_input_update]

theorem headerStep_succ (again next : Label)
    (atHeader : program again = readHeader again next)
    (n sum : Nat) (suffix archive : List Bool)
    (state : MachineLogCounter.State) (register : Option Bool) :
    TM2.step program
      ⟨some again, (state, register),
        startMemory (encodeWord (n + 1) ++ suffix) archive (encodeWord sum)⟩ =
      some ⟨some again, (state, some true),
        startMemory (encodeWord n ++ suffix) archive (encodeWord (sum + 1))⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atHeader]
  simp only [readHeader, TM2.stepAux, startMemory, startExtra, encodeWord,
    List.replicate_succ, List.cons_append, List.head?_cons, List.tail_cons,
    Option.getD_some, Bool.cond_true]
  rw [startMemory_input_update, startMemory_sum_update]
  rfl

theorem headerTrace (again next : Label)
    (atHeader : program again = readHeader again next)
    (n sum : Nat) (suffix archive : List Bool)
    (state : MachineLogCounter.State) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some again, (state, register),
        startMemory (encodeWord n ++ suffix) archive (encodeWord sum)⟩) =
      some ⟨some next, (state, none), startMemory suffix archive (encodeWord (n + sum))⟩ := by
  induction n generalizing sum register with
  | zero =>
      simpa only [Nat.zero_add, Function.iterate_one, MachineComposition.advance_some] using
        headerStep_zero again next atHeader suffix archive sum state register
  | succ n ih =>
      rw [Function.iterate_succ_apply, MachineComposition.advance_some]
      rw [headerStep_succ again next atHeader n sum suffix archive state register]
      simpa only [Nat.add_assoc, Nat.add_comm 1 sum] using ih (sum + 1) (some true)

def headerInTime (again next : Label)
    (atHeader : program again = readHeader again next)
    (n sum : Nat) (suffix archive : List Bool)
    (state : MachineLogCounter.State) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, (state, register), startMemory (encodeWord n ++ suffix) archive (encodeWord sum)⟩
      (some ⟨some next, (state, none), startMemory suffix archive (encodeWord (n + sum))⟩)
      (n + 1) where
  steps := n + 1
  evals_in_steps := headerTrace again next atHeader n sum suffix archive state register
  steps_le_m := le_rfl

theorem initialMemory (word : List Bool) :
    initList machine word =
      ⟨some (.inr .copyFirst), initialState, startMemory word [] []⟩ := by
  have ht : (initList machine word).stk = startMemory word [] [] := by
    funext tape
    cases tape with
    | inl k => simp [initList, machine, startMemory]
    | inr k => cases k <;> simp [initList, machine, startMemory, startExtra]; rfl
  exact congrArg (TM2.Cfg.mk _ _) ht

theorem clockInitialMemory (word rest : List Bool) (sum : Nat) :
    clockConfiguration (startExtra rest word) none
      (initList MachineLogCounter.machine (encodeWord sum)) =
      ⟨some (.inl 0), initialState, startMemory rest word (encodeWord sum)⟩ := by
  have ht : clockTapes (initList MachineLogCounter.machine (encodeWord sum)).stk
      (startExtra rest word) = startMemory rest word (encodeWord sum) := by
    funext tape
    cases tape with
    | inl k =>
      fin_cases k <;> simp [clockTapes, initList, MachineLogCounter.machine, startMemory]; rfl
    | inr k => rfl
  exact congrArg (TM2.Cfg.mk _ _) ht

end UniqueGamesTheorem.Foundations.Complexity.GraphCounterModel

/-! A complete finite machine adding the actual logarithmic graph-round count
as a unary prefix, preserving every bit of the original validated graph table. -/

namespace UniqueGamesTheorem.Foundations.Complexity.GraphCounterPrefix

open Turing PCP GraphCounterModel GraphCounterFinish

def rawOutput (n m : Nat) (rest : List Bool) : List Bool :=
  encodeWord ((n + m).log2 + 1) ++ (encodeWords [n, m] ++ rest)

end UniqueGamesTheorem.Foundations.Complexity.GraphCounterPrefix

/-! Generic placement of the odometer-digit initialization used in
`Hastad.SourceLoopInit`. This extracts its seed/copy/trim scheme from the
formula/header parser: the actual checked copy loop preserves the radix and
scratch, and a single positive-unary pop leaves the remaining count.
The finite program depends on the fixed digit width, not on the radix value. -/

/-!
A concrete sequential composition of two finite TM2 programs. The first output
is transferred to a temporary stack and then to the second input. Both loops
execute actual transitions and reset their shared register on exit. Static
renaming changes neither a stack word nor the number of executed transitions.
-/

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Reduction_MachineTransducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Reduction.MachineTransducer

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineSubstitution (pushWord stepAux_pushWord )

variable {Q : Type} [Fintype Q]

def program (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool) :
    Option (Q × Bool) →
      TM2.Stmt (fun _ : Bool => Bool) (Option (Q × Bool)) (Q × Option Bool)
  | none => loop initial
  | some (state, symbol) =>
      .load (fun register => (transition state symbol, register.2))
        (pushWord true (emit state symbol) (.goto fun _ => none))

def machine (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool) :
    FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Option (Q × Bool)
  main := none
  σ := Q × Option Bool
  initialState := (initial, none)
  m := program initial transition emit

def running (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (state : Q) (input accumulator : List Bool) (register : Option Bool) :
    (machine initial transition emit).Cfg :=
  ⟨some none, (state, register), tapeStacks input accumulator⟩

def emitting (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (oldState : Q) (symbol : Bool) (input accumulator : List Bool)
    (state : Q × Option Bool) : (machine initial transition emit).Cfg :=
  ⟨some (some (oldState, symbol)), state, tapeStacks input accumulator⟩

def halted (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (accumulator : List Bool) : (machine initial transition emit).Cfg :=
  ⟨none, (initial, none), tapeStacks [] accumulator⟩

/-- The final empty pop also restores the initial finite control state. -/
theorem step_empty (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (state : Q) (accumulator : List Bool)
    (register : Option Bool) :
    (machine initial transition emit).step
        (running initial transition emit state [] accumulator register) =
      some (halted initial transition emit accumulator) := by
  change some (TM2.stepAux (loop initial) (state, register) (tapeStacks [] accumulator)) = _
  simp [loop, TM2.stepAux, tapeStacks, halted]
  rw [update_input]
  rfl

theorem step_cons (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (state : Q) (symbol : Bool)
    (input accumulator : List Bool) (register : Option Bool) :
    (machine initial transition emit).step
        (running initial transition emit state (symbol :: input) accumulator register) =
      some (emitting initial transition emit state symbol input accumulator (state, some symbol)) := by
  change some (TM2.stepAux (loop initial) (state, register)
    (tapeStacks (symbol :: input) accumulator)) = _
  simp [loop, TM2.stepAux, tapeStacks, emitting]
  rw [update_input]
  rfl

/-- Emission reads the old state from its label and installs its successor state. -/
theorem step_emit (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (oldState : Q) (symbol : Bool)
    (input accumulator : List Bool) (state : Q × Option Bool) :
    (machine initial transition emit).step
        (emitting initial transition emit oldState symbol input accumulator state) =
      some (running initial transition emit (transition oldState symbol) input
        ((emit oldState symbol).reverse ++ accumulator) state.2) := by
  change some (TM2.stepAux (pushWord true (emit oldState symbol) (.goto fun _ => none))
    (transition oldState symbol, state.2) (tapeStacks input accumulator)) = _
  rw [stepAux_pushWord]
  simp only [TM2.stepAux]
  change some (⟨some none, (transition oldState symbol, state.2),
    Function.update (tapeStacks input accumulator) true
      ((emit oldState symbol).reverse ++ accumulator)⟩ :
    (machine initial transition emit).Cfg) = _
  exact congrArg (fun tapes : Bool → List Bool =>
    some (⟨some none, (transition oldState symbol, state.2), tapes⟩ :
      (machine initial transition emit).Cfg))
    (update_output input accumulator ((emit oldState symbol).reverse ++ accumulator))

def next (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (configuration : Option (machine initial transition emit).Cfg) :
    Option (machine initial transition emit).Cfg :=
  configuration.bind (machine initial transition emit).step

theorem two_steps_cons (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (state : Q) (symbol : Bool)
    (input accumulator : List Bool) (register : Option Bool) :
    (next initial transition emit)^[2]
        (some (running initial transition emit state (symbol :: input) accumulator register)) =
      some (running initial transition emit (transition state symbol) input
        ((emit state symbol).reverse ++ accumulator) (some symbol)) := by
  change (machine initial transition emit).step
    (running initial transition emit state (symbol :: input) accumulator register) >>=
      (machine initial transition emit).step = _
  rw [step_cons]
  exact step_emit initial transition emit state symbol input accumulator (state, some symbol)

/-- Exact execution from any finite control state, accumulator, and symbol register. -/
theorem transduce_steps (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (state : Q) (input accumulator : List Bool)
    (register : Option Bool) :
    (next initial transition emit)^[2 * input.length + 1]
        (some (running initial transition emit state input accumulator register)) =
      some (halted initial transition emit ((output transition emit state input).reverse ++ accumulator)) := by
  induction input generalizing state accumulator register with
  | nil =>
    simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, Function.iterate_one, next,
      Option.bind_some, output, List.reverse_nil, List.nil_append]
      using step_empty initial transition emit state accumulator register
  | cons symbol input ih =>
    rw [List.length_cons]
    rw [show 2 * (input.length + 1) + 1 = (2 * input.length + 1) + 2 by omega]
    rw [Function.iterate_add_apply, two_steps_cons, ih]
    simp only [output, List.reverse_append, List.append_assoc]

theorem initList_eq (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (input : List Bool) :
    initList (machine initial transition emit) input =
      running initial transition emit initial input [] none := by
  unfold initList running
  congr 1
  funext side
  cases side <;> rfl

theorem haltList_eq (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (accumulator : List Bool) :
    haltList (machine initial transition emit) accumulator =
      halted initial transition emit accumulator := by
  unfold haltList halted
  congr 1

theorem transduce_init_steps (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (input : List Bool) :
    (next initial transition emit)^[2 * input.length + 1]
        (some (initList (machine initial transition emit) input)) =
      some (haltList (machine initial transition emit) (output transition emit initial input).reverse) := by
  rw [initList_eq, haltList_eq]
  simpa only [List.append_nil] using transduce_steps initial transition emit initial input [] none

def outputsInTime (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (input : List Bool) :
    TM2OutputsInTime (machine initial transition emit) input
      (some (output transition emit initial input).reverse) (2 * input.length + 1) where
  steps := 2 * input.length + 1
  evals_in_steps := transduce_init_steps initial transition emit input
  steps_le_m := Nat.le_refl _

@[simp] theorem outputsInTime_steps (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (input : List Bool) :
    (outputsInTime initial transition emit input).steps = 2 * input.length + 1 := rfl

end UniqueGamesTheorem.Reduction.MachineTransducer

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineTransducerCopy
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCompare.compareInTime_steps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.MachineTransducerCopy

open Turing
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ Q : Type} [DecidableEq K]

abbrev tapes (source scratch destination : K) (base : K → List Bool)
    (input scratchWord outputWord : List Bool) : K → List Bool :=
  MachineCopy.forkTapes source scratch destination base input scratchWord outputWord

theorem update_source (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination) (base : K → List Bool)
    (input scratchWord outputWord replacement : List Bool) :
    Function.update (tapes source scratch destination base input scratchWord outputWord)
      source replacement = tapes source scratch destination base replacement scratchWord outputWord := by
  funext k
  by_cases hs : k = source
  · subst k; simp [tapes, MachineCopy.forkTapes, sourceScratch, sourceDestination]
  · by_cases ht : k = scratch
    · subst k; simp [tapes, MachineCopy.forkTapes, Ne.symm sourceScratch, scratchDestination]
    · by_cases hd : k = destination
      · subst k; simp [tapes, MachineCopy.forkTapes, Ne.symm sourceDestination]
      · simp [tapes, MachineCopy.forkTapes, hs, ht, hd]

theorem update_scratch (source scratch destination : K)
    (scratchDestination : scratch ≠ destination) (base : K → List Bool)
    (input scratchWord outputWord replacement : List Bool) :
    Function.update (tapes source scratch destination base input scratchWord outputWord)
      scratch replacement = tapes source scratch destination base input replacement outputWord := by
  funext k
  by_cases ht : k = scratch
  · subst k; simp [tapes, MachineCopy.forkTapes, scratchDestination]
  · by_cases hd : k = destination
    · subst k; simp [tapes, MachineCopy.forkTapes, Ne.symm scratchDestination]
    · simp [tapes, MachineCopy.forkTapes, ht, hd]

theorem update_output (source scratch destination : K) (base : K → List Bool)
    (input scratchWord outputWord replacement : List Bool) :
    Function.update (tapes source scratch destination base input scratchWord outputWord)
      destination replacement = tapes source scratch destination base input scratchWord replacement := by
  simp [tapes, MachineCopy.forkTapes]

theorem scanStep_empty (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (initial : Q) (scanLabel restoreLabel : Λ) (emitterLabel : Q → Bool → Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atScan : program scanLabel = scanLoop source scratch initial emitterLabel restoreLabel)
    (base : K → List Bool) (scratchWord outputWord : List Bool)
    (ambient : σ) (control : Q) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, control), register),
      tapes source scratch destination base [] scratchWord outputWord⟩ =
      some ⟨some restoreLabel, ((ambient, initial), none),
        tapes source scratch destination base [] scratchWord outputWord⟩ := by
  change some (TM2.stepAux (program scanLabel) ((ambient, control), register)
    (tapes source scratch destination base [] scratchWord outputWord)) = _
  rw [atScan]
  simp [scanLoop, TM2.stepAux, sourceScratch, sourceDestination, scratchDestination,
    update_source]

theorem scanStep_cons (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (initial : Q) (scanLabel restoreLabel : Λ) (emitterLabel : Q → Bool → Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atScan : program scanLabel = scanLoop source scratch initial emitterLabel restoreLabel)
    (base : K → List Bool) (symbol : Bool) (input scratchWord outputWord : List Bool)
    (ambient : σ) (control : Q) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, control), register),
      tapes source scratch destination base (symbol :: input) scratchWord outputWord⟩ =
      some ⟨some (emitterLabel control symbol), ((ambient, control), some symbol),
        tapes source scratch destination base input (symbol :: scratchWord) outputWord⟩ := by
  change some (TM2.stepAux (program scanLabel) ((ambient, control), register)
    (tapes source scratch destination base (symbol :: input) scratchWord outputWord)) = _
  rw [atScan]
  simp [scanLoop, TM2.stepAux, sourceScratch, sourceDestination, scratchDestination,
    update_source, update_scratch]

theorem restoreTapes (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (base : K → List Bool) (scratchEmpty : base scratch = []) (outputWord : List Bool) :
    Reduction.MachineTransfer.tapesAt scratch source
      (tapes source scratch destination base [] (base source).reverse outputWord)
      [] (base source) = Function.update base destination outputWord := by
  funext k
  by_cases hs : k = source
  · subst k; simp [Reduction.MachineTransfer.tapesAt, sourceDestination]
  · by_cases ht : k = scratch
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, Ne.symm sourceScratch, scratchDestination, scratchEmpty]
    · by_cases hd : k = destination
      · subst k
        simp [Reduction.MachineTransfer.tapesAt, tapes, MachineCopy.forkTapes,
          Ne.symm sourceDestination, Ne.symm scratchDestination]
      · simp [Reduction.MachineTransfer.tapesAt, tapes, MachineCopy.forkTapes, hs, ht, hd]

end UniqueGamesTheorem.Foundations.Complexity.MachineTransducerCopy

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineUnaryAffineAt
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCompare.compareInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec.decodeWords_encodeWord _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter.counterTapes_counter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAffineAt

open Turing
open MachineComposition
open Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

def tapes (source scratch destination : K) (base : K → List Bool)
    (input saved output : List Bool) : K → List Bool :=
  MachineCopy.forkTapes source scratch destination base input saved output

@[simp] theorem tapes_source (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination)
    (base : K → List Bool) (input saved output : List Bool) :
    tapes source scratch destination base input saved output source = input :=
  MachineCopy.forkTapes_source source scratch destination hs hd base input saved output

@[simp] theorem tapes_scratch (source scratch destination : K) (hsd : scratch ≠ destination)
    (base : K → List Bool) (input saved output : List Bool) :
    tapes source scratch destination base input saved output scratch = saved :=
  MachineCopy.forkTapes_left source scratch destination hsd base input saved output

@[simp] theorem tapes_destination (source scratch destination : K)
    (base : K → List Bool) (input saved output : List Bool) :
    tapes source scratch destination base input saved output destination = output :=
  MachineCopy.forkTapes_right source scratch destination base input saved output

theorem update_source (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (base : K → List Bool) (input saved output replacement : List Bool) :
    Function.update (tapes source scratch destination base input saved output) source replacement =
      tapes source scratch destination base replacement saved output := by
  funext k
  by_cases h₀ : k = source
  · subst k; simp [tapes, MachineCopy.forkTapes, hs, hd]
  · by_cases h₁ : k = scratch
    · subst k; simp [tapes, MachineCopy.forkTapes, h₀, hsd]
    · by_cases h₂ : k = destination
      · subst k; simp [tapes, MachineCopy.forkTapes, h₀]
      · simp [tapes, MachineCopy.forkTapes, h₀, h₁, h₂]

theorem update_scratch (source scratch destination : K) (hsd : scratch ≠ destination)
    (base : K → List Bool) (input saved output replacement : List Bool) :
    Function.update (tapes source scratch destination base input saved output) scratch replacement =
      tapes source scratch destination base input replacement output := by
  funext k
  by_cases h : k = scratch
  · subst k; simp [tapes, MachineCopy.forkTapes, hsd]
  · by_cases h' : k = destination
    · subst k; simp [tapes, MachineCopy.forkTapes, h]
    · simp [tapes, MachineCopy.forkTapes, h, h']

theorem update_destination (source scratch destination : K)
    (base : K → List Bool) (input saved output replacement : List Bool) :
    Function.update (tapes source scratch destination base input saved output) destination replacement =
      tapes source scratch destination base input saved replacement := by
  simp [tapes, MachineCopy.forkTapes]

theorem prepend_replicate_word (c b : Nat) (suffix : List Bool) :
    List.replicate c true ++ (encodeWord b ++ suffix) =
      encodeWord (c + b) ++ suffix := by
  simp only [encodeWord, List.replicate_add, List.append_assoc]

theorem restoreTapes (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (base : K → List Bool) (a value : Nat) (suffix output : List Bool) :
    Reduction.MachineTransfer.tapesAt scratch source
      (tapes source scratch destination base (encodeWord 0 ++ suffix)
        (List.replicate a true) (encodeWord value ++ output))
      [] (encodeWord a ++ suffix) =
      tapes source scratch destination base (encodeWord a ++ suffix) [] (encodeWord value ++ output) := by
  funext k
  by_cases h₀ : k = source
  · subst k; simp [tapes, MachineCopy.forkTapes, Reduction.MachineTransfer.tapesAt, hs, hd]
  · by_cases h₁ : k = scratch
    · subst k
      simp [tapes, MachineCopy.forkTapes, Reduction.MachineTransfer.tapesAt, Ne.symm hs, hsd]
    · by_cases h₂ : k = destination
      · subst k
        simp [tapes, MachineCopy.forkTapes, Reduction.MachineTransfer.tapesAt, Ne.symm hd, Ne.symm hsd]
      · simp [tapes, MachineCopy.forkTapes, Reduction.MachineTransfer.tapesAt, h₀, h₁, h₂]

end UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAffineAt

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineLookupLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual traces for the fixed unary lookup machine. Successful lookup preserves
an arbitrary unread table suffix. Rejection relative to a list's end is stated
only for its complete, unframed encoding, so no hidden endpoint is assumed.
-/

/-! Actual lookup from a preserved table. A fresh copy is prefixed to the scan
stack before each access. The old scan suffix is retained and need not be
cleared between accesses. No graph/table data occurs in finite control. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePreservingLookup

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def finalTapes (tape : Fin 5 → K) (base : K → List Bool)
    (values : List Nat) (index value : Nat)
    (indexSuffix workSuffix output : List Bool) : K → List Bool :=
  MachineLookup.tapes (tape 1) (tape 2) (tape 3) base
    (encodeWord 0 ++ indexSuffix)
    (encodeWords (values.drop (index + 1)) ++ workSuffix) (encodeWord value ++ output)

theorem preservingLookup_steps_le (values : List Nat) (i value : Nat)
    (selected : values[i]? = some value) :
    2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values i + 1 ≤
      5 * (encodeWords values).length + 3 := by
  have ht := MachineLookupSpec.steps_le_input_encoding_size values i
  have hi := MachineLookupSpec.index_length_le values i value selected
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachinePreservingLookup

namespace UniqueGamesTheorem.Foundations.Complexity.MachineAffineLookup

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def steps (values : List Nat) (a coefficient offset : Nat) : Nat :=
  (2 * (a + 1) + 1) +
    (2 * ((encodeWords values).length + 1) +
      MachineLookupSpec.steps values (coefficient * a + offset) + 1)

def finalTapes (tape : Fin 5 → K) (base : K → List Bool)
    (values : List Nat) (index value : Nat) : K → List Bool :=
  MachinePreservingLookup.finalTapes tape base values index value
    (base (tape 1)) (base (tape 2)) (base (tape 3))

theorem steps_le (values : List Nat) (a coefficient offset value : Nat)
    (selected : values[coefficient * a + offset]? = some value) :
    steps values a coefficient offset ≤ 2 * a + 5 * (encodeWords values).length + 6 := by
  have h := MachinePreservingLookup.preservingLookup_steps_le values
    (coefficient * a + offset) value selected
  unfold steps
  omega

theorem steps_le_table (values : List Nat) (a coefficient offset value : Nat)
    (selected : values[coefficient * a + offset]? = some value)
    (ha : a ≤ (encodeWords values).length) :
    steps values a coefficient offset ≤ 7 * (encodeWords values).length + 6 := by
  have h := steps_le values a coefficient offset value selected
  omega

theorem finalTapes_other (tape : Fin 5 → K) (base : K → List Bool)
    (values : List Nat) (index value : Nat) (k : K)
    (h₁ : k ≠ tape 1) (h₂ : k ≠ tape 2) (h₃ : k ≠ tape 3) :
    finalTapes tape base values index value k = base k :=
  MachineLookup.tapes_other _ _ _ _ h₁ h₂ h₃ _ _ _ _

theorem finalTapes_output (tape : Fin 5 → K) (base : K → List Bool)
    (values : List Nat) (index value : Nat) :
    finalTapes tape base values index value (tape 3) = encodeWord value ++ base (tape 3) :=
  MachineLookup.tapes_destination _ _ _ _ _ _ _

end UniqueGamesTheorem.Foundations.Complexity.MachineAffineLookup

/-!
A fixed-width gather from an input-resident table. Every coordinate index lives
on a unary tape. The coefficient and coordinate-dependent offsets alone live
in finite control. Actual preserving affine lookup instructions read each
requested field, and the proof below composes their traces. This is the gather
phase of product-row construction, before the fixed-width Horner phase.
-/

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineProductGatherBoundsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds on the actual work stacks left by the preserving gather. These
bounds justify clearing the query/scan remnants after each product field;
they are consequences of the exact tape formulas, not runtime assumptions. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePreservingLookupClean

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

/-- Exact copy, lookup, return, and residual-cleanup transition count. -/
def steps (values : List Nat) (index : Nat) : Nat :=
  (2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values index + 1) +
    ((encodeWords (values.drop (index + 1))).length + 1)

theorem remaining_length_le (values : List Nat) (index : Nat) :
    (encodeWords (values.drop (index + 1))).length ≤ (encodeWords values).length := by
  have h := congrArg (fun words : List Nat => (encodeWords words).length)
    (List.take_append_drop (index + 1) values)
  simp only [encodeWords_append, List.length_append] at h
  omega

theorem steps_le (values : List Nat) (index value : Nat)
    (selected : values[index]? = some value) :
    steps values index ≤ 6 * (encodeWords values).length + 4 := by
  have hc := MachinePreservingLookup.preservingLookup_steps_le values index value selected
  have hd := remaining_length_le values index
  unfold steps
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachinePreservingLookupClean

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineUnaryLessAtLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical comparison of two unary fields. Matched true bits are saved on
two empty scratch stacks. The first delimiter determines the comparison, then
both saved prefixes are restored. All input suffixes and other tapes survive. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def statement (slots : Fin 4 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .scan => scan slots (labels .scan) (labels .restoreLeft)
  | .restoreLeft => Reduction.MachineTransfer.loopAt (slots 2) (slots 0) id false
      (labels .restoreLeft) (some (labels .restoreRight))
  | .restoreRight => Reduction.MachineTransfer.loopAt (slots 3) (slots 1) id false
      (labels .restoreRight) exit

end UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt

/-!
Actual unary-guard iteration for a logarithmic number of rounds. Semantic
cardinality grows by a fixed linear factor. A separate encoding polynomial
bounds each intermediate word; it is never iterated as a size recurrence.
The body hypotheses are individual executions of the supplied finite program.
-/

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineAppendAt
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCompare.compareInTime_steps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.MachineAppendAt

open Turing

variable {K Λ σ β : Type} [DecidableEq K]

def appendTapes (source destination : K) (base : K → List β) : K → List β :=
  Reduction.MachineTransfer.tapesAt source destination base []
    (base destination ++ base source)

@[simp] theorem appendTapes_source (source destination : K)
    (distinct : source ≠ destination) (base : K → List β) :
    appendTapes source destination base source = [] := by
  simp [appendTapes, distinct]

@[simp] theorem appendTapes_destination (source destination : K) (base : K → List β) :
    appendTapes source destination base destination = base destination ++ base source := by
  simp [appendTapes]

def firstTapes (destination scratch : K) (base : K → List β) : K → List β :=
  Reduction.MachineTransfer.tapesAt destination scratch base [] (base destination).reverse

def secondTapes (source destination scratch : K) (base : K → List β) : K → List β :=
  Reduction.MachineTransfer.tapesAt source scratch (firstTapes destination scratch base) []
    ((base source).reverse ++ (base destination).reverse)

theorem finalTapes_eq (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch) (base : K → List β)
    (scratchEmpty : base scratch = []) :
    Reduction.MachineTransfer.tapesAt scratch destination
      (secondTapes source destination scratch base) [] (base destination ++ base source) =
        appendTapes source destination base := by
  funext k
  by_cases hs : k = source
  · subst k
    simp [appendTapes, secondTapes, firstTapes, Reduction.MachineTransfer.tapesAt,
      sourceDestination, sourceScratch]
  · by_cases hd : k = destination
    · subst k
      simp [appendTapes, Reduction.MachineTransfer.tapesAt]
    · by_cases ht : k = scratch
      · subst k
        simp [appendTapes, Reduction.MachineTransfer.tapesAt, Ne.symm sourceScratch,
          Ne.symm destinationScratch, scratchEmpty]
      · simp [appendTapes, secondTapes, firstTapes, Reduction.MachineTransfer.tapesAt,
          hs, hd, ht]

theorem appendTrace (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch)
    (fallback : β) (firstLabel secondLabel thirdLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atFirst : program firstLabel = Reduction.MachineTransfer.loopAt destination scratch
      id fallback firstLabel (some secondLabel))
    (atSecond : program secondLabel = Reduction.MachineTransfer.loopAt source scratch
      id fallback secondLabel (some thirdLabel))
    (atThird : program thirdLabel = Reduction.MachineTransfer.loopAt scratch destination
      id fallback thirdLabel exit)
    (base : K → List β) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option β) :
    (MachineComposition.advance (TM2.step program))^[
        2 * ((base source).length + (base destination).length) + 3]
      (some ⟨some firstLabel, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), appendTapes source destination base⟩ := by
  have first := Reduction.MachineTransfer.transferAt_fromTapes destination scratch
    destinationScratch id fallback firstLabel (some secondLabel) program atFirst
    base ambient register
  change (MachineComposition.advance (TM2.step program))^[(base destination).length + 1]
    (some ⟨some firstLabel, (ambient, register), base⟩) = _ at first
  simp only [List.map_id, scratchEmpty, List.append_nil] at first
  change (MachineComposition.advance (TM2.step program))^[(base destination).length + 1]
    (some ⟨some firstLabel, (ambient, register), base⟩) =
      some ⟨some secondLabel, (ambient, none), firstTapes destination scratch base⟩ at first
  have firstSource : firstTapes destination scratch base source = base source := by
    simp [firstTapes, Reduction.MachineTransfer.tapesAt, sourceDestination, sourceScratch]
  have firstScratch : firstTapes destination scratch base scratch =
      (base destination).reverse := by
    simp [firstTapes]
  have second := Reduction.MachineTransfer.transferAt_fromTapes source scratch
    sourceScratch id fallback secondLabel (some thirdLabel) program atSecond
    (firstTapes destination scratch base) ambient none
  change (MachineComposition.advance (TM2.step program))^[
      (firstTapes destination scratch base source).length + 1]
    (some ⟨some secondLabel, (ambient, none), firstTapes destination scratch base⟩) = _
      at second
  rw [firstSource, firstScratch] at second
  simp only [List.map_id] at second
  change (MachineComposition.advance (TM2.step program))^[(base source).length + 1]
    (some ⟨some secondLabel, (ambient, none), firstTapes destination scratch base⟩) =
      some ⟨some thirdLabel, (ambient, none), secondTapes source destination scratch base⟩
        at second
  have secondScratch : secondTapes source destination scratch base scratch =
      (base source).reverse ++ (base destination).reverse := by
    simp [secondTapes]
  have secondDestination : secondTapes source destination scratch base destination = [] := by
    simp [secondTapes, firstTapes, Reduction.MachineTransfer.tapesAt,
      Ne.symm sourceDestination, destinationScratch]
  have third := Reduction.MachineTransfer.transferAt_fromTapes scratch destination
    (Ne.symm destinationScratch) id fallback thirdLabel exit program atThird
    (secondTapes source destination scratch base) ambient none
  change (MachineComposition.advance (TM2.step program))^[
      (secondTapes source destination scratch base scratch).length + 1]
    (some ⟨some thirdLabel, (ambient, none), secondTapes source destination scratch base⟩) = _
      at third
  rw [secondScratch, secondDestination] at third
  simp only [List.map_id, List.reverse_append, List.reverse_reverse, List.append_nil,
    List.length_append, List.length_reverse] at third
  rw [finalTapes_eq source destination scratch sourceDestination sourceScratch
    destinationScratch base scratchEmpty] at third
  rw [show 2 * ((base source).length + (base destination).length) + 3 =
      ((base source).length + (base destination).length + 1) +
        (((base source).length + 1) + ((base destination).length + 1)) by omega]
  rw [Function.iterate_add_apply]
  rw [Function.iterate_add_apply (m := (base source).length + 1)
    (n := (base destination).length + 1), first, second]
  exact third

end UniqueGamesTheorem.Foundations.Complexity.MachineAppendAt

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRepeat
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCompare.compareInTime_steps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed finite TM2 interpreter for a unary number of runs of a fixed
certified machine. The counter is data on a separate tape. Every body run is
lifted from an actual `TM2OutputsInTime` witness, and all transfers are executed
by the checked finite transfer loops. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRepeat
open Turing

abbrev Symbols (M : FinTM2) := MachineEmbedding.Alphabet M.Γ (fun _ : ExtraTape => M.Γ M.k₀)

def auxProgram (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool) (output : M.Γ M.k₁ ≃ Bool) :
    Phase → TM2.Stmt (Symbols M) (Label M) (State M)
  | .parse => .pop (.inl M.k₀) (fun s v => (s.1,v))
      (.branch (fun s => input (s.2.getD (input.symm false)))
        (.push (.inr .counter) (fun _ => input.symm true)
          (.load (fun s => (s.1,none)) (.goto (fun _ => .inr .parse))))
        (.load (fun s => (s.1,none)) (.goto (fun _ => .inr .guard))))
  | .guard => .pop (.inr .counter) (fun s v => (s.1,v))
      (.branch (fun s => s.2.isSome)
        (.load (fun s => (s.1,none)) (.goto (fun _ => .inl M.main)))
        (.load (fun s => (s.1,none)) (.goto (fun _ => .inr .finalToTemp))))
  | .bodyToTemp => Reduction.MachineTransfer.loopAt (Γ := Symbols M) (Λ := Label M) (.inl M.k₁) (.inr .temporary)
      (fun b => input.symm (output b)) (input.symm false)
      (.inr .bodyToTemp) (some (.inr .tempToBody))
  | .tempToBody => Reduction.MachineTransfer.loopAt (Γ := Symbols M) (Λ := Label M) (.inr .temporary) (.inl M.k₀)
      id (input.symm false) (.inr .tempToBody) (some (.inr .guard))
  | .finalToTemp => Reduction.MachineTransfer.loopAt (Γ := Symbols M) (Λ := Label M) (.inl M.k₀) (.inr .temporary)
      id (input.symm false) (.inr .finalToTemp) (some (.inr .tempToOutput))
  | .tempToOutput => Reduction.MachineTransfer.loopAt (Γ := Symbols M) (Λ := Label M) (.inr .temporary) (.inr .output)
      id (input.symm false) (.inr .tempToOutput) none

def inputTapes (M : FinTM2) (word counter : List (M.Γ M.k₀)) : ∀k, List (Symbols M k) :=
  MachineEmbedding.tapes (initList M word).stk (extraTapes M counter [] [])

@[simp] theorem inputTapes_input (M : FinTM2) (word counter : List (M.Γ M.k₀)) :
    inputTapes M word counter (.inl M.k₀) = word := by
  simp [inputTapes, initList]

@[simp] theorem inputTapes_counter (M : FinTM2) (word counter : List (M.Γ M.k₀)) :
    inputTapes M word counter (.inr .counter) = counter := rfl

def inputConfig (M : FinTM2) (phase : Phase) (word counter : List (M.Γ M.k₀)) :
    TM2.Cfg (Symbols M) (Label M) (State M) :=
  ⟨some (.inr phase),(M.initialState,none),inputTapes M word counter⟩

def embedded (M : FinTM2) (counter : List (M.Γ M.k₀)) (c : M.Cfg) :
    TM2.Cfg (Symbols M) (Label M) (State M) :=
  MachineEmbedding.configuration (some (.inr .bodyToTemp)) (none : Option (M.Γ M.k₀))
    (extraTapes M counter [] []) c

def temporaryTapes (M : FinTM2) (word counter : List (M.Γ M.k₀)) : ∀k, List (Symbols M k) :=
  MachineEmbedding.tapes (fun _ => []) (extraTapes M counter word [])

def temporaryConfig (M : FinTM2) (phase : Phase) (word counter : List (M.Γ M.k₀)) :
    TM2.Cfg (Symbols M) (Label M) (State M) :=
  ⟨some (.inr phase),(M.initialState,none),temporaryTapes M word counter⟩

theorem inputTapes_update_input (M : FinTM2)
    (word counter replacement : List (M.Γ M.k₀)) :
    Function.update (inputTapes M word counter) (.inl M.k₀) replacement =
      inputTapes M replacement counter := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₀
    · subst k; simp [inputTapes, initList]
    · simp [inputTapes, initList, h]
  | inr k => simp [inputTapes]

theorem inputTapes_update_counter (M : FinTM2)
    (word counter replacement : List (M.Γ M.k₀)) :
    Function.update (inputTapes M word counter) (.inr .counter) replacement =
      inputTapes M word replacement := by
  funext k
  cases k with
  | inl k => simp [inputTapes]
  | inr k => cases k <;> simp [inputTapes, extraTapes]

variable (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool) (output : M.Γ M.k₁ ≃ Bool)

theorem bodyToTemp_tapes (result : List (M.Γ M.k₁)) (counter : List (M.Γ M.k₀)) :
    Reduction.MachineTransfer.tapesAt (.inl M.k₁) (.inr .temporary)
      (embedded M counter (haltList M result)).stk []
      (result.reverse.map (fun b => input.symm (output b))) =
    temporaryTapes M (result.reverse.map (fun b => input.symm (output b))) counter := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₁
    · subst k; simp [Reduction.MachineTransfer.tapesAt, temporaryTapes]
    · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, embedded,
        MachineEmbedding.configuration, haltList, h]
  | inr k =>
    cases k <;> simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, embedded,
      MachineEmbedding.configuration, extraTapes]

theorem tempToBody_tapes (word counter : List (M.Γ M.k₀)) :
    Reduction.MachineTransfer.tapesAt (Γ := Symbols M) (.inr .temporary) (.inl M.k₀)
      (temporaryTapes M word counter) [] word.reverse = inputTapes M word.reverse counter := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₀
    · subst k; simp [Reduction.MachineTransfer.tapesAt, inputTapes, initList]
    · simp [Reduction.MachineTransfer.tapesAt, inputTapes, temporaryTapes, initList, h]
  | inr k =>
    cases k <;> simp [Reduction.MachineTransfer.tapesAt, inputTapes, temporaryTapes, extraTapes]

theorem finalToTemp_tapes (word : List (M.Γ M.k₀)) :
    Reduction.MachineTransfer.tapesAt (Γ := Symbols M) (.inl M.k₀) (.inr .temporary)
      (inputTapes M word []) [] word.reverse = temporaryTapes M word.reverse [] := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₀
    · subst k; simp [Reduction.MachineTransfer.tapesAt, temporaryTapes]
    · simp [Reduction.MachineTransfer.tapesAt, inputTapes, temporaryTapes, initList, h]
  | inr k =>
    cases k <;> simp [Reduction.MachineTransfer.tapesAt, inputTapes, temporaryTapes, extraTapes]

omit M input output in
/-- Explicit sum form of the actual repeat budget. -/
theorem loopBudget_eq_sum (count : Nat) (words : Nat → List Bool) (budgets : Nat → Nat) :
    loopBudget count words budgets =
      (∑ i ∈ Finset.range count, (budgets i + 2*(words (i+1)).length+3)) +
      2*(words count).length+3 := by
  induction count generalizing words budgets with
  | zero => simp [loopBudget]
  | succ count ih =>
    rw [loopBudget, ih, Finset.sum_range_succ']
    simp only [Nat.zero_add]
    omega

omit M input output in
/-- A uniform bound along the executed sequence is enough to bound the actual
repeat runtime. No polynomial growth of an arbitrary iteration is asserted. -/
theorem loopBudget_le (count : Nat) (words : Nat → List Bool) (budgets : Nat → Nat)
    (bodyBound lengthBound : Nat)
    (hb : ∀i, i < count → budgets i ≤ bodyBound)
    (hl : ∀i, i ≤ count → (words i).length ≤ lengthBound) :
    loopBudget count words budgets ≤ count*(bodyBound+2*lengthBound+3)+2*lengthBound+3 := by
  rw [loopBudget_eq_sum]
  have hs : (∑ i ∈ Finset.range count, (budgets i+2*(words (i+1)).length+3)) ≤
      count*(bodyBound+2*lengthBound+3) := by
    calc
      _ ≤ ∑ i ∈ Finset.range count, (bodyBound+2*lengthBound+3) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := Finset.mem_range.mp hi
        have hbi := hb i hi'
        have hli := hl (i+1) hi'
        omega
      _ = _ := by simp
  have hlast := hl count (le_refl _)
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachineRepeat

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineCanonicalOutputLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Canonical output for finite Boolean machines

A raw machine may halt with retained metadata and a changed finite state.
This wrapper redirects its halt to a fixed list of actual tape drains, then
executes one state-reset instruction. The output tape is preserved and the
result is literally `haltList`. Its cost follows from the raw execution and
the maximum number of pushes in a raw statement.

The cleanup list is fixed with the program, not selected from the input.
It may contain repetitions and may be empty when output is the only tape.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCanonicalOutput

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype σ]

abbrev Label (Λ : Type) (chosen : List K) := Λ ⊕ (MachineDrainMany.Label chosen ⊕ Unit)

def cleanupLabel (chosen : List K) : MachineDrainMany.Label chosen → Label Λ chosen :=
  fun label => .inr (.inl label)

def resetLabel (chosen : List K) : Label Λ chosen := .inr (.inr ())

def cleanupEntry (chosen : List K) : Option (Label Λ chosen) :=
  MachineDrainMany.entry chosen (cleanupLabel chosen) (some (resetLabel chosen))

end UniqueGamesTheorem.Foundations.Complexity.MachineCanonicalOutput

namespace UniqueGamesTheorem.Foundations.Complexity.MachineTableRows

open Turing
open PCP.GraphTables

variable {K Λ σ : Type} [DecidableEq K]

/-- `fields 0`, `fields 1`, and `fields 2` are the tail, reverse index, and
encoded relation tapes. Every instruction reads or writes a single tape head. -/
def routine (fields : Fin 3 → K) (row output scratch : K)
    (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .relationRead => Reduction.MachineTransfer.loopAt (fields 2) scratch id false
      (labels .relationRead) (some (labels .relationRestore))
  | .relationRestore => MachineCopy.forkLoop scratch (fields 2) row false
      (labels .relationRestore) (some (labels .reverseRead))
  | .reverseRead => Reduction.MachineTransfer.loopAt (fields 1) scratch id false
      (labels .reverseRead) (some (labels .reverseRestore))
  | .reverseRestore => MachineCopy.forkLoop scratch (fields 1) row false
      (labels .reverseRestore) (some (labels .tailRead))
  | .tailRead => Reduction.MachineTransfer.loopAt (fields 0) scratch id false
      (labels .tailRead) (some (labels .tailRestore))
  | .tailRestore => MachineCopy.forkLoop scratch (fields 0) row false
      (labels .tailRestore) (some (labels .appendOld))
  | .appendOld => Reduction.MachineTransfer.loopAt output scratch id false
      (labels .appendOld) (some (labels .appendRow))
  | .appendRow => Reduction.MachineTransfer.loopAt row scratch id false
      (labels .appendRow) (some (labels .appendBack))
  | .appendBack => Reduction.MachineTransfer.loopAt scratch output id false
      (labels .appendBack) exit

end UniqueGamesTheorem.Foundations.Complexity.MachineTableRows

/-!
Actual finite control for the dummy self-loop rows of one padded vertex.
The port count is a fixed program parameter. Vertex and reverse-dart indices
remain on unary tapes, and each row advances the reverse index by one actual
push. The all-true relation is a fixed literal field, initialized once.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineDummyRows

open Turing
open PCP.GraphTables
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

/-- The actual 64-by-64 always-accepting relation. -/
def trueRelation : RelationTable := Vector.replicate 4096 true

def trueBits : List Bool := encodeWords (relationWords trueRelation)

theorem trueBits_length : trueBits.length = 8192 := by
  simp only [trueBits, encodeWords_length, relationWords, trueRelation,
    Vector.toList_replicate, List.map_replicate, List.sum_replicate_nat,
    List.length_replicate]
  rfl

def rowBits (v e : Nat) : List Bool := encodeWord v ++ encodeWord e ++ trueBits

/-- Ordered serialized rows with successive physically stored reverse indices. -/
def rowsBits (v e : Nat) : Nat → List Bool
  | 0 => []
  | count + 1 => rowBits v e ++ rowsBits v (e + 1) count

variable {σ : Type}

/-- No input-dependent natural number occurs in the finite program. -/
def program (d : Nat) : Label d → TM2.Stmt Alphabet (Label d) (σ × Option Bool)
  | .inl () => pushWord 2 trueBits.reverse
      (.load (fun state => (state.1, none)) (continueAt (entry d)))
  | .inr (p, .inl stage) => MachineTableRows.routine fields 3 4 5
      (rowLabel p) (some (bumpLabel p)) stage
  | .inr (p, .inr ()) => .push 1 (fun _ => true) (continueAt (afterPort p))

/-- The three unary row fields, two empty work tapes, and accumulated output. -/
def fieldTapes (v e : Nat) (output : List Bool) : Fin 6 → List Bool :=
  ![encodeWord v, encodeWord e, trueBits, [], output, []]

/-- Before initialization, the fixed-relation tape is empty. -/
def initialTapes (v e : Nat) (output : List Bool) : Fin 6 → List Bool :=
  Function.update (fieldTapes v e output) 2 []

/-- Exact sum of actual row-and-increment costs. This recurrence is matched
to the program by `suffixTrace`, rather than postulated as a runtime. -/
def steps (v e : Nat) (output : List Bool) : Nat → Nat
  | 0 => 0
  | count + 1 => (4 * (v + e + 8194) + 2 * output.length + 10) +
      steps v (e + 1) (output ++ rowBits v e) count

end UniqueGamesTheorem.Foundations.Complexity.MachineDummyRows

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_CleanupLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-stack cleanup. Each selected stack is drained using the
checked pop loop, followed by one transition resetting the finite state.
Repeated selections are allowed; they only reduce the cost upper bound. -/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Cleanup

open Turing
open Complexity
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

@[simp] theorem clearTapes_selected {n : Nat} (selected : Fin n → K)
    (base : K → List Bool) (i : Fin n) : clearTapes selected base (selected i) = [] := by
  rw [clearTapes_apply, ite_eq_left ⟨i, rfl⟩]

theorem clearTapes_unselected {n : Nat} (selected : Fin n → K)
    (base : K → List Bool) (k : K) (notSelected : ∀ i, selected i ≠ k) :
    clearTapes selected base k = base k := by
  rw [clearTapes_apply]
  simp [notSelected]

/-- Enumerating exactly the nonoutput stacks yields the standard final tape
family. Repeated selected stacks are permitted. -/
theorem clearTapes_outputOnly {n : Nat} (selected : Fin n → K)
    (output : K) (base : K → List Bool)
    (excludesOutput : ∀ i, selected i ≠ output)
    (coversOther : ∀ k, k ≠ output → ∃ i, selected i = k) :
    clearTapes selected base = fun k => if k = output then base output else [] := by
  funext k
  by_cases h : k = output
  · subst k
    simp [clearTapes_unselected selected base output excludesOutput]
  · rw [clearTapes_apply]
    simp [h, coversOther k h]

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Cleanup

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Lookup

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K]

theorem stepAux_skipBits (source : K) (bits : List Bool)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (base : K → List Bool) (suffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (skipBits source bits.length next) (ambient, register)
        (Function.update base source (encodeWords (bits.map bitWord) ++ suffix)) =
      TM2.stepAux next (ambient, none) (Function.update base source suffix) := by
  induction bits generalizing register with
  | nil => simp [skipBits, encodeWords, TM2.stepAux]
  | cons bit bits ih =>
    cases bit <;>
      simpa only [List.length_cons, skipBits, List.map_cons, bitWord, Bool.false_eq_true,
        ite_false, if_false, ite_true, if_true, encodeWords, encodeWord, List.replicate_zero,
        List.replicate_succ, List.nil_append, List.cons_append, List.singleton_append,
        TM2.stepAux, Function.update_self, List.head?_cons, List.tail_cons,
        Option.getD_some, Bool.cond_false, Bool.cond_true, Function.update_idem] using
          ih none

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Lookup

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_Emitter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual finite TM2 templates for affine unary fields and finite relation bits.
Commands write in forward bit order onto a stack, so their concatenated result
appears reversed in the accumulator. Every unbounded operand is read from an
isolated unary tape and restored by the checked preserving transducer.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Emitter

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ : Type} {h bound : Nat} [DecidableEq K]

theorem output_encodeWord (coefficient n : Nat) :
    Reduction.MachineTransducer.output transition (payload coefficient) () (encodeWord n) =
      List.replicate (coefficient * n) true := by
  induction n with
  | zero => simp [encodeWord, Reduction.MachineTransducer.output, payload]
  | succ n ih =>
    simp only [encodeWord, List.replicate_succ, List.cons_append,
      Reduction.MachineTransducer.output, payload, ite_true, if_true, transition]
    change List.replicate coefficient true ++
      Reduction.MachineTransducer.output transition (payload coefficient) () (encodeWord n) = _
    rw [ih, ← List.replicate_add]
    congr 1
    simp [Nat.mul_succ, Nat.add_comm]

/-- The finite relation table is encoded one actual Boolean branch at a time. -/
def bitCommands (bits : List (σ → Bool)) : List (Command h σ bound) := bits.map .bit

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Emitter

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_FinalBooleanVerifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.FinalBooleanVerifier

open Target

variable {V E : Type*} {n m : Nat}

@[simp] theorem bitsOfLabels_labelsOfBits (vertices : V ≃ Fin n)
    (assignment : Fin (n * 6) → Bool) : bitsOfLabels vertices (labelsOfBits vertices assignment) = assignment := by
  funext k
  simp only [bitsOfLabels, labelsOfBits, bitIndex, Equiv.apply_symm_apply, Prod.eta]

theorem all_satisfied_of_rejectionCount_zero [Fintype E] (G : ConstraintGraph V E Label)
    (labeling : V → Label) (zero : G.rejectionCount labeling = 0) :
    ∀ e, G.edgeSatisfied labeling e = true := by
  intro e
  cases h : G.edgeSatisfied labeling e with
  | true => rfl
  | false =>
    have member : e ∈ G.rejectedDarts labeling := (G.mem_rejectedDarts labeling e).mpr h
    have positive : 0 < G.rejectionCount labeling := Finset.card_pos.mpr ⟨e, member⟩
    omega

end UniqueGamesTheorem.Foundations.PCP.FinalBooleanVerifier

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_FinalCNFMachineLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual finite-machine phases for the final twelve-query verifier conversion.
The graph codec stores a relation bit as the unary natural 0 or 1. The reader
below consumes those variable-length codewords, rather than treating the row
as an already available raw Boolean block. Its finite register size is fixed
at 4096 for the final alphabet, independent of the graph input size.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine

open Turing
open PCP

namespace Program

open PCP.AlphabetTable

theorem headRoles_injective : Function.Injective headRoles := by
  decide

theorem source_ne_scratch (i : Fin 5) : source i ≠ Tape.scratch := by
  fin_cases i <;> decide

theorem source_ne_accumulator (i : Fin 5) : source i ≠ Tape.accumulator := by
  fin_cases i <;> decide

end Program

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFCleanup

open Turing MachineComposition
open FinalCNFMachine.Program (Tape )

section Redirect

variable {K Λ Λ' σ : Type} {Γ : K → Type} [DecidableEq K]

theorem stepAux_redirect (labels : Λ → Λ') (haltTarget : Option Λ')
    (stmt : TM2.Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (redirectStmt labels haltTarget stmt) state tapes =
      redirectCfg labels haltTarget (TM2.stepAux stmt state tapes) := by
  induction stmt generalizing state tapes with
  | push k f next ih => exact ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih => exact ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
      exact ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih => exact ih (f state) tapes
  | branch test yes no ihYes ihNo =>
      cases h : test state with
      | false => simpa only [redirectStmt, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
      | true => simpa only [redirectStmt, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto label => rfl
  | halt => cases haltTarget <;> rfl

end Redirect

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFCleanup

/-!
The concrete final-CNF machine's entry phase. It archives its complete input,
reads the two unary size fields, emits the exact formula header, and reaches
the row guard. The transition witness is assembled from actual program calls.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

open Turing
open PCP.AlphabetTable

def headerInputTapes (input : List Bool) : Tape → List Bool :=
  headerFrame input [] [] [] [] [] [] []

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineFixedDivMod
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod

open Turing
open Reduction.MachineSubstitution (pushWord stepAux_pushWord )

variable {K Λ σ : Type} [DecidableEq K]

theorem nextResidue_residue (d : Nat) (positive : 0 < d) (n : Nat) :
    nextResidue d positive (residue d positive n) = residue d positive (n + 1) := by
  apply Fin.ext
  change (n % d + 1) % d = (n + 1) % d
  simp only [Nat.add_mod, Nat.mod_mod]

/-- Each emitter is a fixed finite statement indexed by one of the `d` residues. -/
def emitter (d : Nat) (positive : 0 < d) (remainder : K) (exit : Option Λ)
    (r : Fin d) : TM2.Stmt (Alphabet (K := K)) Λ (State σ d) :=
  pushWord remainder (List.replicate r.val true)
    (.load (fun state => ((state.1.1, residue d positive 0), none))
      (Reduction.MachineTransfer.exitAt remainder exit))

end UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_ExpanderRowControlLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Raw natural-word serialization of actual expander rotation tables

The list keeps the stored row order `port + degree * vertex`; no header is
inserted. Lookup equalities and complete unary output lengths are data facts,
not machine execution certificates. Kernel-checked with Lean 4.33.1.
-/

namespace UniqueGamesTheorem.Foundations.PCP.ExpanderTableWords

open ExpanderTables
open UniqueGamesTheorem.Foundations.Complexity (encodeWords decodeWords)

variable {v d : ℕ}

theorem rotationWords_entry_lt (table : Table v d) (n : ℕ)
    (hn : n ∈ rotationWords table) : n < v * d := by
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hn
  exact a.isLt

end UniqueGamesTheorem.Foundations.PCP.ExpanderTableWords

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_FinalCNFLoopLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

protected abbrev Tape.enumList : List Tape := [.inputVertex, .table, .output, .emitScratch,
  .queryReverse, .queryIndex, .lookupOutput, .lookupWork, .lookupRestore, .quotientFirst,
  .quotientSecond, .remainderFirst, .remainderSecond]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_AmplificationIteration
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The finite iteration and size arithmetic for an amplification transformation.
The transformation itself must be supplied by the actual graph construction;
these theorems do not assert that such a transformation exists.  In particular,
the polynomial size estimate below is not a machine runtime certificate.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AmplificationIteration

theorem run_gap {X : Type*} (step : X → X) (gap : X → ℝ)
    (cap : ℝ) (hc : 0 ≤ cap)
    (amplifies : ∀ x, min (2 * gap x) cap ≤ gap (step x))
    (n : Nat) (x : X) :
    min (2 ^ n * gap x) cap ≤ gap (run step n x) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    have hm : min (2 * min (2 ^ n * gap x) cap) cap ≤
        min (2 * gap (run step n x)) cap :=
      min_le_min (mul_le_mul_of_nonneg_left ih (by norm_num)) le_rfl
    rw [min_double_min _ _ hc] at hm
    have h := hm.trans (amplifies (run step n x))
    simpa [run, pow_succ, mul_assoc, mul_left_comm, mul_comm] using h

theorem run_preserves {X : Type*} (step : X → X) (P : X → Prop)
    (preserves : ∀ x, P x → P (step x)) (n : Nat) (x : X) (hx : P x) :
    P (run step n x) := by
  induction n with
  | zero => exact hx
  | succ n ih => exact preserves _ ih

theorem rounds_large (n : Nat) : n < 2 ^ rounds n := by
  simpa [rounds, Nat.log2_eq_log_two] using
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n)

/-- An inverse-size initial gap reaches the fixed threshold after the concrete loop. -/
theorem run_reaches_cap {X : Type*} (step : X → X) (gap : X → ℝ)
    (cap : ℝ) (hc : 0 ≤ cap) (hc1 : cap ≤ 1)
    (amplifies : ∀ x, min (2 * gap x) cap ≤ gap (step x))
    (n : Nat) (x : X) (hg : 0 ≤ gap x) (hstart : 1 ≤ (n : ℝ) * gap x) :
    cap ≤ gap (run step (rounds n) x) := by
  have hp : (n : ℝ) ≤ (2 : ℝ) ^ rounds n := by
    exact_mod_cast (Nat.le_of_lt (rounds_large n))
  have hcap : cap ≤ (2 : ℝ) ^ rounds n * gap x :=
    hc1.trans (hstart.trans (mul_le_mul_of_nonneg_right hp hg))
  have h := run_gap step gap cap hc amplifies (rounds n) x
  rwa [min_eq_right hcap] at h

end UniqueGamesTheorem.Foundations.PCP.AmplificationIteration

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingTableSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Spectral certificates for the actual materialized preprocessing tables.
Exact rotation identities transport the checked semantic overlay and lazy
estimates to the stored tables. No spectral premise is imposed on the
original constraint table in the overlay theorem.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingTableSpectral

open PoweringWalks SpectralReturn

theorem portGraph_ext {V D : Type*} {G H : PortGraph V D}
    (h : ∀ x, G.rot x = H.rot x) : G = H := by
  have hr : G.rot = H.rot := Equiv.ext h
  cases G
  cases H
  cases hr
  rfl

end UniqueGamesTheorem.Foundations.PCP.PreprocessingTableSpectral

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PoweringPortReindexLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact transport of powering through a change of ports. The target's actual
address selector is pulled back, so no compatibility of enumeration orders or
consistency restriction on raw padded labels is needed. -/

noncomputable section
namespace UniqueGamesTheorem.Foundations.PCP.PoweringPortReindex
open PoweringWalks PoweringLabels PoweringReach PoweringTest
open SpectralReturn PoweringSoundness

variable {V D E A : Type*}

def addressEquiv (ports : D ≃ E) (t : Nat) : PortWords D t ≃ PortWords E t where
  toFun w := ⟨w.1, wordEquiv ports w.1.val w.2⟩
  invFun w := ⟨w.1, (wordEquiv ports w.1.val).symm w.2⟩
  left_inv w := by rcases w with ⟨n,p⟩; simp
  right_inv w := by rcases w with ⟨n,p⟩; simp

/-- Pull target raw labels back to old port coordinates; this is a bijection. -/
def labelEquiv (ports : D ≃ E) (t : Nat) : PaddedLabel E t A ≃ PaddedLabel D t A where
  toFun a := fun w => a (addressEquiv ports t w)
  invFun a := fun w => a ((addressEquiv ports t).symm w)
  left_inv a := by funext w; simp
  right_inv a := by funext w; simp

variable (G : PortGraph V D) (H : PortGraph V E) (ports : D ≃ E)
variable (rotation : ∀ v d, H.rot (v, ports d) =
  ((G.rot (v,d)).1, ports (G.rot (v,d)).2))

include rotation

variable (accepts : Edge V E → A → A → Bool)

def pullAccepts : Edge V D → A → A → Bool :=
  fun e => accepts (e.1, ports e.2)

end UniqueGamesTheorem.Foundations.PCP.PoweringPortReindex

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_VertexPadding
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.VertexPadding

open scoped BigOperators

variable {V D A : Type*}

theorem rejectionCount_eq_sum {U E : Type*} [Fintype E]
    (G : ConstraintGraph U E A) (labeling : U → A) :
    G.rejectionCount labeling = ∑ e, if G.edgeSatisfied labeling e = false then 1 else 0 := by
  simp [ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts]

/-- Exact counts for every padded labeling, without any condition on dummy labels. -/
theorem pad_rejectionCount [Fintype V] [Fintype D]
    (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst) (extra : ℕ)
    (labeling : V ⊕ Fin extra → A) :
    (pad G extra).rejectionCount labeling =
      G.rejectionCount (fun v => labeling (Sum.inl v)) := by
  classical
  simp only [rejectionCount_eq_sum, Fintype.sum_prod_type, Fintype.sum_sum_type]
  simp only [edgeSatisfied_inl G htail, edgeSatisfied_inr]
  simp

end UniqueGamesTheorem.Foundations.PCP.VertexPadding

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_Preprocessing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.Preprocessing

open PoweringWalks SpectralReturn

variable {V E A : Type*} [Fintype V] [Fintype E] [Fintype A]
  [DecidableEq V] [DecidableEq E] [DecidableEq A] [Nonempty E] [Nonempty A]

theorem degree_positive : 0 < degree := by
  unfold degree
  omega

theorem sizeFactor_positive : 0 < sizeFactor := by
  have hg : 0 < ExpanderFamily.growth :=
    Nat.zero_lt_one.trans ExpanderFamily.growth_gt_one
  exact Nat.mul_pos (Nat.pow_pos hg) degree_positive

end UniqueGamesTheorem.Foundations.PCP.Preprocessing

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_FinalConstantsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Relations.repeatedConsistentDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.FinalConstants

def windowSize : Nat := 2 * windowHalf + 1

noncomputable def gain : ℝ := (windowSize : ℝ) / denominator

theorem denominator_positive : 0 < denominator := by
  norm_num [denominator, alphabet, compositionLoss]

theorem windowHalf_positive : 0 < windowHalf :=
  Nat.mul_pos denominator_positive Preprocessing.sizeFactor_positive

theorem gain_large : 2 * (Preprocessing.sizeFactor : ℝ) ≤ gain := by
  have hd : (0 : ℝ) < denominator := by exact_mod_cast denominator_positive
  apply (le_div_iff₀ hd).2
  simp only [windowSize, windowHalf, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat]
  nlinarith

end UniqueGamesTheorem.Foundations.PCP.FinalConstants

end

section

/-!
The actual fixed-parameter graph transformation in one PCP amplification round.
It preprocesses the input graph, checks all edges of each bounded walk using
local endpoint labels, and applies the checked constant-query alphabet reduction.
The bounded address list is explicit fixed data shared by every input graph.
-/

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.AmplificationRound

abbrev Label := QueryIncidence.Label 6

end UniqueGamesTheorem.Foundations.PCP.AmplificationRound

end

end

section

/-!
# The fixed constants in the actual powering estimate

The six-bit alphabet has 64 letters. The middle window, endpoint length,
spectral parameter and composition loss in the checked powering theorem give
exactly the constants used in the final amplification round. Large natural
constants remain symbolic in these calculations.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringFinalConstants

/-- The actual six-bit alphabet gives the endpoint length fixed for the round. -/
theorem center_eq :
    PoweringSoundness.center (Fintype.card Alphabet) FinalConstants.windowHalf =
      FinalConstants.endpointLength := by
  rw [card_alphabet]
  rfl

/-- Dividing the actual powering coefficient by the composition loss gives
the round coefficient exactly. The large window parameter is not evaluated. -/
theorem gain_eq :
    PoweringSoundness.gain 64 FinalConstants.windowHalf (31 / 32) / 12288 =
      FinalConstants.gain := by
  change
    (1 / (2 * (FinalConstants.alphabet : ℝ))) ^ 4 *
        (FinalConstants.windowSize : ℝ) /
        ((1 + 2 / (1 - (31 / 32 : ℝ))) + 1) /
        (FinalConstants.compositionLoss : ℝ) =
      (FinalConstants.windowSize : ℝ) / (FinalConstants.denominator : ℝ)
  rw [spectral_denominator_eq]
  have hden : (FinalConstants.denominator : ℝ) =
      16 * (FinalConstants.alphabet : ℝ) ^ 4 * 66 *
        (FinalConstants.compositionLoss : ℝ) := by
    simp only [FinalConstants.denominator, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [hden]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem gain_card_eq :
    PoweringSoundness.gain (Fintype.card Alphabet) FinalConstants.windowHalf (31 / 32) /
        12288 = FinalConstants.gain := by
  rw [card_alphabet]
  exact gain_eq

end UniqueGamesTheorem.Foundations.PCP.PoweringFinalConstants

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingPaddingOffsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The executable dummy numbering is the sum of earlier cloud sizes plus
the local dummy index. This connects the actual list search in vertexOrder
with unary prefix-sum routines, without changing the chosen enumeration. -/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingOffsets

open PreprocessingRegularTables
open scoped BigOperators

theorem offset_all {n : Nat} (padding : Fin n → Nat) :
    offset padding n = ∑ v, padding v := by
  have ht : (List.finRange n).take n = List.finRange n := by simp
  unfold offset
  rw [ht, ← sigma_length padding (List.finRange n)]
  exact paddingList_length padding

end UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingOffsets

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingRegularSoundness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Soundness of the executable regularization tables

The fixed input base table is required only to have its proved spectral
certificate. Every positive cloud uses the actual recursively generated table
at its computed size. Its spectral certificate gives the precise cut bound
used by majority rounding. Empty clouds are handled by their zero cardinality.
Thus neither expansion nor the desired count comparison is an input premise.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularSoundness

open PoweringWalks DegreeReplacement SpectralReturn PreprocessingRegularTables

theorem internalDegree_ge_eight : 8 ≤ internalDegree := by
  simpa only [ExpanderFamily.card_port, internalDegree, pow_two] using
    ExpanderFamily.port_degree_ge_eight

theorem baseDegree_ne_zero : Expanders.baseDegree ≠ 0 := by
  intro h
  have hdegree := internalDegree_ge_eight
  simp only [internalDegree, h, Nat.zero_mul] at hdegree
  omega

end UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularSoundness

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingTablesLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Concrete preprocessing table algorithm

Given one fixed expander base table, this function computes regularized
cloud rows, pads the whole vertex set, overlays a stored family table, and
adds the half-lazy rows. It is total even on zero-dart input tables. The
bounds below concern actual output data; an actual TM2 execution certificate
is a separate theorem and is not inferred from these size bounds.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingTables

open PreprocessingRegularTables

theorem degree_eq : degree = Preprocessing.degree := by
  unfold degree internalDegree Preprocessing.degree
  rw [pow_two]
  omega

end UniqueGamesTheorem.Foundations.PCP.PreprocessingTables

end

section

/-! Bounds on actual metadata, stored rotor words, and emitted prefixes. These
are size estimates used inside separately proved machine executions. -/
namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingMachineBounds
open PreprocessingRegularTables PreprocessingCloudIndex
open UniqueGamesTheorem.Foundations.Complexity
open scoped BigOperators

theorem offset_le_sum {n : Nat} (p : Fin n → Nat) (k : Nat) :
    PreprocessingPaddingOffsets.offset p k ≤ ∑ v, p v := by
  have hfull : (List.finRange n).take n = List.finRange n := by simp
  have hsplit : PreprocessingPaddingOffsets.offset p k +
      (((List.finRange n).drop k).map p).sum =
      PreprocessingPaddingOffsets.offset p n := by
    simp only [PreprocessingPaddingOffsets.offset, hfull]
    rw [← List.sum_append, ← List.map_append, List.take_append_drop]
  rw [PreprocessingPaddingOffsets.offset_all] at hsplit
  omega

noncomputable def regularPolynomial : Polynomial Nat :=
  tablePolynomial ExpanderFamily.growth (ExpanderFamily.growth * (internalDegree + 1))

noncomputable def rotorPolynomial (q : Nat) : Polynomial Nat :=
  (Polynomial.C (ExpanderFamily.growth * q) * Polynomial.X) *
    (Polynomial.C (ExpanderFamily.growth * q) * Polynomial.X + 1)

end UniqueGamesTheorem.Foundations.PCP.PreprocessingMachineBounds

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachinePaddingRowsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddingRows

open Turing MachineComposition

abbrev Alphabet : Tape → Type := MachineEmbedding.Alphabet
  (fun _ : Fin 6 => Bool) (fun _ : Unit => Bool)

def extra (d : Nat) (hd : 0 < d) : Control → TM2.Stmt Alphabet (Label d) State
  | .initialize_ => Reduction.MachineSubstitution.pushWord (.inl 2)
      MachineDummyRows.trueBits.reverse
      (.load (fun _ => (((), none), ())) (.goto (fun _ => .inr .guard)))
  | .guard => .pop (.inr ()) (fun _ bit => (((), bit), ()))
      (.branch (fun s => s.1.2.getD false)
        (.load (fun _ => (((), none), ())) (.goto (fun _ => bodyEntry d hd)))
        (.push (.inr ()) (fun _ => false)
          (.load (fun _ => (((), none), ())) .halt)))
  | .bump => .push (.inl 0) (fun _ => true) (.goto (fun _ => .inr .guard))

def tapes (v e fuel : Nat) (output : List Bool) : ∀ k, List (Alphabet k) :=
  MachineEmbedding.tapes (MachineDummyRows.fieldTapes v e output)
    (fun _ : Unit => encodeWord fuel)

def cfg (d : Nat) (label : Option (Label d)) (v e fuel : Nat)
    (output : List Bool) : TM2.Cfg Alphabet (Label d) State :=
  ⟨label, (((), none), ()), tapes v e fuel output⟩

def paddingBits (d v e : Nat) : Nat → List Bool
  | 0 => []
  | count + 1 => MachineDummyRows.rowsBits v e d ++ paddingBits d (v + 1) (e + d) count

def steps (d v e : Nat) (output : List Bool) : Nat → Nat
  | 0 => 1
  | count + 1 => (MachineDummyRows.steps v e output d + 2) +
      steps d (v + 1) (e + d) (output ++ MachineDummyRows.rowsBits v e d) count

def initialTapes (v e fuel : Nat) (output : List Bool) : ∀ k, List (Alphabet k) :=
  Function.update (tapes v e fuel output) (.inl 2) []

end UniqueGamesTheorem.Foundations.Complexity.MachinePaddingRows

/-! Polynomial bounds for the actual outer padding-loop recurrence. No
execution or cost premise is introduced: the recurrence is the one matched
to the concrete machine by `MachinePaddingRows.loopTrace`. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddingBounds

/-- Exact variable-size input: two unary fields, unary fuel, and old output. -/
def inputSize (v e count : Nat) (output : List Bool) : Nat :=
  (encodeWord v).length + (encodeWord e).length + (encodeWord count).length + output.length

theorem rowBound_le_cap (d v e count : Nat) (output : List Bool) :
    rowBound d v e count ≤ rowCap d (inputSize v e count output) := by
  have hbase : v + e + count ≤ inputSize v e count output := by
    simp only [inputSize, encodeWord_length]
    omega
  have hcount : count ≤ inputSize v e count output := by
    simp only [inputSize, encodeWord_length]
    omega
  have hmul := Nat.mul_le_mul_right d (Nat.succ_le_succ hcount)
  have h := Nat.add_le_add_right (Nat.add_le_add hbase hmul) 8194
  simpa only [rowBound, rowCap, Nat.succ_eq_add_one, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using h

end UniqueGamesTheorem.Foundations.Complexity.MachinePaddingBounds

/-! Polynomial-time certificate for the actual varying-length padding loop,
including its one-time relation initialization. The input vertex, reverse
index, fuel, and accumulated output are all measured as physically stored
bits. This is a reusable stage of the graph-table transformation. -/

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingPaddingWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Exact serialization of whole-vertex padding

The original dart rows remain in their original order, with every old tail,
reverse index, and relation bit unchanged. The suffix is exactly the bit stream
emitted by the checked dummy-vertex machine, starting at vertex `n` and dart
`n*d`. This is an equality for the actual table codec, with no runtime premise.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingWords

open Complexity PortTables

variable {n m d : Nat}

theorem encodeWords_flatMap {α : Type*} (xs : List α) (words : α → List Nat) :
    encodeWords (xs.flatMap words) = xs.flatMap (fun x => encodeWords (words x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

/-- Mixed-radix row order is vertex-major, then increasing port order. -/
theorem flatten_ofFn_rowIndex {α : Type*} (f : Fin (n * d) → List α) :
    (List.ofFn f).flatten =
      (List.ofFn (fun v : Fin n =>
        (List.ofFn (fun p : Fin d => f (rowIndex n d (v, p)))).flatten)).flatten := by
  rw [List.ofFn_mul, List.flatten_flatten, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext v
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext p
  apply congrArg f
  apply Fin.ext
  simp only [rowIndex_val, Nat.mul_comm, Nat.add_comm]

/-- The row emitter's recursive stream enumerates successive reverse indices. -/
theorem dummy_rowsBits_eq_ofFn (v e count : Nat) :
    MachineDummyRows.rowsBits v e count =
      (List.ofFn (fun p : Fin count => MachineDummyRows.rowBits v (e + p.val))).flatten := by
  induction count generalizing e with
  | zero => rfl
  | succ count ih =>
    rw [MachineDummyRows.rowsBits, List.ofFn_succ, List.flatten_cons, ih]
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
    congr 1
    apply congrArg (fun f : Fin count → List Bool => (List.ofFn f).flatten)
    funext p
    congr 1
    omega

/-- The vertex emitter's recursive stream enumerates consecutive vertex blocks. -/
theorem paddingBits_eq_ofFn (d v e count : Nat) :
    MachinePaddingRows.paddingBits d v e count =
      (List.ofFn (fun k : Fin count =>
        MachineDummyRows.rowsBits (v + k.val) (e + k.val * d) d)).flatten := by
  induction count generalizing v e with
  | zero => rfl
  | succ count ih =>
    rw [MachinePaddingRows.paddingBits, List.ofFn_succ, List.flatten_cons, ih]
    simp only [Fin.val_zero, Nat.zero_mul, Nat.add_zero, Fin.val_succ, Nat.add_mul, Nat.one_mul]
    congr 1
    apply congrArg (fun f : Fin count → List Bool => (List.ofFn f).flatten)
    funext k
    congr 1 <;> omega

end UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingWords

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_RawInitialTablesLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit structural numberings of the raw 3SAT incidence graph. Unused
declared variable names are retained; their unary input header pays for them.
The graph has one dummy vertex and one tautological loop, even for an empty
formula. No input-dependent choice of a finite enumeration is made. -/

/-! Polynomial arithmetic for the actual initial-machine phase counts. The
separate execution theorem must connect these counts to the concrete program. -/

/-! Explicit finite predicates and numeric row words of the initial incidence table.
Every relation retains all 4096 entries, including repetitions. -/

/-! The concrete numbered amplification round, with one fixed base expander.
Every intermediate is an actual stored table, with explicit finite coordinates.
The running-time certificate is a separate theorem about these same functions. -/

namespace UniqueGamesTheorem.Foundations.PCP.RoundTables

theorem walkParameter_eq : walkParameter = 2 * FinalConstants.endpointLength :=
  fixedWalkParameter.property

end UniqueGamesTheorem.Foundations.PCP.RoundTables

/-! Gap amplification for the actual numbered table round. The fixed base
expander is the only supplied construction datum with a spectral certificate. -/

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingRegularLoopWordsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineModel

open Turing Complexity Hastad

abbrev Alphabet (_ : Tape) := Bool

def copySource : CopyPhase → Tape
  | .tailVariables _ | .dummyVariables => .variables
  | .variableName slot => .field (nameField slot)
  | _ => .index

def finalTape (slot : Fin 3) : Tape :=
  if slot.val = 0 then .variables else if slot.val = 1 then .counter else .index

def drain (tape : Tape) (again next : Label) : TM2.Stmt Alphabet Label State :=
  MachineDrain.drain tape again (some next)

def headerTape (slot : Fin 2) : Tape := if slot.val = 0 then .variables else .counter

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineModel

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_RawInitialMachinePhases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual execution of the raw initial graph program's reusable phases. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachinePhases

open Turing Complexity RawInitialMachineModel

theorem copySource_ne_scratch (phase : CopyPhase) : copySource phase ≠ Tape.scratch := by
  cases phase <;> simp [copySource]

theorem copySource_ne_reversed (phase : CopyPhase) : copySource phase ≠ Tape.reversed := by
  cases phase <;> simp [copySource]

theorem bitWord_head (b : Bool) :
    (encodeWord (if b then 1 else 0)).head? = some b := by
  cases b <;> rfl

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachinePhases

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_RawInitialMachineStart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
Actual execution of the raw initial graph machine from its standard input
configuration to the first clause-loop guard. The unread clause bits are
preserved verbatim, and all tape contents at the boundary are explicit.
-/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineStart

open Turing Complexity Hastad RawInitialMachineModel

def inputTapes (bits : List Bool) : Tape → List Bool
  | .input => bits
  | _ => []

def firstTapes (n m : ℕ) (clauseBits : List Bool) : Tape → List Bool
  | .input => encodeWord m ++ clauseBits
  | .variables => encodeWord n
  | _ => []

def counterTapes (n m : ℕ) (clauseBits : List Bool) : Tape → List Bool
  | .input => clauseBits
  | .variables => encodeWord n
  | .counter => encodeWord m
  | _ => []

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineStart

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_RawInitialMachineLoopData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The exact input and output streams at successive clause-loop iterations.
These tape invariants use the actual word codecs and clause occurrence order. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData

open Target Complexity RawInitialMachineModel

def loopTapes (n i remaining : Nat) (input reversed : List Bool) : Tape → List Bool
  | .input => input
  | .variables => encodeWord n
  | .counter => encodeWord remaining
  | .index => encodeWord i
  | .reversed => reversed
  | _ => []

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_RawInitialMachineRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! The six incidence rows are emitted by the actual finite program, with
their exact order, full relation lists, transition count, and tape frame. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineRows

open Turing Complexity RawInitialMachineModel RawInitialMachinePhases


def outputTapes (base : Tape → List Bool) (bits : List Bool) : Tape → List Bool :=
  Function.update base .reversed (bits ++ base .reversed)

@[simp] theorem outputTapes_reversed (base : Tape → List Bool) (bits : List Bool) :
    outputTapes base bits .reversed = bits ++ base .reversed := by simp [outputTapes]

@[simp] theorem outputTapes_twice (base : Tape → List Bool) (first second : List Bool) :
    outputTapes (outputTapes base first) second = outputTapes base (second ++ first) := by
  funext tape
  by_cases h : tape = .reversed
  · subst tape; simp [List.append_assoc]
  · simp [outputTapes, h]

theorem reverse_encodeWord_add (a b : ℕ) :
    (encodeWord b).reverse ++ List.replicate a true = (encodeWord (a + b)).reverse := by
  simp only [encodeWord, List.reverse_append, List.reverse_replicate, List.reverse_singleton]
  rw [Nat.add_comm a b, List.replicate_add]
  simp only [List.append_assoc]

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineRows

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_RawInitialMachineFinish
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineRows.outputTapes_reversed _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineRows.outputTapes_twice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact execution of the dummy-row and final cleanup/reversal phases. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineFinish

open Turing Complexity RawInitialMachineModel RawInitialMachinePhases

def tapes (varsWord counter index reversed output : List Bool) : Tape → List Bool
  | .variables => varsWord
  | .counter => counter
  | .index => index
  | .reversed => reversed
  | .output => output
  | _ => []

def finishTapes (n m : Nat) (rev : List Bool) : Tape → List Bool :=
  tapes (encodeWord n) [false] (encodeWord m) rev []

theorem update_reversed (varsWord counter index rev out word : List Bool) :
    Function.update (tapes varsWord counter index rev out) .reversed word =
      tapes varsWord counter index word out := by
  funext k
  cases k <;> simp [tapes]

theorem update_finish (n m : Nat) (rev word : List Bool) :
    Function.update (finishTapes n m rev) .reversed word = finishTapes n m word :=
  update_reversed _ _ _ _ _ _

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineFinish

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingLazyWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact codec expansion of the executable lazy graph table. Each vertex
contributes its `d` always-accepting selfloops, followed by its `d` stored
constraints with the reverse field changed by the displayed div/mod map. -/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingLazyWords

open PortTables GraphTables PreprocessingOverlayTables
open UniqueGamesTheorem.Foundations.Complexity

variable {n d : Nat}

/-- Finite mixed-radix indexing agrees with the actual row-vector order. -/
theorem ofFn_rowIndex {α : Type*} (f : Fin (n * d) → α) :
    List.ofFn f = (List.ofFn fun v : Fin n =>
      List.ofFn fun p : Fin d => f (rowIndex n d (v, p))).flatten := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  congr 1
  funext v
  congr 1
  funext p
  apply congrArg f
  apply Fin.ext
  simp only [rowIndex_val]
  ac_rfl

end UniqueGamesTheorem.Foundations.PCP.PreprocessingLazyWords

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineLazyCodec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact dummy-block codec used by the complete lazy-table machine. -/
namespace UniqueGamesTheorem.Foundations.Complexity.MachineLazyCodec
open PCP.GraphTables PCP.PreprocessingLazyWords

theorem rowsBits_ofFn (v e count : Nat) :
    MachineDummyRows.rowsBits v e count =
      (List.ofFn fun p : Fin count => MachineDummyRows.rowBits v (e + p.val)).flatten := by
  induction count generalizing e with
  | zero => rfl
  | succ count ih =>
    rw [MachineDummyRows.rowsBits, List.ofFn_succ, List.flatten_cons]
    simp only [Fin.val_zero, Nat.add_zero]
    apply congrArg (MachineDummyRows.rowBits v e ++ ·)
    rw [ih]
    apply congrArg List.flatten
    congr 1
    funext p
    simp only [Fin.val_succ]
    congr 1
    omega

theorem encodeWords_flatMap {α : Type*} (items : List α) (words : α → List Nat) :
    encodeWords (items.flatMap words) = items.flatMap (fun x => encodeWords (words x)) := by
  induction items with
  | nil => rfl
  | cons item items ih => simp only [List.flatMap_cons, encodeWords_append, ih]

end UniqueGamesTheorem.Foundations.Complexity.MachineLazyCodec

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachinePortReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePortReindex

open Turing MachineComposition
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ A : Type} [DecidableEq K]

abbrev State (A : Type) (d : Nat) := MachineFixedDivMod.State A d

def clean (d : Nat) (positive : 0 < d) (ambient : A) : State A d :=
  ((ambient, MachineFixedDivMod.residue d positive 0), none)

def exitAt {d : Nat} (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A d) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

/-- A residue-indexed literal instruction; its length is bounded by `d+b`. -/
def emit (d : Nat) (positive : 0 < d) (output : K) (b : Nat)
    (r : Fin d) (next : Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A d) :=
  pushWord output (List.replicate (r.val + b) true)
    (.load (fun s => clean d positive s.1.1) (.goto fun _ => next))

def frame (tape : Fin 5 → K) (base : K → List Bool)
    (work quotient output : List Bool) : K → List Bool :=
  MachineCopy.forkTapes (tape 2) (tape 3) (tape 4) base work quotient output

end UniqueGamesTheorem.Foundations.Complexity.MachinePortReindex

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineLazyRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineLazyRows

open Turing MachineComposition PCP.GraphTables
open PCP.PreprocessingLazyWords (reverseMap )

variable {K Λ A : Type} [DecidableEq K]

abbrev State (A : Type) (d : Nat) := MachinePortReindex.State A d

end UniqueGamesTheorem.Foundations.Complexity.MachineLazyRows

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineExpanderRowDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The two actual division phases of the expander-row program. Static state
conjugation connects the fixed-divisor machine to the common emitter state.
Only the concrete statement placement equations are premises; no phase trace
or whole-row execution is assumed. Each phase has exactly `n + 2` transitions.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

theorem controlStatement_inverse {K Λ σ τ : Type} {Γ : K → Type}
    (e : σ ≃ τ) (q : TM2.Stmt Γ Λ σ) :
    MachineControl.statement id e.symm (MachineControl.statement id e q) = q := by
  induction q <;>
    simp_all only [MachineControl.statement, Equiv.apply_symm_apply,
      Equiv.symm_apply_apply, id_eq]

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineExpanderTableProgramLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

protected abbrev ExtraTape.enumList : List ExtraTape := [.remainingLevel, .currentSize,
  .unaryScratch, .tableReverse]

protected theorem ExtraTape.enumList_nodup : ExtraTape.enumList.Nodup := by decide

instance instFintypeExtraTape : Fintype ExtraTape where
  elems := ⟨ExtraTape.enumList, ExtraTape.enumList_nodup⟩
  complete x := by cases x <;> decide

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineExpanderFamilyTapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Static, pointwise Boolean presentation of the actual family tape alphabet.
Every conversion below is an identity on symbols and has no machine runtime. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

open Turing

theorem transport_tapes_apply {K : Type} {Γ Δ : K → Type}
    (h : Γ = Δ) (base : (k : K) → List (Γ k)) (k : K) :
    MachineAlphabetTransport.tapes h base k =
      Eq.mp (congrArg (fun alphabet => List (alphabet k)) h) (base k) := by
  cases h
  rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineExpanderFamilyTransferLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
# Actual family-table installation and counter cleanup

Checked physical drain and transfer loops are placed in the family program
through its finite register equivalence. Alphabet equality transports their
actual traces back to the dependent alphabet of the full family machine.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

section Composition

open MachineComposition

theorem controlStatementInverse {K Λ σ τ : Type} {Γ : K → Type}
    (states : σ ≃ τ) (q : TM2.Stmt Γ Λ σ) :
    MachineControl.statement id states.symm (MachineControl.statement id states q) = q := by
  induction q <;>
    simp_all only [MachineControl.statement, Equiv.apply_symm_apply,
      Equiv.symm_apply_apply, id_eq]

/-- Static state-coordinate transport preserves every actual transition. -/
theorem controlTrace {K Λ σ τ : Type} {Γ : K → Type} [DecidableEq K]
    (states : σ ≃ τ) (target : Λ → TM2.Stmt Γ Λ τ)
    (n : Nat) (start finish : TM2.Cfg Γ Λ σ)
    (run : (advance (TM2.step (MachineControl.program (Equiv.refl Λ) states.symm target)))^[n]
      (some start) = some finish) :
    (advance (TM2.step target))^[n]
      (some (MachineControl.configuration id states start)) =
      some (MachineControl.configuration id states finish) := by
  let source := MachineControl.program (Equiv.refl Λ) states.symm target
  have roundtrip : MachineControl.program (Equiv.refl Λ) states source = target := by
    funext label
    change MachineControl.statement id states
      (MachineControl.statement id states.symm (target label)) = target label
    exact controlStatementInverse states.symm _
  have simulation : ∀ a b, TM2.step source a = some b →
      TM2.step target (MachineControl.configuration id states a) =
        some (MachineControl.configuration id states b) := by
    intro a b hab
    have h := MachineControl.step_simulation (Equiv.refl Λ) states source a
    rw [roundtrip, hab] at h
    exact h
  exact liftSuccessfulTrace (TM2.step source) (TM2.step target)
    (MachineControl.configuration id states) simulation n start finish run

theorem controlTransferTrace {K Λ σ τ : Type} [DecidableEq K]
    (states : (σ × Option Bool) ≃ τ) (source destination : K)
    (distinct : source ≠ destination) (again : Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ τ)
    (code : target again = MachineControl.statement id states
      (Reduction.MachineTransfer.loopAt source destination id false again exit))
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step target))^[(base source).length + 1]
      (some ⟨some again, states (ambient, register), base⟩) =
      some ⟨exit, states (ambient, none),
        Reduction.MachineTransfer.tapesAt source destination base []
          ((base source).reverse ++ base destination)⟩ := by
  let raw := MachineControl.program (Equiv.refl Λ) states.symm target
  have atRaw : raw again = Reduction.MachineTransfer.loopAt source destination id false again exit := by
    change MachineControl.statement id states.symm (target again) = _
    rw [code]
    exact controlStatementInverse states _
  have run := Reduction.MachineTransfer.transferAt_fromTapes source destination distinct id false
    again exit raw atRaw base ambient register
  unfold Reduction.MachineTransfer.nextAt at run
  simpa only [MachineControl.configuration, Option.map_some, id_eq, Option.map_id,
    List.map_id] using controlTrace states target ((base source).length + 1) _ _ run

end Composition

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily


/-!
# Concrete boundary steps of the expander-table machine

Every execution theorem below reduces the actual common program statement.
States and dependent tape frames are arbitrary; only the relevant unary word
or finite-position branch is specified. No phase execution is a premise.
-/

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineExpanderRowCleanup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {K Λ ρ : Type} [DecidableEq K]

def cleanupSteps (ports : Tape → K) (base : K → List Bool) : Nat :=
  ((base (ports .queryIndex)).length + 1) +
  ((base (ports .lookupOutput)).length + 1) +
  ((base (ports .quotientFirst)).length + 1) +
  ((base (ports .quotientSecond)).length + 1) +
  ((base (ports .remainderFirst)).length + 1) +
  ((base (ports .remainderSecond)).length + 1)

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineExpanderFamilyBoundsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounds for materializing the actual expander family

The costs use the encoded old and new rotation tables, and the already checked
table-machine polynomial. The finite sum follows the actual recursive table
family. These arithmetic lemmas introduce no execution assumptions and make no
claim that the output is polynomial in an isolated binary level parameter.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamilyBounds

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

theorem vertexCount_monotone {q : Nat} (positive : 0 < q) :
    Monotone (vertexCount q) := by
  intro m n hmn
  rw [vertexCount_eq, vertexCount_eq]
  exact Nat.pow_le_pow_right (Nat.mul_pos positive positive) hmn

theorem level_le_vertexCount {q : Nat} (growth : 1 < q * q) (level : Nat) :
    level ≤ vertexCount q level := by
  have positive : 0 < q := by nlinarith
  induction level with
  | zero => exact Nat.zero_le _
  | succ level ih =>
    have hpos := vertexCount_positive positive level
    have hmul := Nat.mul_le_mul_left (vertexCount q level)
      (show 2 ≤ q * q by omega)
    change level + 1 ≤ vertexCount q level * (q * q)
    nlinarith

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamilyBounds

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineOverlayRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineOverlayRows

open Turing MachineComposition
open PCP.GraphTables PCP.PreprocessingOverlayWords
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ A : Type} [DecidableEq K]

abbrev State (A : Type) (e : Nat) := MachinePortReindex.State A e

/-! The fixed-degree vertex loop has one finite label block per port, plus
one terminal boundary. The stored row values do not occur in its program. -/

end UniqueGamesTheorem.Foundations.Complexity.MachineOverlayRows

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineVertexPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Vertex padding from the original serialized port graph

Header counters, the geometric padding count, and the initial row buffer
are generated by physical tape operations before the checked row emitter.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineVertexPadding

open Turing MachineComposition
open UniqueGamesTheorem.Foundations.PCP
open MachineCloudPadding

theorem rowAlphabet_eq : MachinePaddingRows.Alphabet = (fun _ : MachinePaddingRows.Tape => Bool) := by
  funext k; cases k <;> rfl

def rowBoolTapes (base : (k : MachinePaddingRows.Tape) → List (MachinePaddingRows.Alphabet k)) :
    MachinePaddingRows.Tape → List Bool
  | .inl k => base (.inl k)
  | .inr k => base (.inr k)

theorem transport_tapes_apply {K : Type} {Γ Δ : K → Type}
    (h : Γ = Δ) (base : (k : K) → List (Γ k)) (k : K) :
    MachineAlphabetTransport.tapes h base k =
      Eq.mp (congrArg (fun alphabet => List (alphabet k)) h) (base k) := by
  cases h
  rfl

theorem rowCastTapes (base : (k : MachinePaddingRows.Tape) → List (MachinePaddingRows.Alphabet k)) :
    MachineAlphabetTransport.tapes rowAlphabet_eq base = rowBoolTapes base := by
  funext k
  rw [transport_tapes_apply]
  cases k <;> rfl

theorem frameTrace {K Λ σ τ : Type} {Γ : K → Type} [DecidableEq K]
    (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ) (n : Nat)
    (a b : TM2.Cfg Γ Λ σ) (run : (advance (TM2.step source))^[n] (some a) = some b) :
    (advance (TM2.step (MachineStateFrame.frameProgram source)))^[n]
      (some (MachineStateFrame.frameConfiguration ambient a)) =
      some (MachineStateFrame.frameConfiguration ambient b) := by
  have h := MachineStateFrame.frame_iterate source ambient n (some a)
  simpa only [Option.map_some, run] using h

def intermediateCoefficient (d : Nat) : Nat := (d + 2) * ExpanderFamily.growth + 8

noncomputable def intermediatePolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.C (intermediateCoefficient d) * (Polynomial.X + 1)

noncomputable def otherPolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.C (ExpanderFamily.growth + 8) * (Polynomial.X + 1) ^ 2 +
    Polynomial.C ((d + 8) * ExpanderFamily.growth + 24) * (Polynomial.X + 1) + 8222

noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  otherPolynomial d + (MachinePaddingCertificate.timePolynomial d).comp (intermediatePolynomial d)

end UniqueGamesTheorem.Foundations.Complexity.MachineVertexPadding

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachinePaddedOverlay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Physical composition of vertex padding, expander generation, and overlay

The level produced by vertex padding is the family machine's actual input
stack. The two resulting archives are the overlay machine's actual archive
stacks. Static tape placement and finite-state framing preserve the original
input; no copying or recomputation is hidden in a phase boundary.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlay

open Turing MachineComposition MachineCloudPadding
open PCP

abbrev baseDegree := Expanders.baseDegree
abbrev overlayDegree := PreprocessingRegularTables.internalDegree

variable {d : Nat}

/-- The actual padded vertex count is linear in the original encoded size. -/
noncomputable def sizePolynomial : Polynomial Nat :=
  Polynomial.C ExpanderFamily.growth * (Polynomial.X + 1)

/-- Full unary lengths of both physical archives, including all graph
predicate entries, all delimiters, and all expander reverse addresses. -/
noncomputable def archivePolynomial (d : Nat) : Polynomial Nat :=
  let s := sizePolynomial
  s + s * Polynomial.C d + 2 +
    (s * Polynomial.C d) * (s + s * Polynomial.C d + 8192) +
    (s * Polynomial.C overlayDegree) * (s * Polynomial.C overlayDegree + 1)

end UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlay

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineCloudRankLemmas
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCloudPadding.countMemory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCloudRank

open Turing MachineComposition MachineCloudCount

variable {σ : Type}

@[simp] theorem update_memory_spare (a b c d e f x : List Bool) :
    Function.update (memory a b c d e f) .spare x = memory a b c d e x := by
  funext k
  cases k <;> rfl

def rankProgram : RankLabel → TM2.Stmt Alphabet RankLabel (State σ)
  | .queryFirst => Reduction.MachineTransfer.loopAt
      .target .scratch id false .queryFirst (some .querySecond)
  | .querySecond => MachineCopy.forkLoop
      .scratch .target .spare false .querySecond (some .querySkip)
  | .querySkip => MachineLookup.discard .spare .querySkip .tableFirst
  | .tableFirst => Reduction.MachineTransfer.loopAt
      .original .scratch id false .tableFirst (some .tableSecond)
  | .tableSecond => MachineCopy.forkLoop
      .scratch .original .work false .tableSecond (some .headerFirst)
  | .headerFirst => MachineLookup.discard .work .headerFirst .headerSecond
  | .headerSecond => MachineLookup.discard .work .headerSecond .row
  | .row => MachineUnaryCounter.guard .spare .field .done
  | .field => fieldLoop .field .restore
  | .restore => Reduction.MachineTransfer.loopAt
      .scratch .target id false .restore (some (rankSkip 0))
  | .skip i => MachineLookup.discard .work (.skip i) (rankSkip (i.val + 1))
  | .done => .halt

theorem rankProgram_skip {i : Nat} (hi : i < 4097) :
    rankProgram (σ := σ) (rankSkip i) =
      MachineLookup.discard .work (rankSkip i) (rankSkip (i + 1)) := by
  simp only [rankSkip, dite_eq_left hi, rankProgram]

theorem rowGuard_succ (original work target scratch count fuelSuffix : List Bool)
    (k : Nat) (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (rankProgram (σ := σ))
      ⟨some .row, ((ambient, flag), register),
        memory original work target scratch count (encodeWord (k + 1) ++ fuelSuffix)⟩ =
      some ⟨some .field, ((ambient, flag), none),
        memory original work target scratch count (encodeWord k ++ fuelSuffix)⟩ := by
  change some (TM2.stepAux (rankProgram .row) _ _) = _
  simp [rankProgram, MachineUnaryCounter.guard, TM2.stepAux, encodeWord,
    List.replicate_succ]

theorem rowGuard_zero (original work target scratch count fuelSuffix : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (rankProgram (σ := σ))
      ⟨some .row, ((ambient, flag), register),
        memory original work target scratch count (encodeWord 0 ++ fuelSuffix)⟩ =
      some ⟨some .done, ((ambient, flag), none),
        memory original work target scratch count (encodeWord 0 ++ fuelSuffix)⟩ := rfl

theorem zeroRowsTrace (original work target scratch count fuelSuffix : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[2]
      (some ⟨some .row, ((ambient, flag), register),
        memory original work target scratch count (encodeWord 0 ++ fuelSuffix)⟩) =
      some ⟨none, ((ambient, flag), none),
        memory original work target scratch count (encodeWord 0 ++ fuelSuffix)⟩ := by
  rw [Function.iterate_succ_apply]
  change advance (TM2.step (rankProgram (σ := σ)))
    (TM2.step rankProgram ⟨some .row, ((ambient, flag), register),
      memory original work target scratch count (encodeWord 0 ++ fuelSuffix)⟩) = _
  rw [rowGuard_zero]
  rfl

/-- One actual row comparison consumes one unit of fuel and restores the
entire vertex query before discarding the remaining fixed row fields. -/
theorem rankRowTrace (r : Row) (hwidth : r.2.length = 4097) (v k : Nat)
    (original suffix targetSuffix fuelSuffix count : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[rowTime v r]
      (some ⟨some .row, ((ambient, false), register),
        memory original (encodeWords (rowWords r) ++ suffix) (encodeWord v ++ targetSuffix)
          [] count (encodeWord (k + 1) ++ fuelSuffix)⟩) =
      some ⟨some .row, ((ambient, false), none),
        memory original suffix (encodeWord v ++ targetSuffix) []
          (List.replicate (if r.1 = v then 1 else 0) true ++ count)
          (encodeWord k ++ fuelSuffix)⟩ := by
  have hfield := preservingFieldTrace RankLabel.field RankLabel.restore (rankSkip 0)
    rankProgram rfl rfl original (encodeWords r.2 ++ suffix) targetSuffix count
    (encodeWord k ++ fuelSuffix) r.1 v ambient none
  have hskip := discardFieldsTrace rankSkip (rankProgram (σ := σ)) r.2 0
    (by intro i hi; simpa only [Nat.zero_add] using rankProgram_skip (hwidth ▸ hi))
    original suffix (encodeWord v ++ targetSuffix) []
    (List.replicate (if r.1 = v then 1 else 0) true ++ count)
    (encodeWord k ++ fuelSuffix) ambient false none
  have hnonempty : r.2 ≠ [] := by intro h; simp [h] at hwidth
  simp only [Nat.zero_add, hwidth, rankSkip, lt_self_iff_false, ↓reduceDIte,
    hnonempty, ite_false, if_false] at hskip
  have htime : rowTime v r = (encodeWords r.2).length + (r.1 + min r.1 v + 2) + 1 := by
    simp only [rowTime, rowWords, encodeWords, List.length_append, encodeWord_length]
    omega
  rw [htime, Function.iterate_succ_apply]
  change (advance (TM2.step (rankProgram (σ := σ))))^[
      (encodeWords r.2).length + (r.1 + min r.1 v + 2)]
    (TM2.step rankProgram ⟨some .row, ((ambient, false), register),
      memory original (encodeWords (rowWords r) ++ suffix) (encodeWord v ++ targetSuffix)
        [] count (encodeWord (k + 1) ++ fuelSuffix)⟩) = _
  rw [rowGuard_succ, Function.iterate_add_apply]
  simp only [rowWords, encodeWords, List.append_assoc]
  rw [hfield]
  exact hskip

/-- Specification of the trace length; this function is not part of control. -/
def prefixTime (v : Nat) : List Row → Nat
  | [] => 2
  | r :: rs => prefixTime v rs + rowTime v r

/-- The row loop runs for the unary fuel on spare, not until the input ends. -/
theorem prefixTrace (rs : List Row) (hwidth : ∀ r ∈ rs, r.2.length = 4097) (v : Nat)
    (original suffix targetSuffix fuelSuffix count : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[prefixTime v rs]
      (some ⟨some .row, ((ambient, false), register),
        memory original (encodeWords (rs.flatMap rowWords) ++ suffix)
          (encodeWord v ++ targetSuffix) [] count (encodeWord rs.length ++ fuelSuffix)⟩) =
      some ⟨none, ((ambient, false), none),
        memory original suffix (encodeWord v ++ targetSuffix) []
          (List.replicate (rowsHits v rs) true ++ count) (encodeWord 0 ++ fuelSuffix)⟩ := by
  induction rs generalizing count register with
  | nil =>
      simpa only [prefixTime, List.flatMap_nil, encodeWords, List.nil_append,
        List.length_nil, rowsHits, List.replicate_zero] using
        zeroRowsTrace original suffix (encodeWord v ++ targetSuffix) [] count fuelSuffix
          ambient false register
  | cons r rs ih =>
      have hrow := rankRowTrace r (hwidth r (by simp)) v rs.length original
        (encodeWords (rs.flatMap rowWords) ++ suffix) targetSuffix fuelSuffix count ambient register
      have hrest := ih (by intro x hx; exact hwidth x (by simp [hx]))
        (List.replicate (if r.1 = v then 1 else 0) true ++ count) none
      simp only [prefixTime, List.flatMap_cons, encodeWords_append, List.append_assoc,
        List.length_cons]
      rw [Function.iterate_add_apply, hrow]
      simpa only [rowsHits, ← List.append_assoc, List.replicate_append_replicate,
        Nat.add_comm] using hrest

theorem prefixTime_le (v : Nat) (rs : List Row) :
    prefixTime v rs ≤ 3 * (encodeWords (rs.flatMap rowWords)).length + 2 := by
  induction rs with
  | nil => simp only [prefixTime, List.flatMap_nil, encodeWords, List.length_nil,
      Nat.mul_zero, Nat.zero_add, le_refl]
  | cons r rs ih =>
      have hr := rowTime_le v r
      simp only [prefixTime, List.flatMap_cons, encodeWords_append, List.length_append]
      omega

def queryWord (v k : Nat) (suffix : List Bool) : List Bool :=
  encodeWord v ++ (encodeWord k ++ suffix)

theorem encoded_rows_split (rs : List Row) (k : Nat) :
    encodeWords (rs.flatMap rowWords) =
      encodeWords ((rs.take k).flatMap rowWords) ++
        encodeWords ((rs.drop k).flatMap rowWords) := by
  have h := congrArg (fun xs : List Row => encodeWords (xs.flatMap rowWords))
    (List.take_append_drop k rs)
  simpa only [List.flatMap_append, encodeWords_append] using h.symm

def rankSteps (n m v k : Nat) (rs : List Row) (querySuffix : List Bool) : Nat :=
  2 * ((queryWord v k querySuffix).length + 1) + (v + 1) +
    2 * ((inputWord n m rs).length + 1) + (n + 1) + (m + 1) +
      prefixTime v (rs.take k)

/-- The full finite trace copies the query, extracts its unary row fuel,
preserves the graph while copying it, skips both headers, and counts a prefix. -/
theorem rankTrace (n m v k : Nat) (rs : List Row) (hk : k ≤ rs.length)
    (hwidth : ∀ r ∈ rs, r.2.length = 4097) (querySuffix count : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[rankSteps n m v k rs querySuffix]
      (some ⟨some .queryFirst, ((ambient, false), register),
        memory (inputWord n m rs) [] (queryWord v k querySuffix) [] count []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (inputWord n m rs) (encodeWords ((rs.drop k).flatMap rowWords))
          (queryWord v k querySuffix) []
          (List.replicate (rowsHits v (rs.take k)) true ++ count)
          (encodeWord 0 ++ querySuffix)⟩ := by
  have hquery := MachineCopy.copyTrace Tape.target Tape.spare Tape.scratch
    (by decide) (by decide) (by decide) false RankLabel.queryFirst RankLabel.querySecond
    (some RankLabel.querySkip) rankProgram rfl rfl
    (memory (inputWord n m rs) [] (queryWord v k querySuffix) [] count [])
    rfl (ambient, false) register
  simp only [memory_target, memory_spare, List.append_nil, update_memory_spare] at hquery
  have hquerySkip := MachineLookup.discardTrace Tape.spare RankLabel.querySkip RankLabel.tableFirst
    rankProgram rfl
    (memory (inputWord n m rs) [] (queryWord v k querySuffix) [] count (queryWord v k querySuffix))
    v (encodeWord k ++ querySuffix) rfl (ambient, false) none
  simp only [update_memory_spare] at hquerySkip
  have hcopy := MachineCopy.copyTrace Tape.original Tape.work Tape.scratch
    (by decide) (by decide) (by decide) false RankLabel.tableFirst RankLabel.tableSecond
    (some RankLabel.headerFirst) rankProgram rfl rfl
    (memory (inputWord n m rs) [] (queryWord v k querySuffix) [] count
      (encodeWord k ++ querySuffix)) rfl (ambient, false) none
  simp only [memory_original, memory_work, List.append_nil, update_memory_work] at hcopy
  have hfirst := MachineLookup.discardTrace Tape.work RankLabel.headerFirst RankLabel.headerSecond
    rankProgram rfl
    (memory (inputWord n m rs) (inputWord n m rs) (queryWord v k querySuffix) [] count
      (encodeWord k ++ querySuffix))
    n (encodeWord m ++ encodeWords (rs.flatMap rowWords))
    (inputWord_eq n m rs) (ambient, false) none
  simp only [update_memory_work] at hfirst
  have hsecond := MachineLookup.discardTrace Tape.work RankLabel.headerSecond RankLabel.row
    rankProgram rfl
    (memory (inputWord n m rs) (encodeWord m ++ encodeWords (rs.flatMap rowWords))
      (queryWord v k querySuffix) [] count (encodeWord k ++ querySuffix))
    m (encodeWords (rs.flatMap rowWords)) rfl (ambient, false) none
  simp only [update_memory_work] at hsecond
  have hprefix := prefixTrace (rs.take k)
    (by intro r hr; exact hwidth r (List.mem_of_mem_take hr)) v
    (inputWord n m rs) (encodeWords ((rs.drop k).flatMap rowWords))
    (encodeWord k ++ querySuffix) querySuffix count ambient none
  have htake : (rs.take k).length = k := by
    simp only [List.length_take, Nat.min_eq_left hk]
  rw [htake, ← encoded_rows_split rs k] at hprefix
  rw [show rankSteps n m v k rs querySuffix = prefixTime v (rs.take k) +
      ((m + 1) + ((n + 1) + (2 * ((inputWord n m rs).length + 1) +
        ((v + 1) + 2 * ((queryWord v k querySuffix).length + 1))))) by
      unfold rankSteps; omega,
    Function.iterate_add_apply _ (prefixTime v (rs.take k)),
    Function.iterate_add_apply _ (m + 1), Function.iterate_add_apply _ (n + 1),
    Function.iterate_add_apply _ (2 * ((inputWord n m rs).length + 1)),
    Function.iterate_add_apply _ (v + 1), hquery, hquerySkip, hcopy, hfirst, hsecond]
  exact hprefix

/-- The concrete trace has a linear bound in the two preserved input words. -/
theorem rankSteps_le (n m v k : Nat) (rs : List Row) (querySuffix : List Bool) :
    rankSteps n m v k rs querySuffix ≤
      5 * (inputWord n m rs).length + 3 * (queryWord v k querySuffix).length + 6 := by
  have hprefix := prefixTime_le v (rs.take k)
  have hsplit := congrArg List.length (encoded_rows_split rs k)
  simp only [List.length_append] at hsplit
  have hinput := inputWord_length n m rs
  have hquery : v + 1 ≤ (queryWord v k querySuffix).length := by
    simp only [queryWord, List.length_append, encodeWord_length]
    omega
  unfold rankSteps
  omega

open UniqueGamesTheorem.Foundations.PCP

end UniqueGamesTheorem.Foundations.Complexity.MachineCloudRank

/-! Actual inverse cloud numbering. The input table and query are copied
preservingly. A unary working rank decreases only on equal stored tail
fields; a separate unary row position increases on every skipped row.
Only finite phase flags and symbol registers occur in the control state. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCloudSelect

open Turing MachineComposition
open MachineCloudCount (Row rowWords rowTime rowsHits )

abbrev BaseTape := MachineCloudCount.Tape
abbrev BaseAlphabet := MachineCloudCount.Alphabet

variable {σ : Type}

def baseProgram : BaseLabel → TM2.Stmt BaseAlphabet BaseLabel (BaseState σ)
  | .queryFirst => Reduction.MachineTransfer.loopAt .target .scratch id false
      .queryFirst (some .querySecond)
  | .querySecond => MachineCopy.forkLoop .scratch .target .spare false
      .querySecond (some .querySkip)
  | .querySkip => MachineLookup.discard .spare .querySkip .tableFirst
  | .tableFirst => Reduction.MachineTransfer.loopAt .original .scratch id false
      .tableFirst (some .tableSecond)
  | .tableSecond => MachineCopy.forkLoop .scratch .original .work false
      .tableSecond (some .headerFirst)
  | .headerFirst => MachineLookup.discard .work .headerFirst .headerSecond
  | .headerSecond => MachineLookup.discard .work .headerSecond .field
  | .field => MachineCloudCount.fieldLoop .field .restore
  | .restore => Reduction.MachineTransfer.loopAt .scratch .target id false
      .restore (some .done)
  | .skip i => MachineLookup.discard .work (.skip i) (skipLabel (i.val + 1))
  | .clearWork => MachineDrain.drain .work .clearWork (some .clearRank)
  | .clearRank => MachineDrain.drain .spare .clearRank (some .done)
  | .done => .halt

theorem baseProgram_skip {i : Nat} (hi : i < 4097) :
    baseProgram (σ := σ) (skipLabel i) =
      MachineLookup.discard .work (skipLabel i) (skipLabel (i + 1)) := by
  simp only [skipLabel, dite_eq_left hi, baseProgram]

abbrev Tape := BaseTape ⊕ Unit
abbrev Alphabet : Tape → Type := MachineEmbedding.Alphabet BaseAlphabet (fun _ : Unit => Bool)

def go (phase : Phase) (label : Label) : TM2.Stmt Alphabet Label (State σ) :=
  .load (fun s => ((s.1.1, none), phase)) (.goto fun _ => label)

/-- Pop the one-bit match result. Only a match pops the remaining local
rank. Every completed skipped row separately pushes the global position. -/
def dispatcher : TM2.Stmt Alphabet Label (State σ) :=
  .branch (fun s => decide (s.2 = .checking))
    (.pop (.inl .count) (fun s bit => ((s.1.1, bit), s.2))
      (.branch (fun s => s.1.2.getD false)
        (.pop (.inl .spare) (fun s bit => ((s.1.1, bit), s.2))
          (.branch (fun s => s.1.2.getD false)
            (go .advancing (.inl (skipLabel 0)))
            (go .finishing (.inl .clearWork))))
        (go .advancing (.inl (skipLabel 0)))))
    (.branch (fun s => decide (s.2 = .advancing))
      (.push (.inr ()) (fun _ => true) (go .checking (.inl .field)))
      (.load (fun s => ((s.1.1, none), Phase.checking)) .halt))

def extra : Control → TM2.Stmt Alphabet Label (State σ)
  | .initialize_ => .push (.inr ()) (fun _ => false) (go .checking (.inl .queryFirst))
  | .dispatch => dispatcher

def memory (original work target scratch hit rank position : List Bool) :
    ∀ k, List (Alphabet k) :=
  MachineEmbedding.tapes (MachineCloudCount.memory original work target scratch hit rank)
    (fun _ : Unit => position)

@[simp] theorem memory_inl (a b c d e f g : List Bool) (k : BaseTape) :
    memory a b c d e f g (.inl k) = MachineCloudCount.memory a b c d e f k := rfl
@[simp] theorem memory_position (a b c d e f g : List Bool) :
    memory a b c d e f g (.inr ()) = g := rfl

@[simp] theorem update_memory_hit (a b c d e f g x : List Bool) :
    Function.update (memory a b c d e f g) (.inl .count) x = memory a b c d x f g := by
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr k => cases k; rfl
@[simp] theorem update_memory_rank (a b c d e f g x : List Bool) :
    Function.update (memory a b c d e f g) (.inl .spare) x = memory a b c d e x g := by
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr k => cases k; rfl
@[simp] theorem update_memory_position (a b c d e f g x : List Bool) :
    Function.update (memory a b c d e f g) (.inr ()) x = memory a b c d e f x := by
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr k => cases k; rfl

def cfg (label : Option Label) (phase : Phase)
    (original work target hit rank position : List Bool)
    (ambient : σ) (register : Option Bool) : TM2.Cfg Alphabet Label (State σ) :=
  ⟨label, (((ambient, false), register), phase), memory original work target [] hit rank position⟩

def prefixTime (v : Nat) : List Row → Nat
  | [] => 0
  | r :: rs => prefixTime v rs + (rowTime v r + 3)

abbrev queryWord := MachineCloudRank.queryWord

def prepareSteps (n m v rank : Nat) (rs : List Row) (querySuffix : List Bool) : Nat :=
  2 * ((queryWord v rank querySuffix).length + 1) + (v + 1) +
    2 * ((MachineCloudCount.inputWord n m rs).length + 1) + (n + 1) + (m + 1)

def totalSteps (n m v rank : Nat) (rs preceding : List Row)
    (work querySuffix : List Bool) : Nat :=
  prepareSteps n m v rank rs querySuffix + prefixTime v preceding +
    2 * v + work.length + querySuffix.length + 9

theorem prefixTime_le (v : Nat) (rs : List Row) :
    prefixTime v rs ≤ 6 * (encodeWords (rs.flatMap rowWords)).length := by
  induction rs with
  | nil => simp [prefixTime, encodeWords]
  | cons r rs ih =>
    have hr := MachineCloudCount.rowTime_le v r
    have hpos : 1 ≤ (encodeWords (rowWords r)).length := by
      simp only [rowWords, encodeWords, List.length_append, encodeWord_length]
      omega
    simp only [prefixTime, List.flatMap_cons, encodeWords_append, List.length_append]
    omega

theorem totalSteps_le (n m v rank : Nat) (rs preceding : List Row) (work querySuffix : List Bool)
    (hword : encodeWords (rs.flatMap rowWords) =
      encodeWords (preceding.flatMap rowWords) ++ (encodeWord v ++ work)) :
    totalSteps n m v rank rs preceding work querySuffix ≤
      10 * ((MachineCloudCount.inputWord n m rs).length + (queryWord v rank querySuffix).length) + 20 := by
  have hp := prefixTime_le v preceding
  have hw := congrArg List.length hword
  simp only [List.length_append, encodeWord_length] at hw
  have ht := MachineCloudCount.inputWord_length n m rs
  have hq : (queryWord v rank querySuffix).length =
      v + 1 + (rank + 1) + querySuffix.length := by
    simp only [queryWord, MachineCloudRank.queryWord, List.length_append, encodeWord_length]
    omega
  unfold totalSteps prepareSteps
  omega

open UniqueGamesTheorem.Foundations.PCP

end UniqueGamesTheorem.Foundations.Complexity.MachineCloudSelect

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularInternalRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Physical construction of an internal regularization row

The input values belong on unary tapes. The cloud degree and the queried port
are the only arithmetic parameters fixed in finite control. The stored cloud
rotation supplies both the destination's local index and the return port.
The final row contains the full fixed equality predicate.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow

open Turing MachineComposition
open PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ : Type} [DecidableEq K]

abbrev SelectTape := MachineCloudSelect.Tape ⊕ SelectExtraTape
abbrev RawSelectAlphabet : SelectTape → Type :=
  MachineEmbedding.Alphabet MachineCloudSelect.Alphabet (fun _ : SelectExtraTape => Bool)
abbrev SelectAlphabet (_ : SelectTape) := Bool

theorem selectAlphabet_eq : RawSelectAlphabet = SelectAlphabet := by
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr k => rfl

def selectToBoolWord : (k : SelectTape) → List (RawSelectAlphabet k) → List Bool
  | .inl (.inl _), word => word
  | .inl (.inr _), word => word
  | .inr _, word => word

def selectToBoolTapes (base : ∀ k, List (RawSelectAlphabet k)) : SelectTape → List Bool :=
  fun k => selectToBoolWord k (base k)

theorem alphabet_tapes_apply {K : Type} {Γ Δ : K → Type}
    (h : Γ = Δ) (base : ∀ k, List (Γ k)) (k : K) :
    MachineAlphabetTransport.tapes h base k =
      Eq.mp (congrArg (fun alphabet => List (alphabet k)) h) (base k) := by
  cases h
  rfl

theorem selectToBoolTapes_eq (base : ∀ k, List (RawSelectAlphabet k)) :
    selectToBoolTapes base = MachineAlphabetTransport.tapes selectAlphabet_eq base := by
  funext k
  rw [alphabet_tapes_apply]
  cases k with
  | inl k => cases k <;> rfl
  | inr k => rfl

def selectScratch : SelectTape := .inl (.inl .scratch)
def selectQuery : SelectTape := .inl (.inl .target)
def selectOutput : SelectTape := .inl (.inr ())

def compareSlots : Fin 4 ↪ SelectTape where
  toFun i := ![.inr .localIndex, .inr .cloudSize, .inr .savedLeft, .inr .savedRight] i
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def subtractSlots : Fin 4 ↪ SelectTape where
  toFun i := ![.inr .localWork, .inr .sizeWork, .inr .savedLeft, .inr .savedRight] i
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def copySource : SelectCopy → SelectTape
  | .oldLocal | .dummyLocal => .inr .localIndex
  | .oldOwner => .inr .owner
  | .dummySize => .inr .cloudSize
  | .dummyDifference => .inr .localWork

def copyDestination : SelectCopy → SelectTape
  | .oldLocal | .oldOwner => selectQuery
  | .dummyLocal => .inr .localWork
  | .dummySize => .inr .sizeWork
  | .dummyDifference => selectOutput

def afterCopy : SelectCopy → SelectLabel
  | .oldLocal => .inr (.copy .oldOwner .seed)
  | .oldOwner => .inl (.inr .initialize_)
  | .dummyLocal => .inr (.copy .dummySize .seed)
  | .dummySize => .inr .subtract
  | .dummyDifference => .inr (.add .prefixOffset .scan)

def addSource : SelectAdd → SelectTape
  | .prefixOffset => .inr .prefixOffset
  | .darts => .inr .darts

def afterAdd : SelectAdd → SelectLabel
  | .prefixOffset => .inr (.add .darts .scan)
  | .darts => .inr (.cleanup 0)

def cleanupTape (i : Fin 5) : SelectTape :=
  ![selectQuery, .inr .localWork, .inr .sizeWork, .inr .savedLeft, .inr .savedRight] i

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineCloudPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCloudPrefix

open Turing MachineComposition
open UniqueGamesTheorem.Foundations.PCP
open scoped BigOperators

variable {σ : Type}

/-- Uniform budget for one vertex iteration, including unary addition and
cleanup. Its input argument bounds the complete table length. -/
def cycleBudget (L : Nat) : Nat :=
  (ExpanderFamily.growth + 8) * (2 * L) ^ 2 + 25 * (2 * L) + 10 +
    (ExpanderFamily.growth + 2) * L + 5

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.X *
      (Polynomial.C (ExpanderFamily.growth + 8) * (2 * Polynomial.X) ^ 2 +
        25 * (2 * Polynomial.X) + 10 +
          Polynomial.C (ExpanderFamily.growth + 2) * Polynomial.X + 5) +
    2 * (Polynomial.X + 1) + 3

end UniqueGamesTheorem.Foundations.Complexity.MachineCloudPrefix

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularMetadata
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual metadata preparation for an original regularized vertex. The
shared 27-tape row interface is preserved, with two explicit extra outputs
for padding count and geometric level. Family generation is a subsequent
stage and owns the rotor tape. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularMetadata

open Turing MachineComposition
open UniqueGamesTheorem.Foundations.PCP

def rankTape : MachineCloudCount.Tape → Tape
  | .original => .inl 0
  | .work => .inl 10
  | .target => .inl 9
  | .scratch => .inl 11
  | .count => .inl 3
  | .spare => .inl 12

variable {σ : Type}

def rankView : Tape → Option MachineCloudCount.Tape
  | .inl i => match i.val with
    | 0 => some .original
    | 10 => some .work
    | 9 => some .target
    | 11 => some .scratch
    | 3 => some .count
    | 12 => some .spare
    | _ => none
  | .inr _ => none

theorem rankView_left (k : MachineCloudCount.Tape) : rankView (rankTape k) = some k := by
  cases k <;> rfl
theorem rankView_right (j : Tape) (k : MachineCloudCount.Tape)
    (h : rankView j = some k) : rankTape k = j := by
  cases j with
  | inl j => fin_cases j <;> simp_all [rankView, rankTape] <;> subst k <;> rfl
  | inr j => simp_all [rankView]

def rankQuery (v x : Nat) : List Bool := MachineCloudRank.queryWord v x []

noncomputable def timePolynomial : Polynomial Nat :=
  (MachineCloudPrefix.timePolynomial + MachineCloudPadding.timePolynomial).comp
      (2 * Polynomial.X) + 40 * (Polynomial.X + 1)

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularMetadata

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularDummyRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual inherited-row emission for a dummy vertex

The fixed program preserves the physical unary vertex index on tape zero,
computes its inherited reverse index on tape one, invokes the actual one-port
dummy-row emitter, and drains the computed index and fixed true relation.
Tape four accumulates output. Tapes one, two, three, and five are empty at both
boundaries. The degree is fixed program data, not an input-dependent control
parameter.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularDummyRow

open Turing MachineComposition PCP.GraphTables

def emittedBits (q x : Nat) : List Bool :=
  MachineDummyRows.rowBits x (reverseIndex q x)

structure Input (x : Nat) (base : Tape → List Bool) : Prop where
  source : base 0 = encodeWord x
  reverseEmpty : base 1 = []
  relationEmpty : base 2 = []
  scratchEmpty : base 3 = []
  rowEmpty : base 5 = []

def memory (x : Nat) (output : List Bool) : Tape → List Bool :=
  ![encodeWord x, [], [], [], output, []]

theorem memory_input (x : Nat) (output : List Bool) : Input x (memory x output) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem affine_frame (x e : Nat) (base : Tape → List Bool) (input : Input x base) :
    Function.update base 1 (encodeWord e) =
      MachineDummyRows.initialTapes x e (base 4) := by
  funext k
  fin_cases k <;>
    simp [MachineDummyRows.initialTapes, MachineDummyRows.fieldTapes,
      input.source, input.relationEmpty, input.scratchEmpty, input.rowEmpty]

theorem cleanup_frame (x e : Nat) (output : List Bool)
    (base : Tape → List Bool) (input : Input x base) :
    Function.update (Function.update (MachineDummyRows.fieldTapes x e output) 1 []) 2 [] =
      Function.update base 4 output := by
  funext k
  fin_cases k <;>
    simp [MachineDummyRows.fieldTapes, input.source, input.reverseEmpty,
      input.relationEmpty, input.scratchEmpty, input.rowEmpty]

/-- Sum of the actual arithmetic, row-emission, and cleanup transition counts. -/
def steps (q x : Nat) (output : List Bool) : Nat :=
  ((2 * (x + 1) + 1) + (MachineDummyRows.steps x (reverseIndex q x) output 1 + 1)) +
    (((encodeWord (reverseIndex q x + 1)).length + 1) +
      (MachineDummyRows.trueBits.length + 1))

theorem steps_eq (q x : Nat) (output : List Bool) :
    steps q x output = timeBound q x output.length := by
  simp only [steps, MachineDummyRows.steps, encodeWord_length, MachineDummyRows.trueBits_length,
    reverseIndex, timeBound]
  ring

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularDummyRow

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularVertexBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual regularized vertex-block execution

The finite internal-port loop invokes the checked row machine for every port in
order. Each invocation restores the shared 27-tape frame. Inherited-row stages
use fixed tape placements and finite state permutations.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularVertexBlock

open Turing MachineComposition PCP MachineRegularInternalRow
open PreprocessingCloudIndex PreprocessingRegularTables

variable {σ Λ : Type}

theorem portBits_eq {q : Nat} (bits : Fin q → List Bool) (k : Nat) (hk : k ≤ q) :
    portBits bits k = (List.ofFn (fun p : Fin k => bits ⟨p.val, lt_of_lt_of_le p.isLt hk⟩)).flatten := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : k < q := by omega
    rw [portBits, dite_eq_left h, ih (by omega), List.ofFn_succ_last, List.flatten_append]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    rfl

theorem portBits_all {q : Nat} (bits : Fin q → List Bool) :
    portBits bits q = (List.ofFn bits).flatten := by
  simpa only [Fin.eta] using portBits_eq bits q (Nat.le_refl q)

theorem dummyMemory_update (x : Nat) (output output' : List Bool) :
    Function.update (MachineRegularDummyRow.memory x output)
      (4 : MachineRegularDummyRow.Tape) output' = MachineRegularDummyRow.memory x output' := by
  funext j; fin_cases j <;> rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularVertexBlock

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOriginalBodyBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Polynomial runtime for the actual original-vertex body. The size parameter
includes the already accumulated output, so no output-prefix premise is used. -/
namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBodyBounds

open Turing MachineComposition PCP PreprocessingCloudIndex PreprocessingRegularTables
open PreprocessingMachineBounds MachineRegularOriginalBody

noncomputable def wide : Polynomial Nat := Polynomial.C (ExpanderFamily.growth + 1) * Polynomial.X
noncomputable def rowPolynomial (q : Nat) : Polynomial Nat :=
  wide + wide * Polynomial.C (q + 1) + 8192
noncomputable def outputPolynomial (q : Nat) : Polynomial Nat :=
  wide + Polynomial.C q * rowPolynomial q
noncomputable def corePolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C (5*q+32) * rotorPolynomial q + 10*wide + 2*wide + 13*wide + 5*wide +
    Polynomial.C (5*q+10)*(wide+wide) + 4*wide + 2*outputPolynomial q +
      Polynomial.C (8*q+41066)
noncomputable def blockPolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C q * corePolynomial q + Polynomial.C (5*q+20)*wide +
    2*outputPolynomial q + Polynomial.C (5*q+40995)
noncomputable def cleanupPolynomial (q : Nat) : Polynomial Nat := 6*wide + rotorPolynomial q + 13

theorem blockPolynomial_eval (q L : Nat) :
    (blockPolynomial q).eval L =
      MachineRegularVertexBlock.originalTimeBound q
        ((ExpanderFamily.growth+1)*L) ((rotorPolynomial q).eval L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L) := by
  simp only [blockPolynomial, corePolynomial, outputPolynomial, rowPolynomial, wide,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, MachineRegularVertexBlock.originalTimeBound,
    MachineRegularVertexBlock.portTimeBound, MachineRegularInternalRow.coreTimeBound,
    MachineRegularOriginalClean.timeBound, MachineRegularVertexBlock.rowSizeBound]
  ring

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBodyBounds

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOwnerBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual execution and exact runtime of the fixed dummy-owner program. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable PreprocessingRegularLoopWords

theorem oneStep {A : Type} {f : A → Option A} {a b : A}
    (h : f a = some b) : (advance f)^[1] (some a) = some b := by
  simpa only [Function.iterate_one, advance_some] using h

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOwnerBodyBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Bounds for actual dummy-owner execution

The size parameter includes the old output length. During the owner loop,
newly emitted dummy blocks are bounded by the actual complete regularized
table codec. No hypothesis about a machine body's execution supplies a bound.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBodyBounds

open Turing MachineComposition PCP PreprocessingCloudIndex PreprocessingRegularTables
open PreprocessingMachineBounds PreprocessingRegularLoopWords

noncomputable def wide : Polynomial Nat := Polynomial.C (ExpanderFamily.growth + 1) * Polynomial.X

noncomputable def rowPolynomial (q : Nat) : Polynomial Nat :=
  wide + wide * Polynomial.C (q + 1) + 8192

noncomputable def outputPolynomial (q : Nat) : Polynomial Nat :=
  wide + regularPolynomial + Polynomial.C q * rowPolynomial q

noncomputable def corePolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C (5*q+32) * rotorPolynomial q + 10*wide + 2*wide + 13*wide + 5*wide +
    Polynomial.C (5*q+10)*(wide+wide) + 4*wide + 2*outputPolynomial q +
      Polynomial.C (8*q+41066)

noncomputable def blockPolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C q * corePolynomial q + Polynomial.C (5*q+11)*wide +
    2*outputPolynomial q + Polynomial.C (5*q+40986)

theorem blockPolynomial_eval (q L : Nat) :
    (blockPolynomial q).eval L =
      MachineRegularVertexBlock.dummyTimeBound q
        ((ExpanderFamily.growth+1)*L) ((rotorPolynomial q).eval L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L)
        (((ExpanderFamily.growth+1)*L) + regularPolynomial.eval L)
        ((ExpanderFamily.growth+1)*L) := by
  simp only [blockPolynomial, corePolynomial, outputPolynomial, rowPolynomial, wide,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, MachineRegularVertexBlock.dummyTimeBound,
    MachineRegularVertexBlock.portTimeBound, MachineRegularInternalRow.coreTimeBound,
    MachineRegularDummyRow.timeBound, MachineRegularVertexBlock.rowSizeBound]
  simp only [Nat.add_assoc]

noncomputable def prePolynomial : Polynomial Nat :=
  MachineCloudPadding.timePolynomial.comp (2*Polynomial.X+1) + 4*wide + 6

noncomputable def loopPolynomial : Polynomial Nat :=
  wide * (blockPolynomial internalDegree + 2)

noncomputable def cleanupPolynomial : Polynomial Nat :=
  6*wide + rotorPolynomial internalDegree + 13

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBodyBounds

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual regular-table construction

The header subroutine reads the two original graph headers, computes the
padding total by the actual prefix machine, performs unary addition and
constant multiplication, and appends both resulting header fields. The
outer vertex routines are assembled from actual metadata and row programs.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable

open Turing MachineComposition
open UniqueGamesTheorem.Foundations.PCP

namespace Header

variable {σ : Type}

noncomputable def arithmeticPolynomial (q : Nat) : Polynomial Nat :=
  let X : Polynomial Nat := Polynomial.X
  let G : Polynomial Nat := Polynomial.C ExpanderFamily.growth * X
  let D : Polynomial Nat := Polynomial.C (ExpanderFamily.growth * (q + 1)) * X
  (12 * X + 11) + ((2 * (X + 2) + (G + 1)) + (2 * (G + 1) + 1)) +
    (((2 * (D + 2) + 2 * (G + 2)) + (2 * ((G + D + 2) + X) + 3)) + 1 + (X + 1) + 1)

noncomputable def timePolynomial (q : Nat) : Polynomial Nat :=
  MachineCloudPrefix.timePolynomial.comp (2 * Polynomial.X + 1) + arithmeticPolynomial q

end Header

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineUnaryEqualityBit
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec.decodeWords_encodeWord _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter.counterTapes_counter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineUnaryEqualityBit

open Turing
open MachineComposition

variable {K Λ A : Type} [DecidableEq K]

def bitEncoding (bit : Bool) : List Bool := encodeWord (if bit then 1 else 0)

theorem encodeWord_eq_iff (a b : Nat) : encodeWord a = encodeWord b ↔ a = b := by
  constructor
  · intro h
    have hlength := congrArg List.length h
    simp only [encodeWord_length] at hlength
    omega
  · rintro rfl
    rfl

theorem emit_step (destination : K) (bit : Bool) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (label : Λ) (atEmit : program label = emit destination bit exit)
    (state : State A) (base : K → List Bool) :
    TM2.step program ⟨some label, state, base⟩ =
      some ⟨exit, state,
        Function.update base destination (bitEncoding bit ++ base destination)⟩ := by
  change some (TM2.stepAux (program label) state base) = _
  rw [atEmit]
  cases bit <;> cases exit <;>
    simp [emit, exitAt, TM2.stepAux, bitEncoding, encodeWord, Function.update_idem]

end UniqueGamesTheorem.Foundations.Complexity.MachineUnaryEqualityBit

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_PoweringMachineLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-control preparation and enumeration for the powered-table
machine. The degree and radius determine a fixed multiplier `B = 2*d^t`.
Only the input vertex count varies at runtime, and it is stored on unary
tapes. The header machine consumes a cloned first input field, preserving
its unread suffix, and writes the three fields needed by the outer loop.

The row enumeration lemmas specify the canonical suffix invariant used with
`MachineCountedLoop`. They do not stand in for the caller's per-row machine
traces, which must be supplied by the actual walk and relation evaluator. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineLoop

open Turing

def initialTapes (n : Nat) (suffix : List Bool) : HeaderTape → List Bool
  | .source => encodeWord n ++ suffix
  | _ => []

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineLoop

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_PoweringMachineFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Physical output headers followed by complete work-tape cleanup

The finite program first copies the dart-count word onto the existing row
output, then copies the vertex-count word, and finally drains every tape except
the output. Both unary header values are read from physical tapes; they do not
parameterize the program. Header sources and their unread suffixes are restored
by the two copies before cleanup. The final configuration contains the full
encoded header and rows on the output tape and empty words on every other tape.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K] {N : Nat}

def afterD (output : K) (base : K → List Bool) (m : Nat) : K → List Bool :=
  Function.update base output (encodeWord m ++ base output)

def afterHeaders (output : K) (base : K → List Bool) (n m : Nat) : K → List Bool :=
  Function.update base output (encodeWords [n, m] ++ base output)

@[simp] theorem afterHeaders_output (output : K) (base : K → List Bool) (n m : Nat) :
    afterHeaders output base n m output = encodeWords [n, m] ++ base output := by
  simp only [afterHeaders, Function.update_self]

theorem afterHeaders_other (output : K) (base : K → List Bool) (n m : Nat)
    (k : K) (hk : k ≠ output) : afterHeaders output base n m k = base k :=
  Function.update_of_ne hk _ _

theorem afterHeaders_length_le (output : K) (base : K → List Bool) (n m bound : Nat)
    (bounded : ∀ k, (base k).length ≤ bound) (k : K) :
    (afterHeaders output base n m k).length ≤ bound + n + m + 2 := by
  by_cases hk : k = output
  · subst k
    rw [afterHeaders_output]
    have hb := bounded output
    simp only [List.length_append, encodeWords, encodeWord_length, List.length_nil]
    omega
  · rw [afterHeaders_other output base n m k hk]
    have hb := bounded k
    omega

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PoweringTableLayout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Vertex-major serialization of the actual powering table

Each vertex contributes a fixed number of consecutive stored dart rows. The
identities below group the actual vector, including every predicate entry, and
then apply the shared word codec. They do not assume an output layout or assert
a machine running time. Unary bit lengths can vary with the stored indices.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringTableLayout

open UniqueGamesTheorem.Foundations.Complexity
open PoweringTables PoweringEnumeration

theorem encodeWords_flatMap {α : Type*} (items : List α)
    (words : α → List Nat) :
    encodeWords (items.flatMap words) =
      items.flatMap (fun item => encodeWords (words item)) := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [List.flatMap_cons, encodeWords_append, ih]

end UniqueGamesTheorem.Foundations.PCP.PoweringTableLayout

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_PoweringMachineVertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineVertex

open Turing MachineComposition PCP

variable {K Λ : Type} [DecidableEq K] {vertices d n : Nat}

theorem encodeWords_flatMap {X : Type*} (xs : List X) (f : X → List Nat) :
    encodeWords (xs.flatMap f) = xs.flatMap (fun x => encodeWords (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineVertex

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_PoweringPolynomialBudgetLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finishing cost from the actual preceding machine execution

Every stack can grow by at most the fixed program's push bound in one
transition. Consequently an actual bounded execution from the standard input
configuration supplies the uniform stack bound needed by the finishing phase.
The bound below uses the same global machine for that preceding execution; no
separate tape-size hypothesis or numerical simulation is substituted for it.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringRuntimeBudget

open Turing

/-- Uniform stack growth along an actual execution, from any initial configuration. -/
theorem stackLength_le_of_execution (tm : FinTM2) (start finish : tm.Cfg)
    (initialBound priorBudget : Nat)
    (initial : ∀ k, (start.stk k).length ≤ initialBound)
    (prior : StateTransition.EvalsToInTime tm.step start (some finish) priorBudget)
    (k : tm.K) :
    (finish.stk k).length ≤ initialBound + priorBudget * Runtime.programPushBound tm := by
  have grown := Runtime.executionSizeBound tm.step (fun cfg => (cfg.stk k).length)
    (Runtime.programPushBound tm) (Runtime.stepStackLength tm k) prior
  exact grown.trans (Nat.add_le_add_right (initial k) _)

/-- Standard input initialization bounds every initial stack by the input length. -/
theorem stackLength_le_from_input (tm : FinTM2) (input : List (tm.Γ tm.k₀))
    (finish : tm.Cfg) (priorBudget : Nat)
    (prior : StateTransition.EvalsToInTime tm.step (initList tm input)
      (some finish) priorBudget) (k : tm.K) :
    (finish.stk k).length ≤ input.length + priorBudget * Runtime.programPushBound tm :=
  stackLength_le_of_execution tm (initList tm input) finish input.length priorBudget
    (Runtime.initialStackLength tm input) prior k

end UniqueGamesTheorem.Foundations.Complexity.PoweringRuntimeBudget

/-! Complete execution of the one fixed powering machine on the actual
port-table input and generic graph-table output encodings. The varying vertex
count remains on unary tapes throughout. -/

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_RuntimeModel
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec.decodeWords_encodeWord _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter.counterTapes_counter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The finite registers and physical tape roles of the alphabet-table machine.
Input-sized numbers occur only on unary tapes. The comparison and emitter
register layouts are related by explicit, executable product rearrangements.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.RuntimeModel

open Turing
open UniqueGamesTheorem.Foundations.Complexity

abbrev Ambient (q : Nat) := Flags × GenericGraphTables.RelationTable q
abbrev State (q : Nat) := Ambient q × Option Bool

def normal {q : Nat} (relation : GenericGraphTables.RelationTable q) (selfLoop : Bool) : State q :=
  (((selfLoop, false, none), relation), none)

def initial (q : Nat) : State q := normal (Vector.replicate (q * q) false) false

def context {q : Nat} (ambient : Ambient q) : GenericGraphTables.RelationTable q × Bool :=
  (ambient.2, ambient.1.1)

def compareEquiv (q : Nat) : State q ≃
    MachineCompare.State (GenericGraphTables.RelationTable q × Bool) where
  toFun s := ((s.1.2, s.1.1.1), s.1.1.2.1, s.1.1.2.2, s.2)
  invFun s := (((s.1.2, s.2.1, s.2.2.1), s.1.1), s.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem compareEquiv_normal {q : Nat}
    (relation : GenericGraphTables.RelationTable q) (selfLoop : Bool) :
    compareEquiv q (normal relation selfLoop) =
      ((relation, selfLoop), false, none, none) := rfl

def emitterEquiv (q : Nat) : ((Ambient q × Unit) × Option Bool) ≃ State q where
  toFun s := (s.1.1, s.2)
  invFun s := ((s.1, ()), s.2)
  left_inv s := by rcases s with ⟨⟨s, u⟩, r⟩; cases u; rfl
  right_inv _ := rfl

theorem setupPorts_injective : Function.Injective setupPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [setupPorts]

theorem headPorts_injective : Function.Injective headPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [headPorts]

theorem cleanupPorts_ne_output (i : Fin 15) : cleanupPorts i ≠ .output := by
  fin_cases i <;> simp [cleanupPorts]

variable {Λ : Type} {q : Nat}

def compareStatement (stmt : TM2.Stmt Alphabet Λ
    (MachineCompare.State (GenericGraphTables.RelationTable q × Bool))) :
    TM2.Stmt Alphabet Λ (State q) :=
  MachineControl.statement id (compareEquiv q).symm stmt

def emitterStatement (stmt : TM2.Stmt Alphabet Λ ((Ambient q × Unit) × Option Bool)) :
    TM2.Stmt Alphabet Λ (State q) :=
  MachineControl.statement id (emitterEquiv q) stmt

/-- Store the result chosen by the actual comparison's equal/different exit.
This does not compare tape contents in a register transition. -/
def storeLoop (value : Bool) (next : Λ) : TM2.Stmt Alphabet Λ (State q) :=
  .load (fun state => (((value, false, none), state.1.2), none)) (.goto fun _ => next)

theorem stepAux_storeLoop (value : Bool) (next : Λ) (state : State q)
    (base : Tape → List Bool) :
    TM2.stepAux (storeLoop value next) state base =
      ⟨some next, normal state.1.2 value, base⟩ := rfl

def nextRow (next : Λ) : TM2.Stmt Alphabet Λ (State q) :=
  .push .edge (fun _ => true)
    (.load (fun state => (state.1, none)) (.goto fun _ => next))

theorem stepAux_nextRow (next : Λ) (state : State q)
    (base : Tape → List Bool) (edge : Nat) (suffix : List Bool)
    (he : base .edge = encodeWord edge ++ suffix) :
    TM2.stepAux (nextRow next) state base =
      ⟨some next, (state.1, none),
        Function.update base .edge (encodeWord (edge + 1) ++ suffix)⟩ := by
  simp [nextRow, TM2.stepAux, he, encodeWord, List.replicate_succ]

/-- One-step simulations transport complete timed executions through the
explicit finite register permutations. -/
def transportInTime {K τ υ : Type} [DecidableEq K] {Γ : K → Type}
    (e : τ ≃ υ) (p : Λ → TM2.Stmt Γ Λ τ)
    {start finish : TM2.Cfg Γ Λ τ} {budget : Nat}
    (run : StateTransition.EvalsToInTime (TM2.step p) start (some finish) budget) :
    StateTransition.EvalsToInTime (TM2.step (MachineControl.program (Equiv.refl Λ) e p))
      (MachineControl.configuration id e start)
      (some (MachineControl.configuration id e finish)) budget := by
  apply MachineComposition.liftExecutionInTime _ _ (MachineControl.configuration id e) _ run
  intro a b hab
  have h := MachineControl.step_simulation (Equiv.refl Λ) e p a
  rw [hab] at h
  exact h

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.RuntimeModel

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_CompareLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.CompareLoop

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open RuntimeModel

variable {q : Nat} {Λ : Type}

/-- A composable block with exactly seven internal control labels. -/
def statement (labels : Label → Λ) (next : Λ) :
    Label → TM2.Stmt Alphabet Λ (State q)
  | .leftFirst => compareStatement (MachineFieldProfile.copyStatement
      (Reduction.MachineTransfer.loopAt .tail .scratch id false
        (labels .leftFirst) (some (labels .leftSecond))))
  | .leftSecond => compareStatement (MachineFieldProfile.copyStatement
      (MachineCopy.forkLoop .scratch .tail .compareLeft false
        (labels .leftSecond) (some (labels .rightFirst))))
  | .rightFirst => compareStatement (MachineFieldProfile.copyStatement
      (Reduction.MachineTransfer.loopAt .head .scratch id false
        (labels .rightFirst) (some (labels .rightSecond))))
  | .rightSecond => compareStatement (MachineFieldProfile.copyStatement
      (MachineCopy.forkLoop .scratch .head .compareRight false
        (labels .rightSecond) (some (labels .compare))))
  | .compare => compareStatement (MachineCompare.loop .compareLeft .compareRight
      (labels .compare) (some (labels .equalStore)) (some (labels .differentStore)))
  | .equalStore => storeLoop true next
  | .differentStore => storeLoop false next

theorem compareProgram_at
    (program : Λ → TM2.Stmt Alphabet Λ (State q)) (label : Λ)
    (stmt : TM2.Stmt Alphabet Λ
      (MachineCompare.State (GenericGraphTables.RelationTable q × Bool)))
    (atLabel : program label = compareStatement stmt) :
    (MachineControl.program (Equiv.refl Λ) (compareEquiv q) program) label = stmt := by
  change MachineControl.statement id (compareEquiv q) (program label) = stmt
  rw [atLabel]
  exact MachineFieldProfile.statement_roundtrip (compareEquiv q) stmt

theorem encodeWord_eq_iff (left right : Nat) :
    encodeWord left = encodeWord right ↔ left = right := by
  constructor
  · intro h
    have hh := congrArg List.length h
    simpa only [encodeWord_length, Nat.add_right_cancel_iff] using hh
  · rintro rfl
    rfl

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.CompareLoop

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_Addresses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Affine numeric fields of the alphabet-reduction table

The five unbounded unary inputs are n, m, e, tail, head, in that order.
Every field uses a fixed list of natural coefficients and one bounded offset.
For a fixed local event and slot, the query field's coefficient list does not
depend on the input predicate. The predicate changes only its bounded offset.
Evaluation uses the same `Emitter.affineValue` as the actual unary emitter.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Addresses

open UniqueGamesTheorem.Foundations.Hastad
open Enumeration

/-- One q-only bound covers every coefficient and every finite offset. -/
def fieldBound (q : Nat) : Nat :=
  12 * localCount q + tapeCount q + pairTapeCount q + 1

theorem fieldBound_pos (q : Nat) : 0 < fieldBound q := by
  unfold fieldBound
  omega

theorem tapeCount_lt_bound (q : Nat) : tapeCount q < fieldBound q := by
  unfold fieldBound
  omega

theorem pairTapeCount_lt_bound (q : Nat) : pairTapeCount q < fieldBound q := by
  unfold fieldBound
  omega

theorem localCount_lt_bound (q : Nat) : localCount q < fieldBound q := by
  unfold fieldBound
  omega

theorem twelve_local_lt_bound (q : Nat) : 12 * localCount q < fieldBound q := by
  unfold fieldBound
  omega

def zeroOffset (q : Nat) : Fin (fieldBound q) := ⟨0, fieldBound_pos q⟩

def headerVertices (q : Nat) : Field (fieldBound q) :=
  ⟨[(0, tapeCount q), (1, localCount q + pairTapeCount q)], zeroOffset q⟩

def headerDarts (q : Nat) : Field (fieldBound q) :=
  ⟨[(1, 12 * localCount q)], zeroOffset q⟩

def vertexQueryTerms (q : Nat) (side : Bool) : Terms :=
  [(1, localCount q), (if side then 4 else 3, tapeCount q)]

def edgeQueryTerms (q : Nat) : Terms :=
  [(1, localCount q), (0, tapeCount q), (2, pairTapeCount q)]

theorem headerVertices_eval (q n m edge tail head : Nat) :
    eval (headerVertices q) (values n m edge tail head) = vertexCount n m q := by
  simp [eval, headerVertices, values, zeroOffset, Emitter.affineValue,
    vertexCount, eventCount, addressCount, Nat.mul_add,
    Nat.mul_comm, Nat.add_comm, Nat.add_assoc]

theorem headerDarts_eval (q n m edge tail head : Nat) :
    eval (headerDarts q) (values n m edge tail head) = dartCount m q := by
  simp [eval, headerDarts, values, zeroOffset, Emitter.affineValue,
    dartCount, eventCount, Nat.mul_comm, Nat.mul_assoc]

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Addresses

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_EmitRows
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The actual alphabet-reduction row template. The old predicate and the loop flag
are finite registers. All unbounded quantities reside in five preserved unary
tapes. The fixed event/slot/orientation order is retained without deduplication.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.EmitRows

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open Emitter

theorem bitValues_ofFn {σ : Type} {n : Nat}
    (relation : σ → Vector Bool n) (context : σ) :
    (List.ofFn (fun index : Fin n => fun state => (relation state)[index])).map
      (fun bit => if bit context then 1 else 0) =
      (relation context).toList.map GraphTables.bitWord := by
  rw [← vector_list_ofFn (relation context)]
  simp only [List.map_ofFn]
  rfl

theorem encodeWords_flatMap {α : Type} (items : List α) (words : α → List Nat) :
    encodeWords (items.flatMap words) = items.flatMap (fun item => encodeWords (words item)) := by
  induction items with
  | nil => rfl
  | cons item items ih => simp [encodeWords_append, ih]

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.EmitRows

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_Setup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Setup

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad

variable {K Λ σ : Type} [DecidableEq K]

def resultTapes (ports : Ports K) (base : K → List Bool)
    (n m : Nat) (rows : List Bool) : K → List Bool :=
  Function.update
    (Function.update
      (Function.update
        (Function.update (Function.update base (ports 1) rows)
          (ports 2) (encodeWord n)) (ports 3) (encodeWord m))
      (ports 4) (encodeWord m)) (ports 6) (encodeWord 0)

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Setup

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_Body
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
One actual iteration of the alphabet-table driver. The positive unary guard,
row parser, preserving head lookup, comparison, finite emission plan, three
drains, and unary index increment all execute inside `Driver.program`.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Body

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

def bodyTime (q N : Nat) : Nat :=
  (32 + 8 * (Enumeration.localCount q * (6 * (2 * 4104)))) * (N + 1)

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Body

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_LoopInitializationLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
The concrete tapes produced by initialization satisfy the row-zero loop
invariant. Execution of initialization is proved separately by
`Initialization.initializeInTime`; this bridge identifies its resulting tapes.
-/



namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Loop


open Turing
open UniqueGamesTheorem.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

/-- A quadratic prefix allowance because the number of original rows is at
most the length of their fully encoded input table. -/
def prefixTime (q N : Nat) : Nat :=
  Initialization.time N + N * Body.bodyTime q N + 1

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Loop



namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Runtime

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open RuntimeModel


noncomputable def prefixPolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C 27 * Polynomial.X + Polynomial.C 54 +
    Polynomial.X *
      (Polynomial.C (32 + 8 * (Enumeration.localCount q * (6 * (2 * 4104)))) *
        (Polynomial.X + Polynomial.C 1)) + Polynomial.C 1

theorem prefixPolynomial_eval (q N : Nat) :
    (prefixPolynomial q).eval N = Loop.prefixTime q N := by
  simp only [prefixPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Loop.prefixTime,
    Initialization.time, Body.bodyTime]
  ring

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Runtime



/-! Every work tape of the actual alphabet-table machine stores Bool symbols.
This checks the work alphabets separately from the finite-machine structure's
input-alphabet condition, without changing the runtime certificate. -/



/-! The actual padding, expander overlay, and lazy-loop stages composed into
one polynomial-time finite machine. The initial degree-replacement stage is
assembled separately. -/
namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingFinishRuntime

open Turing UniqueGamesTheorem.Foundations.Complexity
open PreprocessingRegularTables

theorem finish_degree_positive (d : Nat) (hd : 0 < d) : 0 < d + internalDegree :=
  hd.trans_le (Nat.le_add_right d internalDegree)

end UniqueGamesTheorem.Foundations.PCP.PreprocessingFinishRuntime



/-! The complete actual preprocessing machine, including degree replacement,
vertex padding, explicit expander construction, overlay, and lazy edges. -/



/-!
Actual sequential finite-machine composition for the concrete numbered round.
The initial composition lemma isolates the preprocessing and powering execution
certificates with their shared bit codecs. The final endpoint supplies the
checked powering and alphabet machines, leaving only preprocessing explicit.
-/

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_NormalizationEmitMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.NormalizationEmitMachine


open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer
open UniqueGamesTheorem.Reduction.MachineSubstitution
open NormalizationWords

variable {K Λ A : Type} [DecidableEq K]

def emitSign (output : K) (sign : SignRef) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .branch (fun state => signValue state.1.2 sign)
    (.push output (fun _ => true)
      (.push output (fun _ => false) (exitAt output exit)))
    (.push output (fun _ => false) (exitAt output exit))

end PerfectCompleteness.NormalizationEmitMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourceOccurrenceIndexMachine
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec.decodeWords_encodeWord _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter.counterTapes_counter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceOccurrenceIndexMachine


open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

variable {K Λ A : Type} [DecidableEq K]

def instruction (tape : Fin 3 → K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .copyOut => loopAt (tape 0) (tape 1) id false
      (labels .copyOut) (some (labels .copyBack))
  | .copyBack => MachineCopy.forkLoop (tape 1) (tape 0) (tape 2) false
      (labels .copyBack) (some (labels .delimiter))
  | .delimiter => .push (tape 2) (fun _ => false) (exitAt (tape 2) exit)

theorem indexTrace (tape : Fin 3 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction tape labels exit l)
    (base : K → List Bool) (ambient : A) (index : Nat)
    (counterWord : base (tape 0) = List.replicate index true)
    (scratchEmpty : base (tape 1) = []) :
    (advance (TM2.step program))^[steps index]
      (some ⟨some (labels main), clean ambient, base⟩) =
      some ⟨exit, clean ambient, Function.update base (tape 2)
        ((encodeWord index).reverse ++ base (tape 2))⟩ := by
  have hd (i j : Fin 3) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have copied := MachineCopy.copyTrace (tape 0) (tape 2) (tape 1)
    (hd 0 2 (by decide)) (hd 0 1 (by decide)) (hd 2 1 (by decide)) false
    (labels .copyOut) (labels .copyBack) (some (labels .delimiter)) program
    (atLabels .copyOut) (atLabels .copyBack) base scratchEmpty ambient none
  rw [counterWord, List.length_replicate] at copied
  have emitted : (advance (TM2.step program))^[1]
      (some ⟨some (labels .delimiter), clean ambient,
        Function.update base (tape 2) (List.replicate index true ++ base (tape 2))⟩) =
      some ⟨exit, clean ambient, Function.update base (tape 2)
        ((encodeWord index).reverse ++ base (tape 2))⟩ := by
    change some (TM2.stepAux (program (labels .delimiter)) _ _) = _
    rw [atLabels .delimiter]
    cases exit <;>
      simp [instruction, TM2.stepAux, exitAt, encodeWord, List.reverse_append,
        List.reverse_replicate]
  exact joinTrace copied emitted

end PerfectCompleteness.SourceOccurrenceIndexMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourceOccurrenceLoopMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceOccurrenceLoopMachine


open Turing
open UniqueGamesTheorem.Foundations
open Complexity Complexity.MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

section Program

variable {K Λ A : Type} [DecidableEq K]

theorem loopTapes_remaining (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input : List Bool) (remaining first : Nat) (output : List Bool) :
    loopTapes tape base input remaining first output (tape 1) = List.replicate remaining true := by
  have hd (i j : Fin 5) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  simp [loopTapes, hd]

theorem update_remaining (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input : List Bool) (remaining first replacement : Nat)
    (output : List Bool) :
    Function.update (loopTapes tape base input remaining first output)
        (tape 1) (List.replicate replacement true) =
      loopTapes tape base input replacement first output := by
  have hd (i j : Fin 5) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 1
  · subst k; simp [loopTapes, hd]
  · simp [loopTapes, h, Function.update_apply]

end Program

end PerfectCompleteness.SourceOccurrenceLoopMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_ExactTargetOdometer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.ExactTargetOdometer


open UniqueGamesTheorem.Foundations.Complexity
open scoped Classical

noncomputable section

variable {width radix : Nat}

theorem setCoordinate_zero (digits : Fin width → Fin radix) (depth : Nat)
    (positive : 0 < radix) (zero : ∀ i, i.val = depth → (digits i).val = 0) :
    setCoordinate digits depth ⟨0, positive⟩ = digits := by
  funext i
  by_cases same : i.val = depth
  · simp only [setCoordinate, ite_eq_left same]
    apply Fin.ext
    exact (zero i same).symm
  · simp [setCoordinate, same]

end

end PerfectCompleteness.ExactTargetOdometer

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_TargetHeaderMachine
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec.decodeWords_encodeWord _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter.counterTapes_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.TargetHeaderMachine


open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer (loopAt exitAt)
open UniqueGamesTheorem.Reduction.MachineSubstitution

variable {K Λ A : Type} [DecidableEq K]

def instruction (q : Nat) (tape : Fin 3 → K) (labels : Label → Λ)
    (done : Option Λ) : Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .copyLast => loopAt (tape 0) (tape 1) id false (labels .copyLast)
      (some (labels .restoreLast))
  | .restoreLast => MachineCopy.forkLoop (tape 1) (tape 0) (tape 2) false
      (labels .restoreLast) (some (labels .pushAlphabet))
  | .pushAlphabet => pushWord (tape 2) (encodeWord q).reverse
      (.goto fun _ => labels .copyRight)
  | .copyRight => loopAt (tape 0) (tape 1) id false (labels .copyRight)
      (some (labels .restoreRight))
  | .restoreRight => MachineCopy.forkLoop (tape 1) (tape 0) (tape 2) false
      (labels .restoreRight) (some (labels .copyLeft))
  | .copyLeft => loopAt (tape 0) (tape 1) id false (labels .copyLeft)
      (some (labels .restoreLeft))
  | .restoreLeft => MachineCopy.forkLoop (tape 1) (tape 0) (tape 2) false
      (labels .restoreLeft) done

theorem pushAlphabetStep (q : Nat) (tape : Fin 3 → K) (labels : Label → Λ)
    (done : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabel : program (labels .pushAlphabet) = instruction q tape labels done .pushAlphabet)
    (base : K → List Bool) (ambient : A) (register : Option Bool) :
    TM2.step program ⟨some (labels .pushAlphabet), (ambient, register), base⟩ =
      some ⟨some (labels .copyRight), (ambient, register),
        Function.update base (tape 2) (encodeWord q ++ base (tape 2))⟩ := by
  change some (TM2.stepAux (program (labels .pushAlphabet)) (ambient, register) base) = _
  rw [atLabel]
  simp only [instruction, stepAux_pushWord, List.reverse_reverse, TM2.stepAux]

theorem headerTrace (q : Nat) (tape : Fin 3 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (done : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, program (labels label) = instruction q tape labels done label)
    (base : K → List Bool) (N : Nat) (sourceWord : base (tape 0) = encodeWord N)
    (scratchEmpty : base (tape 1) = []) (ambient : A) (register : Option Bool) :
    (advance (TM2.step program))^[6 * (N + 2) + 1]
      (some ⟨some (labels main), (ambient, register), base⟩) =
      some ⟨done, (ambient, none),
        Function.update base (tape 2) (encodeWords [N, N, q, N] ++ base (tape 2))⟩ := by
  have h02 : tape 0 ≠ tape 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (distinct h)
  have h01 : tape 0 ≠ tape 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (distinct h)
  have h21 : tape 2 ≠ tape 1 := fun h => (by decide : (2 : Fin 3) ≠ 1) (distinct h)
  let firstTapes := Function.update base (tape 2) (encodeWord N ++ base (tape 2))
  let literalTapes := Function.update firstTapes (tape 2)
    (encodeWord q ++ firstTapes (tape 2))
  let secondTapes := Function.update literalTapes (tape 2)
    (encodeWord N ++ literalTapes (tape 2))
  have first := MachineCopy.copyTrace (tape 0) (tape 2) (tape 1) h02 h01 h21 false
    (labels .copyLast) (labels .restoreLast) (some (labels .pushAlphabet)) program
    (atLabels .copyLast) (atLabels .restoreLast) base scratchEmpty ambient register
  rw [sourceWord, encodeWord_length] at first
  have literal : (advance (TM2.step program))^[1]
      (some ⟨some (labels .pushAlphabet), (ambient, none), firstTapes⟩) =
      some ⟨some (labels .copyRight), (ambient, none), literalTapes⟩ := by
    exact pushAlphabetStep q tape labels done program (atLabels .pushAlphabet)
      firstTapes ambient none
  have literalSource : literalTapes (tape 0) = encodeWord N := by
    simp [literalTapes, firstTapes, h02, sourceWord]
  have literalScratch : literalTapes (tape 1) = [] := by
    simp [literalTapes, firstTapes, Ne.symm h21, scratchEmpty]
  have second := MachineCopy.copyTrace (tape 0) (tape 2) (tape 1) h02 h01 h21 false
    (labels .copyRight) (labels .restoreRight) (some (labels .copyLeft)) program
    (atLabels .copyRight) (atLabels .restoreRight) literalTapes literalScratch ambient none
  rw [literalSource, encodeWord_length] at second
  have secondSource : secondTapes (tape 0) = encodeWord N := by
    simp [secondTapes, h02, literalSource]
  have secondScratch : secondTapes (tape 1) = [] := by
    simp [secondTapes, Ne.symm h21, literalScratch]
  have third := MachineCopy.copyTrace (tape 0) (tape 2) (tape 1) h02 h01 h21 false
    (labels .copyLeft) (labels .restoreLeft) done program
    (atLabels .copyLeft) (atLabels .restoreLeft) secondTapes secondScratch ambient none
  rw [secondSource, encodeWord_length] at third
  have all := joinTrace (joinTrace (joinTrace first literal) second) third
  have count : ((2 * (N + 1 + 1) + 1) + 2 * (N + 1 + 1)) +
      2 * (N + 1 + 1) = 6 * (N + 2) + 1 := by omega
  rw [count] at all
  simpa only [main, secondTapes, literalTapes, firstTapes,
    Function.update_self, Function.update_idem, encodeWords, List.append_nil,
    List.append_assoc] using all

def headerInTime (q : Nat) (tape : Fin 3 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (done : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, program (labels label) = instruction q tape labels done label)
    (base : K → List Bool) (N : Nat) (sourceWord : base (tape 0) = encodeWord N)
    (scratchEmpty : base (tape 1) = []) (ambient : A) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels main), (ambient, register), base⟩
      (some ⟨done, (ambient, none),
        Function.update base (tape 2) (encodeWords [N, N, q, N] ++ base (tape 2))⟩)
      (6 * (N + 2) + 1) where
  steps := 6 * (N + 2) + 1
  evals_in_steps := headerTrace q tape distinct labels done program atLabels base N
    sourceWord scratchEmpty ambient register
  steps_le_m := Nat.le_refl _

@[simp] theorem encodeWord_zero : encodeWord 0 = [false] := rfl

end PerfectCompleteness.TargetHeaderMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_TargetFinalizeMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.TargetFinalizeMachine


open Turing UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Reduction.MachineTransfer
open MachineComposition

variable {K Λ A : Type} [DecidableEq K] {stackCount : Nat}

abbrev WorkLabel (enumeration : Fin stackCount ≃ K) (output : K) :=
  MachineDrainMany.Label (MachineDrainMany.workTapes enumeration output)

abbrev Labels (enumeration : Fin stackCount ≃ K) (output : K) :=
  Label (WorkLabel enumeration output)

def headerTapes (q count : Nat) (tape : Fin 4 → K) (base : K → List Bool)
    (body : List Bool) : K → List Bool :=
  Function.update (bodyTapes tape base body) (tape 3)
    (encodeWords [count, count, q, count] ++ body)

end PerfectCompleteness.TargetFinalizeMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_TargetTapeEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.TargetTapeEnvelope

def bound (w q T E : Nat) : Nat :=
  T + 1 + CanonicalDictionaryNames.streamBound w T E +
    outputBound q E + (E + 1)

theorem bound_le (w q D T E : Nat) (hcount : E ≤ D * (T + 1) ^ w) :
    bound w q T E ≤ coeff w q D * (T + 1) ^ (2 * w + 2) := by
  have hone : 1 ≤ (T + 1) ^ (2 * w + 2) :=
    Nat.one_le_pow (2 * w + 2) (T + 1) (Nat.zero_lt_succ T)
  have hinput : T + 1 ≤ (T + 1) ^ (2 * w + 2) :=
    Nat.le_pow (show 0 < 2 * w + 2 by omega)
  have hcountLinear : E ≤ D * (T + 1) ^ (2 * w + 2) :=
    hcount.trans (Nat.mul_le_mul_left D
      (Nat.pow_le_pow_right (Nat.zero_lt_succ T) (by omega)))
  have hstream : CanonicalDictionaryNames.streamBound w T E ≤
      SignedCostEnvelope.streamCoeff w D * (T + 1) ^ (2 * w + 2) := by
    calc
      CanonicalDictionaryNames.streamBound w T E ≤
          CanonicalDictionaryNames.streamBound w T (D * (T + 1) ^ w) :=
        Nat.mul_le_mul_left _ hcount
      _ ≤ SignedCostEnvelope.streamCoeff w D * (T + 1) ^ (w + 1) :=
        SignedCostEnvelope.streamBound_le w D T
      _ ≤ SignedCostEnvelope.streamCoeff w D * (T + 1) ^ (2 * w + 2) :=
        Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (Nat.zero_lt_succ T) (by omega))
  have hsquare : E ^ 2 ≤ D ^ 2 * (T + 1) ^ (2 * w + 2) := by
    calc
      E ^ 2 ≤ (D * (T + 1) ^ w) ^ 2 := Nat.pow_le_pow_left hcount 2
      _ = D ^ 2 * (T + 1) ^ (w * 2) := by rw [Nat.mul_pow, ← Nat.pow_mul]
      _ ≤ D ^ 2 * (T + 1) ^ (2 * w + 2) :=
        Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (Nat.zero_lt_succ T) (by omega))
  calc
    bound w q T E = (T + 1) + CanonicalDictionaryNames.streamBound w T E +
        2 * E ^ 2 + (2 * q * q + 2 * q + 6) * E + (q + 5) := by
      unfold bound outputBound
      ring
    _ ≤ (T + 1) ^ (2 * w + 2) +
        SignedCostEnvelope.streamCoeff w D * (T + 1) ^ (2 * w + 2) +
        2 * (D ^ 2 * (T + 1) ^ (2 * w + 2)) +
        (2 * q * q + 2 * q + 6) * (D * (T + 1) ^ (2 * w + 2)) +
        (q + 5) * (T + 1) ^ (2 * w + 2) :=
      Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add (Nat.add_le_add hinput hstream) (Nat.mul_le_mul_left 2 hsquare))
          (Nat.mul_le_mul_left (2 * q * q + 2 * q + 6) hcountLinear))
        (le_scaled (q + 5) hone)
    _ = coeff w q D * (T + 1) ^ (2 * w + 2) := by
      unfold coeff
      ring

end PerfectCompleteness.TargetTapeEnvelope

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_TargetFinalizeBound
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.TargetFinalizeBound

open Turing UniqueGamesTheorem.Foundations.Complexity
open TargetFinalizeMachine

variable {K Λ A : Type} [DecidableEq K] {stackCount : Nat}

theorem header_length (q count : Nat) (body : List Bool) :
    (encodeWords [count, count, q, count] ++ body).length =
      3 * (count + 1) + (q + 1) + body.length := by
  simp only [encodeWords, List.length_append, encodeWord_length, List.length_nil]
  omega

theorem headerTapes_length_le (q count : Nat) (tape : Fin 4 → K)
    (base : K → List Bool) (body : List Bool) (B : Nat)
    (bounded : ∀ k, (base k).length ≤ B) (bodyBound : body.length ≤ B)
    (countBound : count ≤ B) :
    ∀ k, (headerTapes q count tape base body k).length ≤ 4 * B + q + 4 := by
  intro k
  by_cases output : k = tape 3
  · subst k
    simp only [headerTapes, Function.update_self, header_length]
    omega
  · by_cases accumulator : k = tape 0
    · subst k
      simp [headerTapes, bodyTapes, output]
    · have hk := bounded k
      simp only [headerTapes, bodyTapes, Function.update_of_ne output,
        Function.update_of_ne accumulator]
      omega

end PerfectCompleteness.TargetFinalizeBound

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_RestrictionRowsLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.OutputAnnihilator.mem_bad _root_.OAI.PerfectCompleteness.TensorProjectedSlice.totalMatrix_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.RestrictionRowsLaw

noncomputable section

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

variable {E C I : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup C] [Module F2 C] [Fintype I]
  (W : Submodule F2 E) (C' : Submodule F2 C) (b : Module.Basis I F2 C')

def rowsLinear : Parameter W C' →ₗ[F2] (I → Module.Dual F2 (E ⧸ W)) where
  toFun A i := (b.coord i).comp A
  map_add' A B := by
    funext i
    apply LinearMap.ext
    intro x
    exact map_add (b.coord i) (A x) (B x)
  map_smul' a A := by
    funext i
    apply LinearMap.ext
    intro x
    exact map_smul (b.coord i) a (A x)

omit [Fintype I] in
@[simp] theorem rowsLinear_apply (A : Parameter W C') (i : I) :
    rowsLinear W C' b A i = (b.coord i).comp A := rfl

def fromRows (rows : I → Module.Dual F2 (E ⧸ W)) : Parameter W C' :=
  b.equivFun.symm.toLinearMap.comp (LinearMap.pi rows)

@[simp] theorem rowsLinear_fromRows (rows : I → Module.Dual F2 (E ⧸ W)) :
    rowsLinear W C' b (fromRows W C' b rows) = rows := by
  funext i
  apply LinearMap.ext
  intro x
  exact b.coord_equivFun_symm i (fun j => rows j x)

section Selection

variable {J : Type*} (sel : J → I)

def selectLinear : (I → Module.Dual F2 (E ⧸ W)) →ₗ[F2]
    (J → Module.Dual F2 (E ⧸ W)) :=
  LinearMap.pi (fun j => LinearMap.proj (sel j))

def selectedRowsLinear : Parameter W C' →ₗ[F2] (J → Module.Dual F2 (E ⧸ W)) :=
  (selectLinear W sel).comp (rowsLinear W C' b)

end Selection

end
end PerfectCompleteness.RestrictionRowsLaw

end OAI
end


