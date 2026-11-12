-- Prove2me | Definitions.Def_OAIQ252P009
-- name    : OAIQ252P009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T07:40:13.475638+00:00
-- url     : https://prove2.me/theorems/6e12ebc8-99d0-43c5-bd8e-06e759a7b547
-- title:
--   Definitions bundle OAIQ252P009 of the split of OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 602 declarations of OpenAI's Lean: 235 definitions, 14 inductive types or structures and 353 theorems. The definitions and types are `OAI.PerfectCompleteness.FiniteListSampling.pairAcceptance`, `OAI.PerfectCompleteness.FiniteProductSplit.otherLaw`, `OAI.PerfectCompleteness.FiniteRangeInverse.agreement`, `OAI.PerfectCompleteness.FixedUnaryRepresentationPlacement.familyInTime`, `OAI.PerfectCompleteness.OriginalChildScalars.callsLaw`, `OAI.PerfectCompleteness.PCPSource.baseDenominator`, `OAI.PerfectCompleteness.PCPSource.sourceDenominator`, `OAI.PerfectCompleteness.PCPSource.sourceGap`, `OAI.PerfectCompleteness.SignedRuntimeBounds.KeyBound`, `OAI.PerfectCompleteness.SignedRuntimeBounds.KeysBound`, `OAI.PerfectCompleteness.SourceOddLists.alphabetLog`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCanonicalOutput.TerminalRun`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCanonicalOutput.completedMachine`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCanonicalOutput.completedProgram`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCanonicalOutput.completedTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCanonicalOutput.embeddedCfg`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCloudCount.tableRows`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCloudPadding.padding`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCloudPadding.subtractLoop`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCloudPadding.totalTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCloudPrefix.amount`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCloudPrefix.bodyTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCloudPrefix.cycleTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCloudPrefix.loopTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCloudPrefix.sumFrom`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCloudPrefix.totalTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCloudSelect.cloudSelectSteps`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCloudSelect.program`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCloudSelect.remainder`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineDrainMany.haltTapes`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.LevelLoopRun`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.ResizeRun`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.affinePhaseInTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.affineResultTapes`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.cleanedCounterTapes`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.cleanupCountersInTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.copyCountInTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.copyFrame`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.familyInTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.installTableInTime` and 209 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `PerfectCompleteness_Construction_OriginalChildScalars`, `PerfectCompleteness_Foundations_FiniteRangeInverse`, `PerfectCompleteness_Foundations_PCPSource`, `PerfectCompleteness_Foundations_QuarterBalanceLemmas`, `PerfectCompleteness_Foundations_SourceOddListsLemmas`, `PerfectCompleteness_Foundations_SourceTupleData`, `PerfectCompleteness_Foundations_TerminalCalls`, `PerfectCompleteness_Machines_ExactTargetOnlineEncoding`, `PerfectCompleteness_Machines_FixedUnaryRepresentationMachine`, `PerfectCompleteness_Machines_NormalizationReadMachine`, `PerfectCompleteness_Machines_SignedRuntimeBounds`, `PerfectCompleteness_Reduction_CompletionLemmas`, `PerfectCompleteness_Sampling_FiniteListSampling`, `UniqueGames_Games_FactorizationLemmas`, `UniqueGames_Machines_FinalCNFStream`, `UniqueGames_Machines_MachineCanonicalOutputLemmas`, `UniqueGames_Machines_MachineCloudCount`, `UniqueGames_Machines_MachineCloudPadding`, `UniqueGames_Machines_MachineCloudPrefix`, `UniqueGames_Machines_MachineCloudRankLemmas`, `UniqueGames_Machines_MachineDrainManyLemmas`, `UniqueGames_Machines_MachineExpanderFamily`, `UniqueGames_Machines_MachineExpanderFamilyBoundsLemmas`, `UniqueGames_Machines_MachineExpanderFamilyLoop`, `UniqueGames_Machines_MachineExpanderFamilyTapes`, `UniqueGames_Machines_MachineExpanderFamilyTransferLemmas`, `UniqueGames_Machines_MachineExpanderRow`, `UniqueGames_Machines_MachineExpanderRowCleanup`, `UniqueGames_Machines_MachineExpanderRowDivision`, `UniqueGames_Machines_MachineExpanderRowEmitLemmas`, `UniqueGames_Machines_MachineExpanderRowFrames`, `UniqueGames_Machines_MachineExpanderTable`, `UniqueGames_Machines_MachineExpanderTableLoop`, `UniqueGames_Machines_MachineExpanderTableProgramLemmas`, `UniqueGames_Machines_MachineExpanderTableReverse`, `UniqueGames_Machines_MachineExpanderTableRows`, `UniqueGames_Machines_MachineFixedDivMod`, `UniqueGames_Machines_MachineLazyRows`, `UniqueGames_Machines_MachineLookupLemmas`, `UniqueGames_Machines_MachinePaddedExpanderFamilyBoundsLemmas`, `UniqueGames_Machines_MachinePaddedOverlayRuntimeLemmas`, `UniqueGames_Machines_MachineProductGatherBoundsLemmas`, `UniqueGames_Machines_MachineRegularDummyRow`, `UniqueGames_Machines_MachineRegularFamily`, `UniqueGames_Machines_MachineRegularInternalRow`, `UniqueGames_Machines_MachineRegularLift`, `UniqueGames_Machines_MachineRegularMetadata`, `UniqueGames_Machines_MachineRegularOriginalBody`, `UniqueGames_Machines_MachineRegularOriginalBodyBounds`, `UniqueGames_Machines_MachineRegularOriginalClean`, `UniqueGames_Machines_MachineRegularOriginalRow`, `UniqueGames_Machines_MachineRegularOwnerBody`, `UniqueGames_Machines_MachineRegularOwnerBodyBounds`, `UniqueGames_Machines_MachineRegularOwnerProgram`, `UniqueGames_Machines_MachineRegularTable`, `UniqueGames_Machines_MachineRegularTableBoundsLemmas`, `UniqueGames_Machines_MachineRegularVertexBlock`, `UniqueGames_Machines_MachineTransducerCopy`, `UniqueGames_Machines_MachineTupleOdometer`, `UniqueGames_Machines_MachineUnaryAffineAt`, `UniqueGames_Machines_MachineUnaryLessAtLemmas`, `UniqueGames_PCP_Emitter`, `UniqueGames_PCP_ExpanderRowControlLemmas`, `UniqueGames_PCP_ExpanderTableEnumeration`, `UniqueGames_PCP_PreprocessingInternalRows`, `UniqueGames_PCP_PreprocessingPaddingOffsets`, `UniqueGames_PCP_PreprocessingPaddingTables`, `UniqueGames_PCP_PreprocessingPaddingWords`, `UniqueGames_PCP_PreprocessingRegularTablesLemmas`, `UniqueGames_PCP_PreprocessingRegularWords`.
--
--   **Imports.** It imports the published bundle `Def_PerfectCompleteness`; the bundles `OAIQ252P003`, `OAIQ252P004` and `OAIQ252P005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ252P012`, `OAIQ252P013`, `OAIQ252P014` and `OAIQ252P015`; the proof of `OAI.PerfectCompleteness.BucketQuotientAgreement.agreement_eq_nonzeroAgreement`.
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
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
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
import Mathlib.LinearAlgebra.TensorProduct.Basic
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
import Definitions.Def_OAIQ252P003
import Definitions.Def_OAIQ252P004
import Definitions.Def_OAIQ252P005

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_QuarterBalanceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.FiniteProductSplit

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

def otherLaw (P : (i : I) → FiniteDistribution (Ω i)) (i : I) :
    FiniteDistribution (Others (Ω := Ω) i) :=
  FiniteProduct.law (fun j : {j : I // j ≠ i} => P j.val)

end
end PerfectCompleteness.FiniteProductSplit

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_FactorizationLemmas
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Repetition

@[simp] theorem logTwo_one : logTwo 1 = 0 := by simp [logTwo]

end UniqueGamesTheorem.Foundations.Repetition

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

namespace UniqueGamesTheorem.Foundations.Complexity.MachineDrainMany

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

theorem steps_le_uniform (chosen : List K) (base : Tapes K) (bound : Nat)
    (h : ∀ k, (base k).length ≤ bound) :
    steps chosen base ≤ chosen.length * (bound + 1) := by
  have hsum : lengthSum chosen base ≤ chosen.length * bound := by
    induction chosen with
    | nil => simp [lengthSum]
    | cons source chosen ih =>
        simp only [lengthSum, List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul,
          Nat.one_mul] at ih ⊢
        have hs := h source
        omega
  have hc := steps_le chosen base
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- The tape component of the actual halted configuration: only output remains. -/
def haltTapes (output : K) (word : List Bool) : Tapes K :=
  fun k => if k = output then word else []

end UniqueGamesTheorem.Foundations.Complexity.MachineDrainMany

/-!
Preserved comparisons of actual field stacks and their finite equality profile.
All whole-word equalities below are specifications of finite-head comparison.
-/

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_FixedUnaryRepresentationMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.FixedUnaryRepresentationMachine


open Turing UniqueGamesTheorem.Foundations.Complexity
open MachineComposition

variable {width : Nat} {Λ A : Type}

theorem sequenceTrace (mode : Mode) (values : Fin width → Nat) (positions : List (Fin width))
    (labels : Label mode positions → Λ) (done : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (width := width)) Λ (State A))
    (atLabels : ∀ label, program (labels label) = instruction mode positions labels done label)
    (destinations : Fin width → List Bool) (ambient : A) :
    (advance (TM2.step program))^[steps mode values positions]
      (some ⟨entry mode positions labels done, (ambient, none), «stacks» mode values destinations⟩) =
      some ⟨done, (ambient, none), «stacks» mode values (result mode values positions destinations)⟩ := by
  have run := MachineFiniteSequence.trace
    (LocalLabel := fun _ : Fin width => LocalLabel mode) (main := fun _ => localMain mode)
    (localInstruction := localInstruction mode) (result := update mode values)
    (cost := fun position _ => cost mode (values position)) program
    (fun _ : Fin width → List Bool => True) (fun _ => (ambient, none)) («stacks» mode values)
    positions (by intros; trivial)
    (by
      intro position _ localLabels localExit atLocal destinationWords _
      exact localTrace mode values position localLabels localExit program atLocal destinationWords ambient)
    labels done atLabels destinations trivial
  simpa only [sequence_steps, entry, result] using run

theorem familyTrace (mode : Mode) (values : Fin width → Nat)
    (labels : Label mode (List.finRange width) → Λ) (done : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (width := width)) Λ (State A))
    (atLabels : ∀ label, program (labels label) =
      instruction mode (List.finRange width) labels done label)
    (destinations : Fin width → List Bool) (ambient : A) :
    (advance (TM2.step program))^[steps mode values (List.finRange width)]
      (some ⟨entry mode (List.finRange width) labels done, (ambient, none),
        «stacks» mode values destinations⟩) =
      some ⟨done, (ambient, none), «stacks» mode values
        (fun position => targetWord mode (values position) ++ destinations position)⟩ := by
  simpa only [result_finRange] using
    sequenceTrace mode values (List.finRange width) labels done program atLabels destinations ambient

end PerfectCompleteness.FixedUnaryRepresentationMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineCloudCount
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_append _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_nil _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_nil _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_done _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_head _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_relation _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_reverseIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_words _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRows_acceptsAt _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRows_get _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRows_reverseAt _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_headIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_headValue _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_relation _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_reverseIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_row _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_head _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tableBits _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tableWords _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_vertices _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.build_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.build_vertices _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.rowList_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.rows_at _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_internal _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.vertexOrder_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.vertexOrder_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCloudCount

open Turing
open MachineComposition

variable {Λ σ : Type}

open UniqueGamesTheorem.Foundations.PCP

def tableRows (t : GraphTables.Table) : List Row :=
  (GraphTables.rowList t).map (fun r =>
    (r.tail.val, r.reverseIndex.val :: GraphTables.relationWords r.relation))

theorem tableRows_width (t : GraphTables.Table) :
    ∀ r ∈ tableRows t, r.2.length = 4097 := by
  intro r hr
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
  simp [GraphTables.relationWords]

theorem tableRows_words (t : GraphTables.Table) :
    (tableRows t).flatMap rowWords = (GraphTables.rowList t).flatMap GraphTables.rowWords := by
  simp only [tableRows, List.flatMap_map]
  apply congrArg (fun f => (GraphTables.rowList t).flatMap f)
  funext r
  rfl

theorem tableRows_input (t : GraphTables.Table) :
    inputWord t.vertices t.darts (tableRows t) = GraphTables.tableBits t := by
  rw [inputWord, tableRows_words]
  rfl

theorem rowList_eq_finRange_map (t : GraphTables.Table) :
    GraphTables.rowList t = (List.finRange t.darts).map (fun e => t.rows[e]) := by
  apply List.ext_getElem
  · simp [GraphTables.rowList]
  · intro i hi hj
    simp [GraphTables.rowList]

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

variable {σ : Type}

def subtractLoop : TM2.Stmt Alphabet Label (State σ) :=
  .pop .count (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.pop .power (fun state _ => (state.1, none))
        (.push .scratch (fun _ => true) (.goto fun _ => .subtract)))
      (.push .count (fun _ => false)
        (.load (fun state => (state.1, none)) (.goto fun _ => .restore))))

def padding (k : Nat) : Nat := PreprocessingLevels.cloudPaddedSize k - k

def totalTime (t : GraphTables.Table) (v : Fin t.vertices) : Nat :=
  (1 + MachineCloudCount.totalSteps t.vertices t.darts v.val (MachineCloudCount.tableRows t)) +
    postTime (PreprocessingCloudIndex.cloudSize t v)

end UniqueGamesTheorem.Foundations.Complexity.MachineCloudPadding

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_CompletionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.FixedUnaryRepresentationPlacement


open Turing UniqueGamesTheorem.Foundations.Complexity
open MachineComposition MachineCloudPadding

variable {width : Nat} {K Λ A : Type}

variable [DecidableEq K]

theorem familyTrace (mode : Mode) (tape : Tape width → K) (view : K → Option (Tape width))
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Label mode width → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, program (labels label) = instruction mode tape labels exit label)
    (extra : K → List Bool) (values : Fin width → Nat)
    (destinations : Fin width → List Bool) (ambient : A) :
    (advance (TM2.step program))^[FixedUnaryRepresentationMachine.steps mode values (List.finRange width)]
      (some ⟨entry mode labels exit, (ambient, none), tapes view extra mode values destinations⟩) =
      some ⟨exit, (ambient, none), tapes view extra mode values
        (fun position => FixedUnaryRepresentationMachine.targetWord mode (values position) ++
          destinations position)⟩ := by
  have native := FixedUnaryRepresentationMachine.familyTrace mode values id none
    (nativeProgram (width := width) (A := A) mode) (fun _ => rfl) destinations ambient
  have placed := Placement.trace tape view left right labels exit extra
    (nativeProgram (width := width) (A := A) mode) program atLabels _ _ _ native
  simpa only [Placement.configuration, Placement.label, entry, tapes] using placed

def familyInTime (mode : Mode) (tape : Tape width → K) (view : K → Option (Tape width))
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Label mode width → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, program (labels label) = instruction mode tape labels exit label)
    (extra : K → List Bool) (values : Fin width → Nat)
    (destinations : Fin width → List Bool) (ambient : A)
    (maximum : Nat) (bounded : ∀ position, values position ≤ maximum) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry mode labels exit, (ambient, none), tapes view extra mode values destinations⟩
      (some ⟨exit, (ambient, none), tapes view extra mode values
        (fun position => FixedUnaryRepresentationMachine.targetWord mode (values position) ++
          destinations position)⟩)
      (width * (2 * maximum + 3)) where
  steps := FixedUnaryRepresentationMachine.steps mode values (List.finRange width)
  evals_in_steps := familyTrace mode tape view left right labels exit program atLabels extra
    values destinations ambient
  steps_le_m := by
    simpa only [List.length_finRange] using
      FixedUnaryRepresentationMachine.steps_le mode values (List.finRange width) maximum bounded

end PerfectCompleteness.FixedUnaryRepresentationPlacement



end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineTupleOdometer
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCompare.compareInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt.transferLeft_tapes _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt.transferRight_tapes _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineTupleOdometer

open Turing
open Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K]

theorem stepAux_increment_succ (current remaining : K) (distinct : current ≠ remaining)
    (doneLabel resetLabel : Λ) (base : K → List Bool) (d r : ℕ)
    (currentSuffix remainingSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (increment current remaining doneLabel resetLabel) (ambient, register)
      (digitTapes current remaining base d (r + 1) currentSuffix remainingSuffix) =
      ⟨some doneLabel, (ambient, none),
        digitTapes current remaining base (d + 1) r currentSuffix remainingSuffix⟩ := by
  simp [increment, TM2.stepAux, digitTapes, MachineUnaryAddAt.unaryTapes,
    distinct, encodeWord, List.replicate_succ, update_current, update_remaining]

theorem stepAux_increment_zero (current remaining : K) (distinct : current ≠ remaining)
    (doneLabel resetLabel : Λ) (base : K → List Bool) (d : ℕ)
    (currentSuffix remainingSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (increment current remaining doneLabel resetLabel) (ambient, register)
      (digitTapes current remaining base d 0 currentSuffix remainingSuffix) =
      ⟨some resetLabel, (ambient, none),
        digitTapes current remaining base d 0 currentSuffix remainingSuffix⟩ := by
  simp [increment, TM2.stepAux, digitTapes, MachineUnaryAddAt.unaryTapes,
    distinct, encodeWord]

/-- A non-carrying digit increment is one actual ambient-program transition. -/
theorem incrementStep_succ (current remaining : K) (distinct : current ≠ remaining)
    (checkLabel doneLabel resetLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atCheck : program checkLabel = increment current remaining doneLabel resetLabel)
    (base : K → List Bool) (d r : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some checkLabel, (ambient, register),
      digitTapes current remaining base d (r + 1) currentSuffix remainingSuffix⟩ =
      some ⟨some doneLabel, (ambient, none),
        digitTapes current remaining base (d + 1) r currentSuffix remainingSuffix⟩ := by
  change some (TM2.stepAux (program checkLabel) (ambient, register) _) = _
  rw [atCheck, stepAux_increment_succ current remaining distinct]

theorem incrementStep_zero (current remaining : K) (distinct : current ≠ remaining)
    (checkLabel doneLabel resetLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atCheck : program checkLabel = increment current remaining doneLabel resetLabel)
    (base : K → List Bool) (d : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some checkLabel, (ambient, register),
      digitTapes current remaining base d 0 currentSuffix remainingSuffix⟩ =
      some ⟨some resetLabel, (ambient, none),
        digitTapes current remaining base d 0 currentSuffix remainingSuffix⟩ := by
  change some (TM2.stepAux (program checkLabel) (ambient, register) _) = _
  rw [atCheck, stepAux_increment_zero current remaining distinct]

theorem resetTrace (current remaining : K) (distinct : current ≠ remaining)
    (resetLabel carryLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atReset : program resetLabel = reset current remaining resetLabel carryLabel)
    (base : K → List Bool) (d r : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[d + 1]
      (some ⟨some resetLabel, (ambient, register),
        digitTapes current remaining base d r currentSuffix remainingSuffix⟩) =
      some ⟨some carryLabel, (ambient, none),
        digitTapes current remaining base 0 (d + r) currentSuffix remainingSuffix⟩ :=
  MachineUnaryAddAt.addTrace current remaining distinct resetLabel (some carryLabel)
    program atReset base d r currentSuffix remainingSuffix ambient register

/-- Exhaustion costs one check plus the actual `d + 1`-transition reset. -/
theorem carryTrace (current remaining : K) (distinct : current ≠ remaining)
    (checkLabel doneLabel resetLabel carryLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atCheck : program checkLabel = increment current remaining doneLabel resetLabel)
    (atReset : program resetLabel = reset current remaining resetLabel carryLabel)
    (base : K → List Bool) (d : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[d + 2]
      (some ⟨some checkLabel, (ambient, register),
        digitTapes current remaining base d 0 currentSuffix remainingSuffix⟩) =
      some ⟨some carryLabel, (ambient, none),
        digitTapes current remaining base 0 d currentSuffix remainingSuffix⟩ := by
  rw [show d + 2 = (d + 1) + 1 by omega, Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step program))^[d + 1]
    (TM2.step program ⟨some checkLabel, (ambient, register),
      digitTapes current remaining base d 0 currentSuffix remainingSuffix⟩) = _
  rw [incrementStep_zero current remaining distinct checkLabel doneLabel resetLabel
    program atCheck]
  simpa only [Nat.add_zero] using resetTrace current remaining distinct resetLabel carryLabel
    program atReset base d 0 currentSuffix remainingSuffix ambient none

section AscendingCycle

open scoped BigOperators

def bodyConfiguration (current remaining : K) (bodyLabel : Λ)
    (maximum remainder : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : ℕ → σ) (base : ℕ → K → List Bool) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some bodyLabel, (ambient (remainder + 1), none),
    digitTapes current remaining (base (remainder + 1)) (maximum - remainder)
      remainder currentSuffix remainingSuffix⟩

def checkConfiguration (current remaining : K) (checkLabel : Λ)
    (maximum remainder : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : ℕ → σ) (register : ℕ → Option Bool) (base : ℕ → K → List Bool) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some checkLabel, (ambient remainder, register remainder),
    digitTapes current remaining (base remainder) (maximum - remainder)
      remainder currentSuffix remainingSuffix⟩

def cycleExit (current remaining : K) (exitLabel : Λ)
    (maximum : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : ℕ → σ) (base : ℕ → K → List Bool) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some exitLabel, (ambient 0, none),
    digitTapes current remaining (base 0) 0 maximum currentSuffix remainingSuffix⟩

def VisitTraces (current remaining : K) (bodyLabel checkLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (maximum count : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : ℕ → σ) (register : ℕ → Option Bool) (base : ℕ → K → List Bool)
    (cost : ℕ → ℕ) : Prop :=
  ∀ r, r ≤ count → (MachineComposition.advance (TM2.step program))^[cost r]
    (some (bodyConfiguration current remaining bodyLabel maximum r
      currentSuffix remainingSuffix ambient base)) =
    some (checkConfiguration current remaining checkLabel maximum r
      currentSuffix remainingSuffix ambient register base)

theorem cycleTrace (current remaining : K) (distinct : current ≠ remaining)
    (bodyLabel checkLabel resetLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atCheck : program checkLabel = increment current remaining bodyLabel resetLabel)
    (atReset : program resetLabel = reset current remaining resetLabel exitLabel)
    (maximum count : ℕ) (hcount : count ≤ maximum)
    (currentSuffix remainingSuffix : List Bool) (ambient : ℕ → σ)
    (register : ℕ → Option Bool) (base : ℕ → K → List Bool) (cost : ℕ → ℕ)
    (visits : VisitTraces current remaining bodyLabel checkLabel program maximum count
      currentSuffix remainingSuffix ambient register base cost) :
    (MachineComposition.advance (TM2.step program))^[cycleSteps cost maximum count]
      (some (bodyConfiguration current remaining bodyLabel maximum count
        currentSuffix remainingSuffix ambient base)) =
      some (cycleExit current remaining exitLabel maximum
        currentSuffix remainingSuffix ambient base) := by
  induction count with
  | zero =>
    rw [cycleSteps_zero, Function.iterate_add_apply, visits 0 (Nat.le_refl 0)]
    simpa only [checkConfiguration, cycleExit, Nat.sub_zero] using
      carryTrace current remaining distinct checkLabel bodyLabel resetLabel exitLabel
        program atCheck atReset (base 0) maximum currentSuffix remainingSuffix
        (ambient 0) (register 0)
  | succ count ih =>
    rw [cycleSteps_succ, Function.iterate_add_apply, visits (count + 1) (Nat.le_refl _),
      Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[cycleSteps cost maximum count]
      (TM2.step program ⟨some checkLabel, (ambient (count + 1), register (count + 1)),
        digitTapes current remaining (base (count + 1)) (maximum - (count + 1))
          (count + 1) currentSuffix remainingSuffix⟩) = _
    rw [incrementStep_succ current remaining distinct checkLabel bodyLabel resetLabel
      program atCheck]
    have hnext : maximum - (count + 1) + 1 = maximum - count := by omega
    rw [hnext]
    exact ih (by omega) (fun r hr => visits r (by omega))

/-- A full positive-radix cycle performs `n` body visits and exactly `2*n`
counter transitions. This bound comes from the composed actual execution. -/
def ascendingCycleInTime (current remaining : K) (distinct : current ≠ remaining)
    (bodyLabel checkLabel resetLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atCheck : program checkLabel = increment current remaining bodyLabel resetLabel)
    (atReset : program resetLabel = reset current remaining resetLabel exitLabel)
    (n : ℕ) (hn : 0 < n) (currentSuffix remainingSuffix : List Bool)
    (ambient : ℕ → σ) (register : ℕ → Option Bool) (base : ℕ → K → List Bool)
    (cost : ℕ → ℕ) (B : ℕ)
    (visits : VisitTraces current remaining bodyLabel checkLabel program (n - 1) (n - 1)
      currentSuffix remainingSuffix ambient register base cost)
    (bodyBound : ∀ r, r < n → cost r ≤ B) :
    StateTransition.EvalsToInTime (TM2.step program)
      (bodyConfiguration current remaining bodyLabel (n - 1) (n - 1)
        currentSuffix remainingSuffix ambient base)
      (some (cycleExit current remaining exitLabel (n - 1)
        currentSuffix remainingSuffix ambient base)) (n * (B + 2)) where
  steps := cycleSteps cost (n - 1) (n - 1)
  evals_in_steps := cycleTrace current remaining distinct bodyLabel checkLabel resetLabel exitLabel
    program atCheck atReset (n - 1) (n - 1) (Nat.le_refl _) currentSuffix remainingSuffix
    ambient register base cost visits
  steps_le_m := by
    have hsum : (∑ r ∈ Finset.range n, cost r) ≤ n * B := by
      calc
        _ ≤ ∑ _r ∈ Finset.range n, B :=
          Finset.sum_le_sum (fun r hr => bodyBound r (Finset.mem_range.mp hr))
        _ = _ := by simp
    have hn' : n - 1 + 1 = n := by omega
    simp only [cycleSteps, hn', Nat.mul_add] at *
    omega

end AscendingCycle

section Nested

open scoped BigOperators

/-- A finite nesting schedule. Only leaves supply actual emitter traces.
Internal nodes supply concrete instruction placements and compatible endpoint
schedules; their complete execution is derived below. Level `q` operates
coordinate `q`, so coordinate zero is always the innermost loop. -/
inductive NestedCycle (n : ℕ) (current remaining : ℕ → K) (bodyLabel : Λ)
    (checkLabel resetLabel : ℕ → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)) :
    ℕ → Λ → Configuration K Λ σ → Configuration K Λ σ → Type where
  | leaf (exitLabel : Λ) (start finish : Configuration K Λ σ) (count : ℕ)
      (atBody : start.l = some bodyLabel) (atExit : finish.l = some exitLabel)
      (run : (MachineComposition.advance (TM2.step program))^[count] (some start) = some finish) :
      NestedCycle n current remaining bodyLabel checkLabel resetLabel program
        0 exitLabel start finish
  | node (depth : ℕ) (exitLabel : Λ) (positive : 0 < n)
      (distinct : current depth ≠ remaining depth)
      (atCheck : program (checkLabel depth) =
        increment (current depth) (remaining depth) bodyLabel (resetLabel depth))
      (atReset : program (resetLabel depth) =
        reset (current depth) (remaining depth) (resetLabel depth) exitLabel)
      (s : CycleSchedule K σ)
      (children : ∀ r : Fin n,
        NestedCycle n current remaining bodyLabel checkLabel resetLabel program
          depth (checkLabel depth)
          (bodyConfiguration (current depth) (remaining depth) bodyLabel (n - 1) r.val
            s.currentSuffix s.remainingSuffix s.ambient s.base)
          (checkConfiguration (current depth) (remaining depth) (checkLabel depth) (n - 1) r.val
            s.currentSuffix s.remainingSuffix s.ambient s.register s.base)) :
      NestedCycle n current remaining bodyLabel checkLabel resetLabel program
        (depth + 1) exitLabel
        (bodyConfiguration (current depth) (remaining depth) bodyLabel (n - 1) (n - 1)
          s.currentSuffix s.remainingSuffix s.ambient s.base)
        (cycleExit (current depth) (remaining depth) exitLabel (n - 1)
          s.currentSuffix s.remainingSuffix s.ambient s.base)

namespace NestedCycle

variable {n : ℕ} {current remaining : ℕ → K} {bodyLabel : Λ}
  {checkLabel resetLabel : ℕ → Λ}
  {program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)}

def steps {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) : ℕ :=
  match tree with
  | .leaf _ _ _ count _ _ _ => count
  | .node _ _ _ _ _ _ _ children =>
    cycleSteps (fun r => if hr : r < n then steps (children ⟨r, hr⟩) else 0) (n - 1) (n - 1)
termination_by depth

/-- Every supplied emitter leaf obeys its local time allowance. There is no
whole-loop runtime premise at any internal node. -/
def LeafBound (B : ℕ) {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) : Prop :=
  match tree with
  | .leaf _ _ _ count _ _ _ => count ≤ B
  | .node _ _ _ _ _ _ _ children => ∀ r, LeafBound B (children r)
termination_by depth

/-- The whole nested-loop trace is derived from its actual leaf traces and
the concrete increment/reset code. -/
theorem trace {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) :
    (MachineComposition.advance (TM2.step program))^[tree.steps] (some start) = some finish := by
  induction tree with
  | leaf exitLabel start finish count atBody atExit run => simpa only [steps] using run
  | node depth exitLabel positive distinct atCheck atReset s children ih =>
    simp only [steps]
    apply cycleTrace (current depth) (remaining depth) distinct bodyLabel (checkLabel depth)
      (resetLabel depth) exitLabel program atCheck atReset (n - 1) (n - 1)
      (Nat.le_refl _) s.currentSuffix s.remainingSuffix s.ambient s.register s.base
      (fun r => if hr : r < n then steps (children ⟨r, hr⟩) else 0)
    intro r hr
    have hlt : r < n := by omega
    simpa only [dite_eq_left hlt] using ih ⟨r, hlt⟩

theorem steps_le {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) (B : ℕ) (bounded : tree.LeafBound B) :
    tree.steps ≤ n ^ depth * B + counterOverhead n depth := by
  induction tree with
  | leaf exitLabel start finish count atBody atExit run =>
    simpa only [steps, LeafBound, counterOverhead, pow_zero, Nat.one_mul, Nat.add_zero] using bounded
  | node depth exitLabel positive distinct atCheck atReset s children ih =>
    simp only [LeafBound] at bounded
    have visits : VisitTraces (current depth) (remaining depth) bodyLabel (checkLabel depth)
        program (n - 1) (n - 1) s.currentSuffix s.remainingSuffix s.ambient s.register s.base
        (fun r => if hr : r < n then steps (children ⟨r, hr⟩) else 0) := by
      intro r hr
      have hlt : r < n := by omega
      simpa only [dite_eq_left hlt] using (children ⟨r, hlt⟩).trace
    have bodyBound : ∀ r, r < n →
        (if hr : r < n then steps (children ⟨r, hr⟩) else 0) ≤
          n ^ depth * B + counterOverhead n depth := by
      intro r hr
      simpa only [dite_eq_left hr] using ih ⟨r, hr⟩ (bounded ⟨r, hr⟩)
    have h := (ascendingCycleInTime (current depth) (remaining depth) distinct bodyLabel
      (checkLabel depth) (resetLabel depth) exitLabel program atCheck atReset n positive
      s.currentSuffix s.remainingSuffix s.ambient s.register s.base
      (fun r => if hr : r < n then steps (children ⟨r, hr⟩) else 0)
      (n ^ depth * B + counterOverhead n depth) visits bodyBound).steps_le_m
    change cycleSteps _ (n - 1) (n - 1) ≤ _ at h
    simpa only [steps, counterOverhead, pow_succ, Nat.mul_add, Nat.add_mul,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc] using h

end NestedCycle

namespace NestedCycle

variable {n : ℕ} {current remaining : ℕ → K} {bodyLabel : Λ}
  {checkLabel resetLabel : ℕ → Λ}
  {program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)}

theorem steps_le_power {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) (hn : 0 < n) (B : ℕ) (bounded : tree.LeafBound B) :
    tree.steps ≤ (B + 2 * depth) * n ^ depth := by
  have h := (tree.steps_le B bounded).trans
    (Nat.add_le_add_left (counterOverhead_le n depth hn) (n ^ depth * B))
  simpa only [Nat.add_mul, Nat.mul_add, Nat.mul_comm] using h

end NestedCycle

end Nested

end UniqueGamesTheorem.Foundations.Complexity.MachineTupleOdometer

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_FiniteRangeInverse
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FiniteRangeInverse

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters (F2)
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open PerfectCompleteness.PartialTableInverse

attribute [local instance] linearMapFintype

universe u v w

variable {H : Type u} {K : Type v} {Y : Type w}
  [AddCommGroup H] [Module F2 H] [AddCommGroup K] [Module F2 K]
  [Fintype H] [Fintype K] [Fintype Y]
  [FiniteDimensional F2 H] [FiniteDimensional F2 K]

def agreement (f : (Module.Dual F2 H →ₗ[F2] K) → Option Y) : ℝ :=
  𝔼 a : {a : K // a ≠ 0}, 𝔼 X : Module.Dual F2 H →ₗ[F2] K,
    𝔼 h : H, definedEquality f X (matrixStep X a.val h)

end
end PerfectCompleteness.FiniteRangeInverse

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_OriginalChildScalars
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalChildScalars

open PointwiseSpaces RecursiveSpaces DescendantSpaces TreeSourceSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def callsLaw (calls : Nat) (repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    FiniteDistribution (Fin calls → ScalarTape repeats chosen q slots) :=
  FiniteProduct.law (fun _ : Fin calls =>
    RecursiveSampler.tapeLaw F2 repeats (.step chosen q) (LeafDomain slots))

end
end PerfectCompleteness.OriginalChildScalars

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineUnaryAffineAt
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCompare.compareInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec.decodeWords_encodeWord _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter.counterTapes_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt.transferLeft_tapes _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt.transferRight_tapes _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
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

theorem scan_step_succ (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient : Nat) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (base : K → List Bool) (a b : Nat) (suffix saved output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, (ambient,register), tapes source scratch destination base
      (encodeWord (a + 1) ++ suffix) saved (encodeWord b ++ output)⟩ =
      some ⟨some scanLabel, (ambient,some true), tapes source scratch destination base
        (encodeWord a ++ suffix) (true :: saved) (encodeWord (coefficient + b) ++ output)⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  rw [show encodeWord (a + 1) ++ suffix = true :: (encodeWord a ++ suffix) by
    simp [encodeWord, List.replicate_succ]]
  simp [scan, TM2.stepAux, tapes_source _ _ _ hs hd,
    update_source source scratch destination hs hd hsd, tapes_scratch _ _ _ hsd,
    update_scratch _ _ _ hsd, stepAux_pushWord, tapes_destination,
    prepend_replicate_word, update_destination]

theorem scan_step_zero (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient : Nat) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (base : K → List Bool) (b : Nat) (suffix saved output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, (ambient,register), tapes source scratch destination base
      (encodeWord 0 ++ suffix) saved (encodeWord b ++ output)⟩ =
      some ⟨some restoreLabel, (ambient,none), tapes source scratch destination base
        (encodeWord 0 ++ suffix) saved (encodeWord b ++ output)⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  rw [show encodeWord 0 ++ suffix = false :: suffix from rfl]
  simp [scan, finish, TM2.stepAux, tapes_source _ _ _ hs hd,
    update_source source scratch destination hs hd hsd]

theorem scanTrace (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient : Nat) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (base : K → List Bool) (a b : Nat) (suffix saved output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[a + 1]
      (some ⟨some scanLabel, (ambient,register), tapes source scratch destination base
        (encodeWord a ++ suffix) saved (encodeWord b ++ output)⟩) =
      some ⟨some restoreLabel, (ambient,none), tapes source scratch destination base
        (encodeWord 0 ++ suffix) (List.replicate a true ++ saved)
        (encodeWord (coefficient * a + b) ++ output)⟩ := by
  induction a generalizing b saved register with
  | zero =>
      simpa using scan_step_zero source scratch destination hs hd hsd coefficient scanLabel
        restoreLabel program atScan base b suffix saved output ambient register
  | succ a ih =>
      rw [Function.iterate_succ_apply]
      simp only [advance_some]
      rw [scan_step_succ source scratch destination hs hd hsd coefficient scanLabel restoreLabel
        program atScan]
      rw [ih]
      have hval : coefficient * a + (coefficient + b) = coefficient * (a + 1) + b := by
        rw [Nat.mul_succ]; omega
      rw [hval]
      have hsave : List.replicate a true ++ true :: saved = List.replicate (a + 1) true ++ saved := by
        simp only [List.replicate_add, List.replicate_one, List.append_assoc, List.singleton_append]
      rw [hsave]

theorem affineTrace (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient : Nat) (scanLabel restoreLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (atRestore : program restoreLabel = Reduction.MachineTransfer.loopAt
      scratch source id false restoreLabel exit)
    (base : K → List Bool) (a b : Nat) (suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * (a + 1)]
      (some ⟨some scanLabel, (ambient,register), tapes source scratch destination base
        (encodeWord a ++ suffix) [] (encodeWord b ++ output)⟩) =
      some ⟨exit, (ambient,none), tapes source scratch destination base
        (encodeWord a ++ suffix) [] (encodeWord (coefficient * a + b) ++ output)⟩ := by
  have hscan := scanTrace source scratch destination hs hd hsd coefficient scanLabel restoreLabel
    program atScan base a b suffix [] output ambient register
  simp only [List.append_nil] at hscan
  let mid := tapes source scratch destination base (encodeWord 0 ++ suffix)
    (List.replicate a true) (encodeWord (coefficient * a + b) ++ output)
  have hrestore := Reduction.MachineTransfer.transferAt_fromTapes scratch source (Ne.symm hs)
    id false restoreLabel exit program atRestore mid ambient none
  change (advance (TM2.step program))^[(mid scratch).length + 1]
    (some ⟨some restoreLabel,(ambient,none),mid⟩) = _ at hrestore
  have hsaved : mid scratch = List.replicate a true := by
    simp [mid, tapes, hsd]
  have hsource : mid source = encodeWord 0 ++ suffix := by
    simp [mid, tapes, hs, hd]
  rw [hsaved, hsource] at hrestore
  simp only [List.length_replicate, List.reverse_replicate, List.map_id] at hrestore
  have hword : List.replicate a true ++ (encodeWord 0 ++ suffix) = encodeWord a ++ suffix := by
    simp [encodeWord, List.append_assoc]
  rw [hword] at hrestore
  simp only [mid, restoreTapes source scratch destination hs hd hsd] at hrestore
  rw [show 2 * (a + 1) = (a + 1) + (a + 1) by omega, Function.iterate_add_apply, hscan]
  exact hrestore

/-- Include the literal offset prefix. The caller supplies an arbitrary output
suffix, not a precomputed address; all runtime arithmetic occurs on the tapes. -/
theorem seededAffineTrace (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient offset : Nat) (seedLabel scanLabel restoreLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atSeed : program seedLabel = seed destination offset scanLabel)
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (atRestore : program restoreLabel = Reduction.MachineTransfer.loopAt
      scratch source id false restoreLabel exit)
    (base : K → List Bool) (a : Nat) (suffix : List Bool)
    (sourceWord : base source = encodeWord a ++ suffix) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * (a + 1) + 1]
      (some ⟨some seedLabel, (ambient,register), base⟩) =
      some ⟨exit, (ambient,none),
        Function.update base destination (encodeWord (coefficient * a + offset) ++ base destination)⟩ := by
  have hseed : TM2.step program ⟨some seedLabel,(ambient,register),base⟩ =
      some ⟨some scanLabel,(ambient,register),
        Function.update base destination (encodeWord offset ++ base destination)⟩ := by
    change some (TM2.stepAux (program seedLabel) _ _) = _
    rw [atSeed, seed, stepAux_pushWord]
    simp only [List.reverse_reverse, TM2.stepAux]
  have hrun := affineTrace source scratch destination hs hd hsd coefficient scanLabel restoreLabel
    exit program atScan atRestore base a offset suffix (base destination) ambient register
  have hframe (word : List Bool) :
      tapes source scratch destination base (encodeWord a ++ suffix) [] word =
        Function.update base destination word := by
    rw [← sourceWord, ← scratchEmpty]
    simp only [tapes, MachineCopy.forkTapes, Function.update_eq_self]
  rw [hframe, hframe] at hrun
  rw [Function.iterate_succ_apply]
  simp only [advance_some]
  rw [hseed]
  exact hrun

end UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAffineAt

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineLookupLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_archive _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.atGuard _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableWords.decode_rotationWords _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
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

namespace UniqueGamesTheorem.Foundations.Complexity.MachineLookup

open Turing
open MachineComposition

variable {K σ : Type} [DecidableEq K]

theorem guard_step_succ (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination)
    (base : K → List Bool) (i : Nat) (indexSuffix input output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program index source destination)
      ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord (i + 1) ++ indexSuffix) input output⟩ =
      some ⟨some .skip, (ambient, none), tapes index source destination base
        (encodeWord i ++ indexSuffix) input output⟩ := by
  change some (TM2.stepAux (program index source destination .guard) _ _) = _
  simp [program, MachineUnaryCounter.guard, TM2.stepAux,
    tapes_index, his, hid, encodeWord, List.replicate_succ, update_index]

theorem guard_step_zero (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination)
    (base : K → List Bool) (indexSuffix input output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program index source destination)
      ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) input output⟩ =
      some ⟨some .select, (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) input output⟩ := by
  change some (TM2.stepAux (program index source destination .guard) _ _) = _
  simp [program, MachineUnaryCounter.guard, TM2.stepAux,
    tapes_index, his, hid, encodeWord]

theorem select_step_nonempty (index source destination : K)
    (hsd : source ≠ destination) (base : K → List Bool)
    (counter input output : List Bool) (hinput : input ≠ [])
    (ambient : σ) (register : Option Bool) :
    TM2.step (program index source destination)
      ⟨some .select, (ambient, register),
        tapes index source destination base counter input output⟩ =
      some ⟨some .copy, (ambient, input.head?),
        tapes index source destination base counter input (false :: output)⟩ := by
  change some (TM2.stepAux (program index source destination .select) _ _) = _
  cases input with
  | nil => exact (hinput rfl).elim
  | cons head tail =>
    simp [program, select, Hastad.SourceMachine.fieldStart, TM2.stepAux,
      tapes_source, hsd, update_destination]

theorem copyTrace (index source destination : K)
    (hsd : source ≠ destination) (base : K → List Bool)
    (counter : List Bool) (n : Nat) (suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[n + 1]
      (some ⟨some .copy, (ambient, register), tapes index source destination base
        counter (encodeWord n ++ suffix) (false :: output)⟩) =
      some ⟨some .accepted, (ambient, none), tapes index source destination base
        counter suffix (encodeWord n ++ output)⟩ := by
  have h := Hastad.SourceMachine.fieldLoopTrace source destination hsd
    Label.copy (some Label.accepted) (program index source destination) rfl
    (Function.update base index counter) n suffix (false :: output) ambient register
  simpa only [Hastad.SourceMachine.fieldTapes, tapes, encodeWord,
    List.append_assoc, List.singleton_append] using h

theorem selectTrace (index source destination : K)
    (hsd : source ≠ destination) (base : K → List Bool)
    (counter : List Bool) (n : Nat) (suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[n + 2]
      (some ⟨some .select, (ambient, register), tapes index source destination base
        counter (encodeWord n ++ suffix) output⟩) =
      some ⟨some .accepted, (ambient, none), tapes index source destination base
        counter suffix (encodeWord n ++ output)⟩ := by
  rw [show n + 2 = (n + 1) + 1 by omega, Function.iterate_succ_apply]
  simp only [advance_some]
  rw [select_step_nonempty index source destination hsd base counter
    (encodeWord n ++ suffix) output (by simp [encodeWord]) ambient register]
  exact copyTrace index source destination hsd base counter n suffix output ambient _

theorem skipCycleTrace (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (i n : Nat) (indexSuffix suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[n + 2]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord (i + 1) ++ indexSuffix) (encodeWord n ++ suffix) output⟩) =
      some ⟨some .guard, (ambient, none), tapes index source destination base
        (encodeWord i ++ indexSuffix) suffix output⟩ := by
  rw [show n + 2 = (n + 1) + 1 by omega, Function.iterate_succ_apply]
  simp only [advance_some]
  rw [guard_step_succ index source destination his hid]
  have h := discardTrace source Label.skip Label.guard
    (program index source destination) rfl
    (tapes index source destination base (encodeWord i ++ indexSuffix)
      (encodeWord n ++ suffix) output) n suffix (by simp [hsd]) ambient none
  simpa only [update_source index source destination hsd] using h

/-- A successful positional lookup scans precisely its prior and selected
field. The suffix is arbitrary and is retained byte for byte. -/
theorem successPrefixTrace (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (prior : List Nat) (value : Nat)
    (indexSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[
        (encodeWords prior).length + prior.length + value + 3]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord prior.length ++ indexSuffix)
        (encodeWords prior ++ (encodeWord value ++ suffix)) output⟩) =
      some ⟨some .accepted, (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) suffix (encodeWord value ++ output)⟩ := by
  induction prior generalizing register with
  | nil =>
    simp only [encodeWords, List.length_nil, Nat.zero_add, List.nil_append]
    rw [show value + 3 = (value + 2) + 1 by omega, Function.iterate_succ_apply]
    simp only [advance_some]
    rw [guard_step_zero index source destination his hid]
    exact selectTrace index source destination hsd base _ value suffix output ambient none
  | cons n prior ih =>
    simp only [encodeWords, List.length_cons, List.length_append, encodeWord_length]
    rw [show n + 1 + (encodeWords prior).length + (prior.length + 1) + value + 3 =
      ((encodeWords prior).length + prior.length + value + 3) + (n + 2) by omega,
      Function.iterate_add_apply]
    rw [List.append_assoc,
      skipCycleTrace index source destination his hid hsd base prior.length n]
    exact ih none

/-- Successful array access, with explicit selected value and preserved framing. -/
theorem lookupTrace_some (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (values : List Nat) (i value : Nat)
    (selected : values[i]? = some value)
    (indexSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[MachineLookupSpec.steps values i]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord i ++ indexSuffix) (encodeWords values ++ suffix) output⟩) =
      some ⟨some .accepted, (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) (encodeWords (values.drop (i + 1)) ++ suffix)
        (encodeWord value ++ output)⟩ := by
  have hi := (List.getElem?_eq_some_iff.mp selected).1
  have hlength : (values.take i).length = i := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hsource : encodeWords (values.take i) ++
      (encodeWord value ++ (encodeWords (values.drop (i + 1)) ++ suffix)) =
      encodeWords values ++ suffix := by
    rw [MachineLookupSpec.encoded_selected_split values i value selected]
    simp only [List.append_assoc]
  have htime : MachineLookupSpec.steps values i =
      (encodeWords (values.take i)).length + i + value + 3 := by
    rw [MachineLookupSpec.steps_eq_scannedBits_of_some values i value selected,
      MachineLookupSpec.scannedBits_of_some values i value selected]
    omega
  have h := successPrefixTrace index source destination his hid hsd base (values.take i)
    value indexSuffix (encodeWords (values.drop (i + 1)) ++ suffix) output ambient register
  rw [hlength, hsource] at h
  simpa only [htime] using h

end UniqueGamesTheorem.Foundations.Complexity.MachineLookup

/-! Actual lookup from a preserved table. A fresh copy is prefixed to the scan
stack before each access. The old scan suffix is retained and need not be
cleared between accesses. No graph/table data occurs in finite control. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePreservingLookup

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

theorem lookupFramedHaltTrace_some (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (values : List Nat) (i value : Nat)
    (selected : values[i]? = some value) (indexSuffix suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (MachineLookup.program index source destination)))^[
      MachineLookupSpec.steps values i + 1]
      (some ⟨some MachineLookup.Label.guard, (ambient,register),
        MachineLookup.tapes index source destination base (encodeWord i ++ indexSuffix)
          (encodeWords values ++ suffix) output⟩) =
      some ⟨none, (ambient,none), MachineLookup.tapes index source destination base
        (encodeWord 0 ++ indexSuffix) (encodeWords (values.drop (i + 1)) ++ suffix)
        (encodeWord value ++ output)⟩ := by
  rw [Function.iterate_succ_apply',
    MachineLookup.lookupTrace_some index source destination his hid hsd
      base values i value selected indexSuffix suffix output ambient register]
  simp only [advance_some, TM2.step, MachineLookup.program, TM2.stepAux]

/-- Code-level interfaces specify the actual two copy loops and six lookup
instructions in the caller's program. No execution premise is supplied. -/
theorem preservingLookupTrace (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (firstLabel secondLabel : Λ) (lookupLabels : MachineLookup.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atFirst : program firstLabel = Reduction.MachineTransfer.loopAt
      (tape 0) (tape 4) id false firstLabel (some secondLabel))
    (atSecond : program secondLabel = MachineCopy.forkLoop
      (tape 4) (tape 0) (tape 2) false secondLabel (some (lookupLabels .guard)))
    (atLookup : ∀ l, program (lookupLabels l) =
      MachineSubroutine.statement lookupLabels exit (MachineLookup.program (tape 1) (tape 2) (tape 3) l))
    (base : K → List Bool) (values : List Nat) (tableWord : base (tape 0) = encodeWords values)
    (scratchEmpty : base (tape 4) = []) (i value : Nat) (selected : values[i]? = some value)
    (indexSuffix workSuffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[
      2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values i + 1]
      (some ⟨some firstLabel, (ambient,register),
        initialTapes tape base i indexSuffix workSuffix output⟩) =
      some ⟨exit, (ambient,none), finalTapes tape base values i value indexSuffix workSuffix output⟩ := by
  have hd (a b : Fin 5) (hne : a ≠ b) : tape a ≠ tape b := fun h => hne (distinct h)
  let start := initialTapes tape base i indexSuffix workSuffix output
  have htable : start (tape 0) = encodeWords values := by
    simpa only [start, initialTapes, MachineLookup.tapes_other _ _ _ _
      (hd 0 1 (by decide)) (hd 0 2 (by decide)) (hd 0 3 (by decide))] using tableWord
  have hs : start (tape 4) = [] := by
    simpa only [start, initialTapes, MachineLookup.tapes_other _ _ _ _
      (hd 4 1 (by decide)) (hd 4 2 (by decide)) (hd 4 3 (by decide))] using scratchEmpty
  have hwork : start (tape 2) = workSuffix := by
    simp only [start, initialTapes, MachineLookup.tapes_source _ _ _ (hd 2 3 (by decide))]
  have hcopy := MachineCopy.copyTrace (tape 0) (tape 2) (tape 4)
    (hd 0 2 (by decide)) (hd 0 4 (by decide)) (hd 2 4 (by decide)) false
    firstLabel secondLabel (some (lookupLabels .guard)) program atFirst atSecond start hs ambient register
  rw [htable, hwork] at hcopy
  simp only [start, initialTapes, MachineLookup.update_source _ _ _ (hd 2 3 (by decide))] at hcopy
  have hlookup := MachineSubroutine.trace lookupLabels exit
    (MachineLookup.program (tape 1) (tape 2) (tape 3)) program atLookup
    (MachineLookupSpec.steps values i + 1) _ _
    (lookupFramedHaltTrace_some (tape 1) (tape 2) (tape 3)
      (hd 1 2 (by decide)) (hd 1 3 (by decide)) (hd 2 3 (by decide))
      base values i value selected indexSuffix workSuffix output ambient none)
  simp only [MachineSubroutine.configuration, MachineSubroutine.label] at hlookup
  rw [show 2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values i + 1 =
      (MachineLookupSpec.steps values i + 1) + 2 * ((encodeWords values).length + 1) by omega,
    Function.iterate_add_apply]
  change (advance (TM2.step program))^[MachineLookupSpec.steps values i + 1]
    ((advance (TM2.step program))^[2 * ((encodeWords values).length + 1)]
      (some ⟨some firstLabel, (ambient,register),
        MachineLookup.tapes (tape 1) (tape 2) (tape 3) base
          (encodeWord i ++ indexSuffix) workSuffix output⟩)) = _
  rw [hcopy]
  exact hlookup

end UniqueGamesTheorem.Foundations.Complexity.MachinePreservingLookup

namespace UniqueGamesTheorem.Foundations.Complexity.MachineAffineLookup

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

theorem initialTapes_eq_update (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (i : Nat) :
    MachinePreservingLookup.initialTapes tape base i
      (base (tape 1)) (base (tape 2)) (base (tape 3)) =
      Function.update base (tape 1) (encodeWord i ++ base (tape 1)) := by
  have hd (a b : Fin 5) (hne : a ≠ b) : tape a ≠ tape b := fun h => hne (distinct h)
  funext k
  by_cases h₁ : k = tape 1
  · subst k
    simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes,
      hd 1 2 (by decide), hd 1 3 (by decide)]
  · by_cases h₂ : k = tape 2
    · subst k
      simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes, h₁,
        hd 2 3 (by decide)]
    · by_cases h₃ : k = tape 3
      · subst k
        simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes, h₁]
      · simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes, h₁, h₂, h₃]

/-- An exact trace for the actual composite instructions. `atLabels` specifies
the caller's finite program; there is no execution or runtime premise. -/
theorem affineLookupTrace (source : K) (tape : Fin 5 → K)
    (distinct : Function.Injective tape) (outside : ∀ i, source ≠ tape i)
    (coefficient offset : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction source tape coefficient offset labels exit l)
    (base : K → List Bool) (values : List Nat)
    (tableWord : base (tape 0) = encodeWords values) (scratchEmpty : base (tape 4) = [])
    (a : Nat) (suffix : List Bool) (sourceWord : base source = encodeWord a ++ suffix)
    (value : Nat) (selected : values[coefficient * a + offset]? = some value)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps values a coefficient offset]
      (some ⟨some (labels .seed), (ambient,register), base⟩) =
      some ⟨exit, (ambient,none), finalTapes tape base values (coefficient * a + offset) value⟩ := by
  have hd (i j : Fin 5) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have haffine := MachineUnaryAffineAt.seededAffineTrace source (tape 4) (tape 1)
    (outside 4) (outside 1) (hd 4 1 (by decide)) coefficient offset
    (labels .seed) (labels .scan) (labels .restore) (some (labels .copyFirst))
    program (atLabels .seed) (atLabels .scan) (atLabels .restore)
    base a suffix sourceWord scratchEmpty ambient register
  have hlookup := MachinePreservingLookup.preservingLookupTrace tape distinct
    (labels .copyFirst) (labels .copySecond) (fun q => labels (.lookup q)) exit
    program (atLabels .copyFirst) (atLabels .copySecond) (fun q => atLabels (.lookup q))
    base values tableWord scratchEmpty (coefficient * a + offset) value selected
    (base (tape 1)) (base (tape 2)) (base (tape 3)) ambient none
  rw [initialTapes_eq_update tape distinct] at hlookup
  rw [steps, Nat.add_comm, Function.iterate_add_apply, haffine]
  exact hlookup

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
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineTransducerCopy
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCompare.compareInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt.transferLeft_tapes _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt.transferRight_tapes
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

theorem emitterStep (source scratch destination : K)
    (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (scanLabel : Λ) (emitterLabel : Q → Bool → Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atEmitter : ∀ control symbol, program (emitterLabel control symbol) =
      emitter destination transition emit scanLabel control symbol)
    (base : K → List Bool) (input scratchWord outputWord : List Bool)
    (ambient : σ) (control : Q) (symbol : Bool) :
    TM2.step program ⟨some (emitterLabel control symbol), ((ambient, control), some symbol),
      tapes source scratch destination base input scratchWord outputWord⟩ =
      some ⟨some scanLabel, ((ambient, transition control symbol), some symbol),
        tapes source scratch destination base input scratchWord
          ((emit control symbol).reverse ++ outputWord)⟩ := by
  change some (TM2.stepAux (program (emitterLabel control symbol)) ((ambient, control), some symbol)
    (tapes source scratch destination base input scratchWord outputWord)) = _
  rw [atEmitter]
  simp only [emitter, TM2.stepAux]
  rw [stepAux_pushWord]
  simp only [TM2.stepAux, MachineCopy.forkTapes_right]
  rw [update_output]

theorem twoSteps_cons (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (scanLabel restoreLabel : Λ) (emitterLabel : Q → Bool → Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atScan : program scanLabel = scanLoop source scratch initial emitterLabel restoreLabel)
    (atEmitter : ∀ control symbol, program (emitterLabel control symbol) =
      emitter destination transition emit scanLabel control symbol)
    (base : K → List Bool) (symbol : Bool) (input scratchWord outputWord : List Bool)
    (ambient : σ) (control : Q) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2]
      (some ⟨some scanLabel, ((ambient, control), register),
        tapes source scratch destination base (symbol :: input) scratchWord outputWord⟩) =
      some ⟨some scanLabel, ((ambient, transition control symbol), some symbol),
        tapes source scratch destination base input (symbol :: scratchWord)
          ((emit control symbol).reverse ++ outputWord)⟩ := by
  change (TM2.step program ⟨some scanLabel, ((ambient, control), register),
    tapes source scratch destination base (symbol :: input) scratchWord outputWord⟩).bind
      (TM2.step program) = _
  rw [scanStep_cons source scratch destination sourceScratch sourceDestination scratchDestination
    initial scanLabel restoreLabel emitterLabel program atScan base symbol input scratchWord
    outputWord ambient control register]
  exact emitterStep source scratch destination transition emit scanLabel emitterLabel program
    atEmitter base input (symbol :: scratchWord) outputWord ambient control symbol

theorem scanTrace (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (scanLabel restoreLabel : Λ) (emitterLabel : Q → Bool → Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atScan : program scanLabel = scanLoop source scratch initial emitterLabel restoreLabel)
    (atEmitter : ∀ control symbol, program (emitterLabel control symbol) =
      emitter destination transition emit scanLabel control symbol)
    (base : K → List Bool) (input scratchWord outputWord : List Bool)
    (ambient : σ) (control : Q) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * input.length + 1]
      (some ⟨some scanLabel, ((ambient, control), register),
        tapes source scratch destination base input scratchWord outputWord⟩) =
      some ⟨some restoreLabel, ((ambient, initial), none),
        tapes source scratch destination base [] (input.reverse ++ scratchWord)
          ((Reduction.MachineTransducer.output transition emit control input).reverse ++ outputWord)⟩ := by
  induction input generalizing control scratchWord outputWord register with
  | nil =>
    simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, Function.iterate_one,
      MachineComposition.advance_some, Reduction.MachineTransducer.output, List.reverse_nil,
      List.nil_append] using
      scanStep_empty source scratch destination sourceScratch sourceDestination scratchDestination
        initial scanLabel restoreLabel emitterLabel program atScan base scratchWord outputWord
        ambient control register
  | cons symbol input ih =>
    rw [List.length_cons, show 2 * (input.length + 1) + 1 = (2 * input.length + 1) + 2 by omega,
      Function.iterate_add_apply]
    rw [twoSteps_cons source scratch destination sourceScratch sourceDestination scratchDestination
      initial transition emit scanLabel restoreLabel emitterLabel program atScan atEmitter base
      symbol input scratchWord outputWord ambient control register, ih]
    simp only [Reduction.MachineTransducer.output, List.reverse_append, List.reverse_cons,
      List.append_assoc, List.singleton_append]

theorem transduceCopyTrace (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (scanLabel restoreLabel : Λ) (emitterLabel : Q → Bool → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atScan : program scanLabel = scanLoop source scratch initial emitterLabel restoreLabel)
    (atEmitter : ∀ control symbol, program (emitterLabel control symbol) =
      emitter destination transition emit scanLabel control symbol)
    (atRestore : program restoreLabel =
      Reduction.MachineTransfer.loopAt scratch source id false restoreLabel exit)
    (base : K → List Bool) (scratchEmpty : base scratch = [])
    (ambient : σ) (control : Q) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[3 * (base source).length + 2]
      (some ⟨some scanLabel, ((ambient, control), register), base⟩) =
      some ⟨exit, ((ambient, initial), none),
        Function.update base destination
          ((Reduction.MachineTransducer.output transition emit control (base source)).reverse ++
            base destination)⟩ := by
  have scan := scanTrace source scratch destination sourceScratch sourceDestination scratchDestination
    initial transition emit scanLabel restoreLabel emitterLabel program atScan atEmitter base
    (base source) (base scratch) (base destination) ambient control register
  have tapesSelf : tapes source scratch destination base (base source) (base scratch)
      (base destination) = base := MachineCopy.forkTapes_self source scratch destination base
  rw [tapesSelf] at scan
  simp only [scratchEmpty, List.append_nil] at scan
  let outputWord :=
    (Reduction.MachineTransducer.output transition emit control (base source)).reverse ++ base destination
  let scanned := tapes source scratch destination base [] (base source).reverse outputWord
  have restore := Reduction.MachineTransfer.transferAt_fromTapes scratch source (Ne.symm sourceScratch)
    id false restoreLabel exit program atRestore scanned (ambient, initial) none
  change (MachineComposition.advance (TM2.step program))^[(scanned scratch).length + 1]
    (some ⟨some restoreLabel, ((ambient, initial), none), scanned⟩) = _ at restore
  have scratchWord : scanned scratch = (base source).reverse := by
    simp [scanned, scratchDestination]
  have sourceWord : scanned source = [] := by
    simp [scanned, sourceScratch, sourceDestination]
  rw [scratchWord, sourceWord] at restore
  simp only [List.map_id, List.reverse_reverse, List.append_nil, List.length_reverse] at restore
  rw [restoreTapes source scratch destination sourceScratch sourceDestination scratchDestination
    base scratchEmpty outputWord] at restore
  rw [show 3 * (base source).length + 2 =
    ((base source).length + 1) + (2 * (base source).length + 1) by omega,
    Function.iterate_add_apply, scan]
  exact restore

end UniqueGamesTheorem.Foundations.Complexity.MachineTransducerCopy

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_Emitter
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.program_firstEmit _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.program_outputEmit _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.program_secondEmit _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
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

/-- Exact execution of one command of the supplied actual program. The only
program hypotheses are equations for its concrete finite statements. -/
theorem commandTrace (sources : Fin h → K) (scratch output : K)
    (sourceScratch : ∀ i, sources i ≠ scratch)
    (sourceOutput : ∀ i, sources i ≠ output) (scratchOutput : scratch ≠ output)
    (labels : Phase bound → Λ) (next : Λ) (command : Command h σ bound)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ phase,
      program (labels phase) = commandStatement sources scratch output labels next command phase)
    (values : Fin h → Nat) (base : K → List Bool)
    (operands : ∀ i, base (sources i) = encodeWord (values i))
    (scratchEmpty : base scratch = []) (ambient : σ) :
    (MachineComposition.advance (TM2.step program))^[commandSteps values command]
      (some ⟨some (labels .entry), ((ambient, ()), none), base⟩) =
      some ⟨some next, ((ambient, ()), none),
        Function.update base output ((commandBits values ambient command).reverse ++ base output)⟩ := by
  cases command with
  | literal word =>
    change some (TM2.stepAux (program (labels .entry)) ((ambient, ()), none) base) = _
    rw [atLabels]
    simp only [commandStatement, stepAux_pushWord, TM2.stepAux, commandBits]
  | bit value =>
    change some (TM2.stepAux (program (labels .entry)) ((ambient, ()), none) base) = _
    rw [atLabels]
    cases hb : value ambient <;>
      simp [commandStatement, TM2.stepAux, pushWord, commandBits, hb, encodeWord]
  | bounded value =>
    change (TM2.step program ⟨some (labels .entry), ((ambient, ()), none), base⟩).bind
      (TM2.step program) = _
    have first : TM2.step program ⟨some (labels .entry), ((ambient, ()), none), base⟩ =
        some ⟨some (labels (.offset (value ambient))), ((ambient, ()), none), base⟩ := by
      change some (TM2.stepAux (program (labels .entry)) _ _) = _
      rw [atLabels]
      rfl
    rw [first]
    change some (TM2.stepAux (program (labels (.offset (value ambient)))) _ _) = _
    rw [atLabels]
    simp only [commandStatement, stepAux_pushWord, TM2.stepAux, commandBits]
  | scaled source coefficient =>
    have emitAt : ∀ control symbol, program (labels (.emit symbol)) =
        MachineTransducerCopy.emitter output transition (payload coefficient)
          (labels .entry) control symbol := by
      intro control symbol
      cases control
      exact atLabels (.emit symbol)
    have run := MachineTransducerCopy.transduceCopyTrace (sources source) scratch output
      (sourceScratch source) (sourceOutput source) scratchOutput () transition (payload coefficient)
      (labels .entry) (labels .restore) (fun _ symbol => labels (.emit symbol)) (some next)
      program (atLabels .entry) emitAt (atLabels .restore) base scratchEmpty ambient () none
    rw [operands source, encodeWord_length, output_encodeWord] at run
    exact run
  | scaledIf source coefficient active =>
    have first : TM2.step program ⟨some (labels .entry), ((ambient, ()), none), base⟩ =
        some ⟨some (labels (.scanIf (active ambient))), ((ambient, ()), none), base⟩ := by
      change some (TM2.stepAux (program (labels .entry)) _ _) = _
      rw [atLabels]
      rfl
    have emitAt : ∀ control symbol, program (labels (.emitIf (active ambient) symbol)) =
        MachineTransducerCopy.emitter output transition
          (payload (if active ambient then coefficient else 0))
          (labels (.scanIf (active ambient))) control symbol := by
      intro control symbol
      cases control
      exact atLabels (.emitIf (active ambient) symbol)
    have run := MachineTransducerCopy.transduceCopyTrace (sources source) scratch output
      (sourceScratch source) (sourceOutput source) scratchOutput () transition
      (payload (if active ambient then coefficient else 0))
      (labels (.scanIf (active ambient))) (labels .restore)
      (fun _ symbol => labels (.emitIf (active ambient) symbol)) (some next)
      program (atLabels (.scanIf (active ambient))) emitAt (atLabels .restore)
      base scratchEmpty ambient () none
    rw [operands source, encodeWord_length, output_encodeWord] at run
    change (MachineComposition.advance (TM2.step program))^[
      (3 * (values source + 1) + 2) + 1] _ = _
    rw [Function.iterate_succ_apply]
    simp only [MachineComposition.advance_some]
    rw [first]
    exact run

def prefixBits {count : Nat} (commands : Fin count → Command h σ bound)
    (values : Fin h → Nat) (ambient : σ) : Nat → List Bool
  | 0 => []
  | r + 1 => prefixBits commands values ambient r ++
      commandBits values ambient (commandAt commands r)

def prefixSteps {count : Nat} (commands : Fin count → Command h σ bound)
    (values : Fin h → Nat) : Nat → Nat
  | 0 => 0
  | r + 1 => prefixSteps commands values r + commandSteps values (commandAt commands r)

/-- Composition of the actual finite command traces, with preserved operand
stacks available again at every command boundary. -/
theorem prefixTrace {count : Nat} (commands : Fin count → Command h σ bound)
    (sources : Fin h → K) (scratch output : K)
    (sourceScratch : ∀ i, sources i ≠ scratch)
    (sourceOutput : ∀ i, sources i ≠ output) (scratchOutput : scratch ≠ output)
    (labels : Label count bound → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement commands sources scratch output labels exit label)
    (values : Fin h → Nat) (base : K → List Bool)
    (operands : ∀ i, base (sources i) = encodeWord (values i))
    (scratchEmpty : base scratch = []) (ambient : σ) (r : Nat) (hr : r ≤ count) :
    (MachineComposition.advance (TM2.step p))^[prefixSteps commands values r]
      (some ⟨some (labels (labelAt count bound 0 .entry)), ((ambient, ()), none), base⟩) =
      some ⟨some (labels (labelAt count bound r .entry)), ((ambient, ()), none),
        resultTapes output base (prefixBits commands values ambient r)⟩ := by
  induction r with
  | zero => simp [prefixSteps, prefixBits, resultTapes]
  | succ r ih =>
    have hrc : r < count := by omega
    let prior := resultTapes output base (prefixBits commands values ambient r)
    have priorOperands : ∀ i, prior (sources i) = encodeWord (values i) := by
      intro i
      simpa [prior, resultTapes, sourceOutput i] using operands i
    have priorScratch : prior scratch = [] := by
      simpa [prior, resultTapes, scratchOutput] using scratchEmpty
    have commandAtLabels : ∀ phase, p (labels (labelAt count bound r phase)) =
        commandStatement sources scratch output (fun phase => labels (labelAt count bound r phase))
          (labels (labelAt count bound (r + 1) .entry)) (commandAt commands r) phase := by
      intro phase
      rw [atLabels]
      simp only [statement, labelAt, Nat.min_eq_left (Nat.le_of_lt hrc), hrc, ite_true, if_true]
    have one := commandTrace sources scratch output sourceScratch sourceOutput scratchOutput
      (fun phase => labels (labelAt count bound r phase))
      (labels (labelAt count bound (r + 1) .entry)) (commandAt commands r)
      p commandAtLabels values prior priorOperands priorScratch ambient
    rw [prefixSteps, Nat.add_comm, Function.iterate_add_apply, ih (by omega)]
    rw [one]
    congr 2
    simp [prior, prefixBits, resultTapes, List.reverse_append, List.append_assoc]

/-- The complete callable program, including its actual final jump or halt. -/
theorem planTrace {count : Nat} (commands : Fin count → Command h σ bound)
    (sources : Fin h → K) (scratch output : K)
    (sourceScratch : ∀ i, sources i ≠ scratch)
    (sourceOutput : ∀ i, sources i ≠ output) (scratchOutput : scratch ≠ output)
    (labels : Label count bound → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement commands sources scratch output labels exit label)
    (values : Fin h → Nat) (base : K → List Bool)
    (operands : ∀ i, base (sources i) = encodeWord (values i))
    (scratchEmpty : base scratch = []) (ambient : σ) :
    (MachineComposition.advance (TM2.step p))^[prefixSteps commands values count + 1]
      (some ⟨some (labels (labelAt count bound 0 .entry)), ((ambient, ()), none), base⟩) =
      some ⟨exit, ((ambient, ()), none),
        resultTapes output base (prefixBits commands values ambient count)⟩ := by
  rw [Function.iterate_succ_apply', prefixTrace commands sources scratch output sourceScratch
    sourceOutput scratchOutput labels exit p atLabels values base operands scratchEmpty ambient count
    (Nat.le_refl _)]
  change some (TM2.stepAux (p (labels (labelAt count bound count .entry))) _ _) = _
  rw [atLabels]
  cases exit <;> simp [statement, labelAt, Reduction.MachineTransfer.exitAt, TM2.stepAux]

theorem prefixBits_listCommands (commands : List (Command h σ bound))
    (values : Fin h → Nat) (ambient : σ) (r : Nat) (hr : r ≤ commands.length) :
    prefixBits (listCommands commands) values ambient r =
      (commands.take r).flatMap (commandBits values ambient) := by
  induction r with
  | zero => simp [prefixBits]
  | succ r ih =>
    have hrc : r < commands.length := by omega
    rw [prefixBits, ih (by omega), List.take_succ_eq_append_getElem hrc,
      List.flatMap_append]
    simp [commandAt, hrc, listCommands]

theorem bits_listCommands (commands : List (Command h σ bound))
    (values : Fin h → Nat) (ambient : σ) :
    prefixBits (listCommands commands) values ambient commands.length =
      commands.flatMap (commandBits values ambient) := by
  simpa using prefixBits_listCommands commands values ambient commands.length (Nat.le_refl _)

theorem scaleBits (terms : List (Fin h × Nat)) (values : Fin h → Nat) (ambient : σ) :
    (terms.map (fun term => (Command.scaled term.1 term.2 : Command h σ bound))).flatMap
      (commandBits values ambient) =
    List.replicate ((terms.map (fun term => term.2 * values term.1)).sum) true := by
  induction terms with
  | nil => rfl
  | cons term terms ih =>
    simp only [List.map_cons, List.flatMap_cons, commandBits, List.sum_cons]
    rw [ih, List.replicate_add]

theorem affineCommands_bits (terms : List (Fin h × Nat)) (offset : σ → Fin bound)
    (values : Fin h → Nat) (ambient : σ) :
    (affineCommands terms offset).flatMap (commandBits values ambient) =
      encodeWord (affineValue terms values (offset ambient).val) := by
  simp only [affineCommands, List.flatMap_append, scaleBits, List.flatMap_cons,
    List.flatMap_nil, commandBits, List.append_nil, affineValue, encodeWord,
    List.replicate_add, List.append_assoc]

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Emitter

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_FinalCNFStream
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.cloudRank_cloudSelect _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.cloudRank_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_cloudRank _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_oldCloudIndex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.mem_cloudDarts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.paddedCloudRank_new _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.paddedCloudRank_new_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.paddedCloudRank_old _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.paddedCloudRank_old_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.paddedCloudRank_select _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.paddedCloudSelect_castAdd _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.paddedCloudSelect_natAdd _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.paddedCloudSelect_rank _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_internal _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.vertexOrder_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.vertexOrder_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Exact row enumeration and input/output stream identities for the concrete
final-CNF machine. Rows occur in stored order, including repeated rows.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

open PCP PCP.AlphabetTable FinalCNFTableAdapter

@[simp] theorem outputStream_append (plan : Plan) (table : GraphTables.Table)
    (first rest : List (Fin table.darts)) :
    outputStream plan table (first ++ rest) =
      outputStream plan table first ++ outputStream plan table rest := by
  simp only [outputStream, List.flatMap_append]

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineFixedDivMod
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionStates_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec.decodeWords_encodeWord _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter.counterTapes_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
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

theorem update_source (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (base : K → List Bool)
    (input quotientWord remainderWord replacement : List Bool) :
    Function.update (tapes source quotient remainder base input quotientWord remainderWord)
      source replacement = tapes source quotient remainder base replacement quotientWord remainderWord := by
  funext k
  by_cases hs : k = source
  · subst k
    simp [tapes, MachineCopy.forkTapes, sourceQuotient, sourceRemainder]
  · by_cases hq : k = quotient
    · subst k
      simp [tapes, MachineCopy.forkTapes, Ne.symm sourceQuotient, quotientRemainder]
    · by_cases hr : k = remainder
      · subst k
        simp [tapes, MachineCopy.forkTapes, Ne.symm sourceRemainder]
      · simp [tapes, MachineCopy.forkTapes, hs, hq, hr]

theorem update_quotient (source quotient remainder : K)
    (quotientRemainder : quotient ≠ remainder) (base : K → List Bool)
    (input quotientWord remainderWord replacement : List Bool) :
    Function.update (tapes source quotient remainder base input quotientWord remainderWord)
      quotient replacement = tapes source quotient remainder base input replacement remainderWord := by
  funext k
  by_cases hq : k = quotient
  · subst k
    simp [tapes, MachineCopy.forkTapes, quotientRemainder]
  · by_cases hr : k = remainder
    · subst k
      simp [tapes, MachineCopy.forkTapes, Ne.symm quotientRemainder]
    · simp [tapes, MachineCopy.forkTapes, hq, hr]

theorem update_remainder (source quotient remainder : K) (base : K → List Bool)
    (input quotientWord remainderWord replacement : List Bool) :
    Function.update (tapes source quotient remainder base input quotientWord remainderWord)
      remainder replacement = tapes source quotient remainder base input quotientWord replacement := by
  simp [tapes, MachineCopy.forkTapes]

theorem scanAux_true (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (base : K → List Bool) (input quotientWord remainderWord : List Bool)
    (ambient : σ) (r : Fin d) (register : Option Bool) :
    TM2.stepAux (scanLoop d positive source quotient scanLabel emitterLabel)
      ((ambient, r), register)
      (tapes source quotient remainder base (true :: input) quotientWord remainderWord) =
      ⟨some scanLabel, ((ambient, nextResidue d positive r), some true),
        tapes source quotient remainder base input
          (if (nextResidue d positive r).val = 0 then true :: quotientWord else quotientWord)
          remainderWord⟩ := by
  by_cases hcarry : (nextResidue d positive r).val = 0 <;>
    simp [scanLoop, TM2.stepAux, sourceQuotient, sourceRemainder, quotientRemainder,
      update_source, update_quotient, hcarry]

theorem scanAux_false (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (base : K → List Bool) (input quotientWord remainderWord : List Bool)
    (ambient : σ) (r : Fin d) (register : Option Bool) :
    TM2.stepAux (scanLoop d positive source quotient scanLabel emitterLabel)
      ((ambient, r), register)
      (tapes source quotient remainder base (false :: input) quotientWord remainderWord) =
      ⟨some (emitterLabel r), ((ambient, r), some false),
        tapes source quotient remainder base (false :: input) quotientWord remainderWord⟩ := by
  simp [scanLoop, TM2.stepAux, sourceQuotient, sourceRemainder, quotientRemainder,
    update_source]

/-- A scan transition updates the actual quotient and finite residue of the
already-processed count. The count itself is a proof index, not machine state. -/
theorem scanStep_succ (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (base : K → List Bool) (n k : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, residue d positive k), register),
      unaryTapes source quotient remainder base (n + 1) (k / d) 0
        sourceSuffix quotientSuffix remainderSuffix⟩ =
      some ⟨some scanLabel, ((ambient, residue d positive (k + 1)), some true),
        unaryTapes source quotient remainder base n ((k + 1) / d) 0
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  change some (TM2.stepAux (program scanLabel) ((ambient, residue d positive k), register)
    (unaryTapes source quotient remainder base (n + 1) (k / d) 0
      sourceSuffix quotientSuffix remainderSuffix)) = _
  rw [atScan]
  simp only [unaryTapes, encodeWord, List.replicate_succ, List.cons_append]
  rw [scanAux_true d positive source quotient remainder sourceQuotient sourceRemainder
    quotientRemainder, nextResidue_residue]
  by_cases hmod : (k + 1) % d = 0
  · rw [Nat.succ_div_of_mod_eq_zero hmod]
    simp [residue, hmod, List.replicate_succ]
  · rw [Nat.succ_div_of_mod_ne_zero hmod]
    simp [residue, hmod]

theorem scanStep_zero (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (base : K → List Bool) (q : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (r : Fin d) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, r), register),
      unaryTapes source quotient remainder base 0 q 0
        sourceSuffix quotientSuffix remainderSuffix⟩ =
      some ⟨some (emitterLabel r), ((ambient, r), some false),
        unaryTapes source quotient remainder base 0 q 0
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  change some (TM2.stepAux (program scanLabel) ((ambient, r), register)
    (unaryTapes source quotient remainder base 0 q 0
      sourceSuffix quotientSuffix remainderSuffix)) = _
  rw [atScan]
  simp only [unaryTapes, encodeWord, List.replicate_zero, List.nil_append,
    List.singleton_append]
  rw [scanAux_false d positive source quotient remainder sourceQuotient sourceRemainder
    quotientRemainder]

theorem emitterStep (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (emitterLabel : Fin d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atEmitter : ∀ r, program (emitterLabel r) = emitter d positive remainder exit r)
    (base : K → List Bool) (n q : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (r : Fin d) (register : Option Bool) :
    TM2.step program ⟨some (emitterLabel r), ((ambient, r), register),
      unaryTapes source quotient remainder base n q 0
        sourceSuffix quotientSuffix remainderSuffix⟩ =
      some ⟨exit, ((ambient, residue d positive 0), none),
        unaryTapes source quotient remainder base n q r.val
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  change some (TM2.stepAux (program (emitterLabel r)) ((ambient, r), register)
    (unaryTapes source quotient remainder base n q 0
      sourceSuffix quotientSuffix remainderSuffix)) = _
  rw [atEmitter]
  unfold emitter
  rw [stepAux_pushWord]
  simp only [unaryTapes, MachineCopy.forkTapes_right, List.reverse_replicate]
  rw [update_remainder]
  cases exit <;>
    simp [TM2.stepAux, Reduction.MachineTransfer.exitAt, encodeWord, List.append_assoc]

/-- The general invariant starts at the finite residue and unary quotient of
`k`, then scans `n` additional input bits. It is an actual execution theorem. -/
theorem trace_fromCount (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (exit : Option Λ) (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (atEmitter : ∀ r, program (emitterLabel r) = emitter d positive remainder exit r)
    (base : K → List Bool) (n k : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 2]
      (some ⟨some scanLabel, ((ambient, residue d positive k), register),
        unaryTapes source quotient remainder base n (k / d) 0
          sourceSuffix quotientSuffix remainderSuffix⟩) =
      some ⟨exit, ((ambient, residue d positive 0), none),
        unaryTapes source quotient remainder base 0 ((k + n) / d) ((k + n) % d)
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  induction n generalizing k register with
  | zero =>
    change (TM2.step program ⟨some scanLabel, ((ambient, residue d positive k), register),
      unaryTapes source quotient remainder base 0 (k / d) 0
        sourceSuffix quotientSuffix remainderSuffix⟩).bind (TM2.step program) = _
    rw [scanStep_zero d positive source quotient remainder sourceQuotient sourceRemainder
      quotientRemainder scanLabel emitterLabel program atScan, Option.bind_some]
    simpa only [residue, Nat.add_zero] using
      emitterStep d positive source quotient remainder emitterLabel exit program atEmitter
        base 0 (k / d) sourceSuffix quotientSuffix remainderSuffix ambient
        (residue d positive k) (some false)
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[n + 2]
      (TM2.step program ⟨some scanLabel, ((ambient, residue d positive k), register),
        unaryTapes source quotient remainder base (n + 1) (k / d) 0
          sourceSuffix quotientSuffix remainderSuffix⟩) = _
    rw [scanStep_succ d positive source quotient remainder sourceQuotient sourceRemainder
      quotientRemainder scanLabel emitterLabel program atScan]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1) (some true)

/-- Exact unary quotient and remainder, with both output counters initially zero. -/
theorem divModTrace (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (exit : Option Λ) (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (atEmitter : ∀ r, program (emitterLabel r) = emitter d positive remainder exit r)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 2]
      (some ⟨some scanLabel, ((ambient, residue d positive 0), register),
        unaryTapes source quotient remainder base n 0 0
          sourceSuffix quotientSuffix remainderSuffix⟩) =
      some ⟨exit, ((ambient, residue d positive 0), none),
        unaryTapes source quotient remainder base 0 (n / d) (n % d)
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  simpa only [Nat.zero_add, Nat.zero_div] using
    trace_fromCount d positive source quotient remainder sourceQuotient sourceRemainder
      quotientRemainder scanLabel emitterLabel exit program atScan atEmitter base n 0
      sourceSuffix quotientSuffix remainderSuffix ambient register

/-- Stop just before emission, retaining the final finite residue as actual control. -/
theorem scanTrace_fromCount (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (base : K → List Bool) (n k : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some scanLabel, ((ambient, residue d positive k), register),
        unaryTapes source quotient remainder base n (k / d) 0
          sourceSuffix quotientSuffix remainderSuffix⟩) =
      some ⟨some (emitterLabel (residue d positive (k + n))),
        ((ambient, residue d positive (k + n)), some false),
        unaryTapes source quotient remainder base 0 ((k + n) / d) 0
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  induction n generalizing k register with
  | zero =>
    simpa only [Nat.zero_add, Nat.add_zero, Function.iterate_one,
      MachineComposition.advance_some] using
      scanStep_zero d positive source quotient remainder sourceQuotient sourceRemainder
        quotientRemainder scanLabel emitterLabel program atScan base (k / d)
        sourceSuffix quotientSuffix remainderSuffix ambient (residue d positive k) register
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[n + 1]
      (TM2.step program ⟨some scanLabel, ((ambient, residue d positive k), register),
        unaryTapes source quotient remainder base (n + 1) (k / d) 0
          sourceSuffix quotientSuffix remainderSuffix⟩) = _
    rw [scanStep_succ d positive source quotient remainder sourceQuotient sourceRemainder
      quotientRemainder scanLabel emitterLabel program atScan]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1) (some true)

theorem emitterWithFinishStep [Fintype σ] (d : Nat) (positive : 0 < d)
    (source quotient remainder : K) (emitterLabel : Fin d → Λ) (exit : Option Λ)
    (finish : σ → Fin d → σ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atEmitter : ∀ r, program (emitterLabel r) =
      emitterWithFinish d positive remainder exit finish r)
    (base : K → List Bool) (n q : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (r : Fin d) (register : Option Bool) :
    TM2.step program ⟨some (emitterLabel r), ((ambient, r), register),
      unaryTapes source quotient remainder base n q 0
        sourceSuffix quotientSuffix remainderSuffix⟩ =
      some ⟨exit, ((finish ambient r, residue d positive 0), none),
        unaryTapes source quotient remainder base n q r.val
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  change some (TM2.stepAux (program (emitterLabel r)) ((ambient, r), register)
    (unaryTapes source quotient remainder base n q 0
      sourceSuffix quotientSuffix remainderSuffix)) = _
  rw [atEmitter]
  unfold emitterWithFinish
  rw [stepAux_pushWord]
  simp only [unaryTapes, MachineCopy.forkTapes_right, List.reverse_replicate]
  rw [update_remainder]
  cases exit <;>
    simp [TM2.stepAux, Reduction.MachineTransfer.exitAt, encodeWord, List.append_assoc]

/-- The callback is a fixed finite-control table, applied in the existing emitter transition. -/
theorem divModTraceWithFinish [Fintype σ] (d : Nat) (positive : 0 < d)
    (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (exit : Option Λ) (finish : σ → Fin d → σ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (atEmitter : ∀ r, program (emitterLabel r) =
      emitterWithFinish d positive remainder exit finish r)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 2]
      (some ⟨some scanLabel, ((ambient, residue d positive 0), register),
        unaryTapes source quotient remainder base n 0 0
          sourceSuffix quotientSuffix remainderSuffix⟩) =
      some ⟨exit, ((finish ambient (residue d positive n), residue d positive 0), none),
        unaryTapes source quotient remainder base 0 (n / d) (n % d)
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  have hscan := scanTrace_fromCount d positive source quotient remainder
    sourceQuotient sourceRemainder quotientRemainder scanLabel emitterLabel program atScan
    base n 0 sourceSuffix quotientSuffix remainderSuffix ambient register
  simp only [Nat.zero_add, Nat.zero_div] at hscan
  rw [Function.iterate_succ_apply', hscan, MachineComposition.advance_some]
  exact emitterWithFinishStep d positive source quotient remainder emitterLabel exit finish
    program atEmitter base 0 (n / d) sourceSuffix quotientSuffix remainderSuffix ambient
    (residue d positive n) (some false)

theorem divModFromTapesWithFinish [Fintype σ] (d : Nat) (positive : 0 < d)
    (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (exit : Option Λ) (finish : σ → Fin d → σ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (atEmitter : ∀ r, program (emitterLabel r) =
      emitterWithFinish d positive remainder exit finish r)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (sourceInput : base source = encodeWord n ++ sourceSuffix)
    (quotientInput : base quotient = encodeWord 0 ++ quotientSuffix)
    (remainderInput : base remainder = encodeWord 0 ++ remainderSuffix)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 2]
      (some ⟨some scanLabel, ((ambient, residue d positive 0), register), base⟩) =
      some ⟨exit, ((finish ambient (residue d positive n), residue d positive 0), none),
        unaryTapes source quotient remainder base 0 (n / d) (n % d)
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  have hbase : unaryTapes source quotient remainder base n 0 0 sourceSuffix quotientSuffix
      remainderSuffix = base := by
    simp only [unaryTapes, ← sourceInput, ← quotientInput, ← remainderInput,
      MachineCopy.forkTapes_self]
  have h := divModTraceWithFinish d positive source quotient remainder sourceQuotient
    sourceRemainder quotientRemainder scanLabel emitterLabel exit finish program atScan
    atEmitter base n sourceSuffix quotientSuffix remainderSuffix ambient register
  rw [hbase] at h
  exact h

end UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod

end

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

/-- Actual ambient-program execution. `code` fixes the concrete instructions
at each placed label; it does not assume any execution or semantic behavior.
The frame records an empty working copy at both endpoints. -/
theorem traceAt (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (code : ∀ label, target (labels label) = statement tape labels exit label)
    (base : K → List Bool) (values : List Nat)
    (tableWord : base (tape 0) = encodeWords values)
    (scratchEmpty : base (tape 4) = [])
    (index value : Nat) (selected : values[index]? = some value)
    (indexSuffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step target))^[steps values index]
      (some ⟨some (labels (.run .copyFirst)), (ambient, register),
        MachinePreservingLookup.initialTapes tape base index indexSuffix [] output⟩) =
      some ⟨exit, (ambient, none),
        MachinePreservingLookup.initialTapes tape base 0 indexSuffix []
          (encodeWord value ++ output)⟩ := by
  have hd (a b : Fin 5) (hne : a ≠ b) : tape a ≠ tape b :=
    fun h => hne (distinct h)
  have raw := MachinePreservingLookup.preservingLookupTrace tape distinct
    MachinePreservingLookup.Label.copyFirst MachinePreservingLookup.Label.copySecond
    MachinePreservingLookup.Label.lookup none (MachinePreservingLookup.program tape)
    rfl rfl (fun _ => rfl) base values tableWord scratchEmpty index value selected
    indexSuffix [] output ambient register
  have run := MachineSubroutine.trace (fun label => labels (.run label))
    (some (labels .cleanup)) (MachinePreservingLookup.program tape) target
    (fun label => code (.run label))
    (2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values index + 1)
    _ _ raw
  simp only [MachineSubroutine.configuration, MachineSubroutine.label] at run
  have cleanup := MachineDrain.drainTrace (tape 2) (labels .cleanup) exit target
    (code .cleanup)
    (MachinePreservingLookup.finalTapes tape base values index value indexSuffix [] output)
    (encodeWords (values.drop (index + 1))) ambient none
  have word : MachinePreservingLookup.finalTapes tape base values index value
      indexSuffix [] output (tape 2) = encodeWords (values.drop (index + 1)) := by
    simp only [MachinePreservingLookup.finalTapes,
      MachineLookup.tapes_source _ _ _ (hd 2 3 (by decide)), List.append_nil]
  have start : Function.update
      (MachinePreservingLookup.finalTapes tape base values index value indexSuffix [] output)
      (tape 2) (encodeWords (values.drop (index + 1))) =
      MachinePreservingLookup.finalTapes tape base values index value indexSuffix [] output := by
    rw [← word, Function.update_eq_self]
  have finish : Function.update
      (MachinePreservingLookup.finalTapes tape base values index value indexSuffix [] output)
      (tape 2) [] = MachinePreservingLookup.initialTapes tape base 0 indexSuffix []
        (encodeWord value ++ output) := by
    unfold MachinePreservingLookup.finalTapes MachinePreservingLookup.initialTapes
    rw [MachineLookup.update_source _ _ _ (hd 2 3 (by decide))]
  rw [start, finish] at cleanup
  rw [show steps values index =
      ((encodeWords (values.drop (index + 1))).length + 1) +
        (2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values index + 1) by
        unfold steps
        omega,
    Function.iterate_add_apply, run]
  exact cleanup

/-- The framing representation is the caller's exact tape state whenever its
index and work tape contain the specified index and an empty list. -/
theorem initialTapes_eq (tape : Fin 5 → K) (base : K → List Bool)
    (index : Nat) (indexSuffix : List Bool)
    (counterWord : base (tape 1) = encodeWord index ++ indexSuffix)
    (workEmpty : base (tape 2) = []) :
    MachinePreservingLookup.initialTapes tape base index indexSuffix [] (base (tape 3)) =
      base := by
  simp only [MachinePreservingLookup.initialTapes, MachineLookup.tapes,
    ← counterWord, ← workEmpty, Function.update_eq_self]

/-- A convenience interface starting from the caller's exact configuration. -/
theorem traceAt_fromTapes (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (code : ∀ label, target (labels label) = statement tape labels exit label)
    (base : K → List Bool) (values : List Nat)
    (tableWord : base (tape 0) = encodeWords values)
    (scratchEmpty : base (tape 4) = [])
    (index value : Nat) (selected : values[index]? = some value)
    (indexSuffix : List Bool)
    (counterWord : base (tape 1) = encodeWord index ++ indexSuffix)
    (workEmpty : base (tape 2) = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step target))^[steps values index]
      (some ⟨some (labels (.run .copyFirst)), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        MachinePreservingLookup.initialTapes tape base 0 indexSuffix []
          (encodeWord value ++ base (tape 3))⟩ := by
  have h := traceAt tape distinct labels exit target code base values tableWord scratchEmpty
    index value selected indexSuffix (base (tape 3)) ambient register
  rw [initialTapes_eq tape base index indexSuffix counterWord workEmpty] at h
  exact h

end UniqueGamesTheorem.Foundations.Complexity.MachinePreservingLookupClean

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

namespace UniqueGamesTheorem.Foundations.PCP.ExpanderRowControl

open ExpanderTables

theorem firstAddress_eq_rowIndex {v d : Nat} (vertex : Fin v) (s : Control d) :
    firstAddress vertex.val s =
      (rowIndex v (degree d) (vertex,firstOffset s)).val := by
  rw [rowIndex_val]
  exact Nat.add_comm _ _

theorem secondAddress_eq_rowIndex {v d : Nat} (vertex : Fin v) (s : Control d) :
    secondAddress vertex.val s =
      (rowIndex v (degree d) (vertex,secondOffset s)).val := by
  rw [rowIndex_val]
  exact Nat.add_comm _ _

end UniqueGamesTheorem.Foundations.PCP.ExpanderRowControl

end

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

/-- The exact zero-based lookup hypothesis consumed by the machine lookup API. -/
theorem rotationWords_getElem? (table : Table v d) (i : Fin (v * d)) :
    (rotationWords table)[i.val]? = some (reverseIndex table i).val := by
  apply List.getElem?_eq_some_iff.mpr
  exact ⟨by simpa only [rotationWords_length] using i.isLt,
    rotationWords_getElem table i.val i.isLt⟩

/-- The serialized reverse index decodes to the actual table lookup. -/
theorem rotationWords_lookup (table : Table v d) (x : Fin v × Fin d) :
    (rotationWords table)[(rowIndex v d x).val]? =
      some (rowIndex v d (lookup table x)).val := by
  simpa only [lookup, Equiv.apply_symm_apply] using
    rotationWords_getElem? table (rowIndex v d x)

/-- Both the input and output use port-first mixed-radix row coordinates. -/
theorem rotationWords_row_order (table : Table v d) (x : Fin v × Fin d) :
    (rotationWords table)[x.2.val + d * x.1.val]? =
      some ((lookup table x).2.val + d * (lookup table x).1.val) := by
  simpa only [rowIndex_val] using rotationWords_lookup table x

/-- Complete raw-row serialization bound, with no discarded delimiter or prefix. -/
theorem encode_rotationWords_length_le (table : Table v d) :
    (encodeWords (rotationWords table)).length ≤ (v * d) * (v * d + 1) := by
  calc
    _ ≤ (rotationWords table).length * (v * d + 1) :=
      Complexity.encodeWords_length_le _ _
        (fun n hn => (rotationWords_entry_lt table n hn).le)
    _ = _ := by rw [rotationWords_length]

end UniqueGamesTheorem.Foundations.PCP.ExpanderTableWords

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingRegularTablesLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Executable degree replacement on the actual finite constraint rows

Vertices are numbered by first listing the original darts, then the dummy
darts in original-vertex order. Each local cloud uses its explicit filtered
dart list. Internal ports carry equality; the final port retains the original
constraint, or an always-accepting loop at a dummy dart. The constructor is
total, including inputs with no darts. The fixed base expander is supplied
once; every input-dependent operation is an explicit finite calculation.
-/

/-!
# Exact serialized family tables at actual regularization vertices

The geometric family maps request zero to a one-vertex table. Empty clouds in
regularization instead remain empty. The bridge therefore requires positive
cloud size, derived here from each actual original or dummy vertex.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingFamilyBridge

open PreprocessingCloudIndex PreprocessingRegularTables ExpanderTableWords
open UniqueGamesTheorem.Foundations.Complexity (encodeWords)

/-- Transporting only the size equality leaves every serialized rotor entry
unchanged; no relabeling or alternative numbering is introduced. -/
theorem rotationWords_resizeTable {n m q : Nat} (h : n = m)
    (table : ExpanderTables.Table n q) :
    rotationWords (resizeTable h table) = rotationWords table := by
  cases h
  rfl

/-- This left side is definitionally the output `MachineRegularFamily.rotor`
for the request on its physical core tape 4. The right side is exactly the
archive expected on core tape 7 by the internal-row machine. -/
theorem familyRotor_eq_familyCloudTable (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (hk : 0 < cloudSize t v) :
    encodeWords (rotationWords (ExpanderTables.family H
      (PreprocessingLevels.boundedLevel (cloudSize t v)))) =
      encodeWords (rotationWords (familyCloudTable H t v)) := by
  unfold familyCloudTable
  rw [dite_eq_right (Nat.ne_of_gt hk)]
  erw [rotationWords_resizeTable]
  rfl

/-- An empty cloud has no padding vertices either. -/
theorem padding_zero_of_cloudSize_zero (t : GraphTables.Table) (v : Fin t.vertices)
    (hk : cloudSize t v = 0) : padding t v = 0 := by
  simp only [padding, hk, PreprocessingLevels.cloudPaddedSize_zero, Nat.sub_zero]

/-- Every actual dummy vertex also belongs to a positive original cloud. -/
theorem cloudSize_pos_of_dummy (t : GraphTables.Table) (v : Fin t.vertices)
    (j : Fin (padding t v)) : 0 < cloudSize t v := by
  by_contra h
  have hk := Nat.eq_zero_of_not_pos h
  have hp := padding_zero_of_cloudSize_zero t v hk
  have hj := j.isLt
  omega

end UniqueGamesTheorem.Foundations.PCP.PreprocessingFamilyBridge

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingPaddingOffsets
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
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

theorem paddingOrder_val {n : Nat} (padding : Fin n → Nat)
    (v : Fin n) (j : Fin (padding v)) :
    (PreprocessingRegularTables.paddingOrder padding ⟨v, j⟩).val =
      offset padding v.val + j.val := by
  change (paddingList padding).idxOf ⟨v, j⟩ = _
  have h := sigma_idxOf padding (List.finRange n) v (List.mem_finRange v) j
  simpa only [List.idxOf_finRange, paddingList, offset] using h

theorem vertexOrder_dummy_val (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) (v : Fin t.vertices) (j : Fin (padding v)) :
    (vertexOrder t padding (Sum.inr ⟨v, j⟩)).val =
      t.darts + offset padding v.val + j.val := by
  rw [vertexOrder_dummy, paddingOrder_val]
  omega

end UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingOffsets

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingPaddingTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Executable whole-vertex padding of regular constraint tables

The first `n` vertex rows retain their old rotation and complete relation
tables. Every additional vertex has one self-reversing, always-accepting loop
at each port. An explicit finite sum equivalence identifies these stored rows
with `VertexPadding.pad`; rejection counts are preserved for every labeling.

The construction materializes finite vectors. No machine runtime bound is
claimed here.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables

open PoweringWalks PortTables

variable {n m d : Nat}

theorem reverseIndex_pad_old (table : Table n d) (h : n ≤ m)
    (v : Fin n) (p : Fin d) :
    (pad table h).reverseIndex[rowIndex m d (v.castLE h, p)] =
      rowIndex m d ((rotation table (v, p)).1.castLE h, (rotation table (v, p)).2) := by
  rw [← rowIndex_rotation, rotation_pad_old]

theorem relation_ext {r s : GraphTables.RelationTable}
    (h : ∀ a b, GraphTables.relationAt r a b = GraphTables.relationAt s a b) : r = s := by
  apply Vector.ext
  intro i hi
  simpa only [GraphTables.relationAt, Prod.eta, Equiv.apply_symm_apply,
    Fin.getElem_fin] using
    h (GraphTables.relationIndex.symm ⟨i, hi⟩).1
      (GraphTables.relationIndex.symm ⟨i, hi⟩).2

/-- The entire old 4096-bit relation row is retained. -/
theorem relations_pad_old (table : Table n d) (h : n ≤ m)
    (v : Fin n) (p : Fin d) :
    (pad table h).relations[rowIndex m d (v.castLE h, p)] =
      table.relations[rowIndex n d (v, p)] := by
  apply relation_ext
  intro a b
  exact accepts_pad_old table h v p a b

end UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineUnaryLessAtLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
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

theorem scan_step_zero_left (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program scanLabel = scan slots scanLabel restoreLabel)
    (base : K → List Bool) (b : Nat) (leftSuffix rightSuffix savedLeft savedRight : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, flag), register),
      tapes slots base (encodeWord 0 ++ leftSuffix) (encodeWord b ++ rightSuffix) savedLeft savedRight⟩ =
      some ⟨some restoreLabel, ((ambient, decide (0 < b)), none),
        tapes slots base (encodeWord 0 ++ leftSuffix) (encodeWord b ++ rightSuffix) savedLeft savedRight⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  cases b <;> simp [scan, stop, TM2.stepAux, encodeWord, List.replicate_succ]

theorem scan_step_zero_right (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program scanLabel = scan slots scanLabel restoreLabel)
    (base : K → List Bool) (a : Nat) (leftSuffix rightSuffix savedLeft savedRight : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, flag), register),
      tapes slots base (encodeWord (a + 1) ++ leftSuffix) (encodeWord 0 ++ rightSuffix) savedLeft savedRight⟩ =
      some ⟨some restoreLabel, ((ambient, false), none),
        tapes slots base (encodeWord (a + 1) ++ leftSuffix) (encodeWord 0 ++ rightSuffix) savedLeft savedRight⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  simp [scan, stop, TM2.stepAux, encodeWord, List.replicate_succ]

theorem scan_step_succ (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program scanLabel = scan slots scanLabel restoreLabel)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix savedLeft savedRight : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, flag), register),
      tapes slots base (encodeWord (a + 1) ++ leftSuffix) (encodeWord (b + 1) ++ rightSuffix)
        savedLeft savedRight⟩ =
      some ⟨some scanLabel, ((ambient, flag), some true),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix)
          (true :: savedLeft) (true :: savedRight)⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  simp [scan, TM2.stepAux, encodeWord, List.replicate_succ]

theorem scanTrace (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program scanLabel = scan slots scanLabel restoreLabel)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix savedLeft savedRight : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step program))^[min a b + 1]
      (some ⟨some scanLabel, ((ambient, flag), register),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix) savedLeft savedRight⟩) =
      some ⟨some restoreLabel, ((ambient, decide (a < b)), none),
        tapes slots base (encodeWord (a - b) ++ leftSuffix) (encodeWord (b - a) ++ rightSuffix)
          (List.replicate (min a b) true ++ savedLeft) (List.replicate (min a b) true ++ savedRight)⟩ := by
  induction a generalizing b savedLeft savedRight register with
  | zero =>
    simpa using scan_step_zero_left slots scanLabel restoreLabel program atScan base b
      leftSuffix rightSuffix savedLeft savedRight ambient flag register
  | succ a ih =>
    cases b with
    | zero =>
      simpa using scan_step_zero_right slots scanLabel restoreLabel program atScan base a
        leftSuffix rightSuffix savedLeft savedRight ambient flag register
    | succ b =>
      have hm : min (a + 1) (b + 1) = min a b + 1 := by omega
      rw [hm, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [scan_step_succ slots scanLabel restoreLabel program atScan, ih]
      have hsave (xs : List Bool) :
          List.replicate (min a b) true ++ true :: xs =
            List.replicate (min a b + 1) true ++ xs := by
        simp [List.replicate_add, List.append_assoc]
      simp only [hsave, Nat.add_sub_add_right, Nat.add_lt_add_iff_right]

theorem comparisonTrace (slots : Fin 4 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step program))^[steps a b]
      (some ⟨some (labels .scan), ((ambient, flag), register),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix) [] []⟩) =
      some ⟨exit, ((ambient, decide (a < b)), none),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix) [] []⟩ := by
  have hscan := scanTrace slots (labels .scan) (labels .restoreLeft) program (atLabels .scan)
    base a b leftSuffix rightSuffix [] [] ambient flag register
  simp only [List.append_nil] at hscan
  have hwordLeft : List.replicate (min a b) true ++ (encodeWord (a - b) ++ leftSuffix) =
      encodeWord a ++ leftSuffix := by
    rw [MachineUnaryAffineAt.prepend_replicate_word,
      show min a b + (a - b) = a by omega]
  have hwordRight : List.replicate (min a b) true ++ (encodeWord (b - a) ++ rightSuffix) =
      encodeWord b ++ rightSuffix := by
    rw [MachineUnaryAffineAt.prepend_replicate_word,
      show min a b + (b - a) = b by omega]
  let middle := tapes slots base (encodeWord (a - b) ++ leftSuffix)
    (encodeWord (b - a) ++ rightSuffix) (List.replicate (min a b) true) (List.replicate (min a b) true)
  have hleft := Reduction.MachineTransfer.transferAt_fromTapes
    (Γ := fun _ : K => Bool) (σ := σ × Bool) (slots 2) (slots 0)
    (slots.injective.ne (by decide)) id false (labels .restoreLeft) (some (labels .restoreRight))
    program (by simpa only [statement] using atLabels .restoreLeft)
    middle (ambient, decide (a < b)) none
  change (advance (TM2.step program))^[(middle (slots 2)).length + 1]
    (some ⟨some (labels .restoreLeft), ((ambient, decide (a < b)), none), middle⟩) = _ at hleft
  simp only [middle, tapes_savedLeft, tapes_left, List.length_replicate, List.reverse_replicate,
    List.map_id, hwordLeft, transferLeft_tapes] at hleft
  let afterLeft := tapes slots base (encodeWord a ++ leftSuffix)
    (encodeWord (b - a) ++ rightSuffix) [] (List.replicate (min a b) true)
  have hright := Reduction.MachineTransfer.transferAt_fromTapes
    (Γ := fun _ : K => Bool) (σ := σ × Bool) (slots 3) (slots 1)
    (slots.injective.ne (by decide)) id false (labels .restoreRight) exit
    program (by simpa only [statement] using atLabels .restoreRight)
    afterLeft (ambient, decide (a < b)) none
  change (advance (TM2.step program))^[(afterLeft (slots 3)).length + 1]
    (some ⟨some (labels .restoreRight), ((ambient, decide (a < b)), none), afterLeft⟩) = _ at hright
  simp only [afterLeft, tapes_savedRight, tapes_right, List.length_replicate, List.reverse_replicate,
    List.map_id, hwordRight, transferRight_tapes] at hright
  have hfirst : (advance (TM2.step program))^[(min a b + 1) + (min a b + 1)]
      (some ⟨some (labels .scan), ((ambient, flag), register),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix) [] []⟩) =
      some ⟨some (labels .restoreRight), ((ambient, decide (a < b)), none), afterLeft⟩ := by
    rw [Function.iterate_add_apply, hscan]
    exact hleft
  rw [show steps a b = (min a b + 1) + ((min a b + 1) + (min a b + 1)) by
    unfold steps; omega, Function.iterate_add_apply, hfirst]
  exact hright

/-- Actual comparison on a caller frame: both complete operand tapes and all
other tapes are preserved, both scratch tapes remain empty, and the finite
result flag is precisely the strict comparison of the two unary values. -/
theorem lessThanTrace (slots : Fin 4 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix : List Bool)
    (leftWord : base (slots 0) = encodeWord a ++ leftSuffix)
    (rightWord : base (slots 1) = encodeWord b ++ rightSuffix)
    (leftEmpty : base (slots 2) = []) (rightEmpty : base (slots 3) = [])
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step program))^[steps a b]
      (some ⟨some (labels .scan), ((ambient, flag), register), base⟩) =
      some ⟨exit, ((ambient, decide (a < b)), none), base⟩ := by
  have h := comparisonTrace slots labels exit program atLabels base a b leftSuffix rightSuffix
    ambient flag register
  have hframe := tapes_self slots base
  rw [leftWord, rightWord, leftEmpty, rightEmpty] at hframe
  rw [hframe] at h
  exact h

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
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingInternalRows
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_append _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_nil _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_append _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_nil _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_done _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_head _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_relation _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_reverseIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_words _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRows_acceptsAt _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRows_get _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRows_reverseAt _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_headIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_headValue _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_relation _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_reverseIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_row _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_head _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tableBits _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tableWords _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.boolView_outer _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.caller_initialState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.caller_normalizeState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.clearRegister_initialState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.program_outer _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.program_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.tableExecution_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamilyBounds.familyBudget_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamilyBounds.resizeSum_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.program_firstEmit _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.program_outputEmit _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.program_secondEmit _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.accumulatedVertices_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.caller_boundaryState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.caller_prepareState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.caller_resetState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.caller_rowAfterState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.clearRegister_boundaryState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.prepareState_boundaryState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.program_outer _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.program_row _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.rowAfterState_position _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.rowExecution_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.initialExtra_scratch _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.initialExtra_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRow.rowBlock_at _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Relations.oldPredicate_relationAt _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Relations.relationAt_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.build_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.build_vertices _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.rowList_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.rows_at _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.generatedWords_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.priorVertices_full _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.priorVertices_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.vertexWords_drop_full _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.vertexWords_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringRowData.basePredicate_transposeBits _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringRowData.basePredicate_walkBits _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringRowData.leftMatches_walkBits _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringRowData.rightMatches_walkBits _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringRowData.rowBits_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTableLayout.vertexRows_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTables.table_vertices _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Preprocessing.graph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.accepts_materialize _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.lazy_accepts_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.lazy_accepts_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.overlay_accepts_expander _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.overlay_accepts_old _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.accepts_pad _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.accepts_pad_new _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.accepts_pad_old _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.baseGraph_pad _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_new _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_old _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.rotation_pad _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.rotation_pad_new _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.rotation_pad_old _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Regularization.graph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_reverse_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_reverse_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.paddedG_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows

open DegreeReplacement PreprocessingCloudIndex PreprocessingRegularTables

variable (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
variable (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)

/-- The one actual cloud-table lookup used by this internal row. -/
def localStep (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    Fin (cloudSize t v + padding v) × Fin q :=
  ExpanderTables.lookup (tables v) (paddedCloudRank t padding v x, p)

def rowIndex (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    Fin (vertexCount t padding * (q + 1)) :=
  PortTables.rowIndex (vertexCount t padding) (q + 1)
    (vertexOrder t padding x.val, portOrder q (.inl p))

/-- This is a row read from the actual serialized output table. -/
def row (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    GraphTables.DartRow (vertexCount t padding) (vertexCount t padding * (q + 1)) :=
  (PortTables.flatRows (ofCloudTables t padding tables))[rowIndex t padding v x p]

/-- The fixed, complete 64-label equality predicate. -/
def equalityRelation : GraphTables.RelationTable :=
  GraphTables.relationOf (fun a b => decide (a = b))

@[simp] theorem equalityRelation_apply (a b : GraphTables.Label) :
    GraphTables.relationAt equalityRelation a b = decide (a = b) :=
  GraphTables.relationAt_relationOf _ a b

theorem relation_ext {r s : GraphTables.RelationTable}
    (h : ∀ a b, GraphTables.relationAt r a b = GraphTables.relationAt s a b) : r = s := by
  apply Vector.ext
  intro i hi
  simpa only [GraphTables.relationAt, Prod.eta, Equiv.apply_symm_apply,
    Fin.getElem_fin] using
    h (GraphTables.relationIndex.symm ⟨i, hi⟩).1
      (GraphTables.relationIndex.symm ⟨i, hi⟩).2

/-- Equality is the entire stored relation vector, not only one tested entry. -/
theorem relations_internal (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (ofCloudTables t padding tables).relations[rowIndex t padding v x p] = equalityRelation := by
  apply relation_ext
  intro a b
  rw [equalityRelation_apply]
  exact accepts_internal t padding tables x.val p a b

@[simp] theorem row_tail (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (row t padding tables v x p).tail.val = (vertexOrder t padding x.val).val := by
  simp only [row, rowIndex, PortTables.flatRows, Vector.getElem_ofFn,
    Fin.getElem_fin, Fin.eta, Equiv.symm_apply_apply]

@[simp] theorem row_relation (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (row t padding tables v x p).relation = equalityRelation := by
  simpa only [row, PortTables.flatRows, Vector.getElem_ofFn, Fin.getElem_fin] using
    relations_internal t padding tables v x p

@[simp] theorem localStep_original (v : Fin t.vertices) (x : Cloud (GraphTables.semantics t) v)
    (p : Fin q) :
    localStep t padding tables v (paddedOld t padding v x) p =
      ExpanderTables.lookup (tables v) (Fin.castAdd (padding v) (cloudRank t v x), p) := rfl

@[simp] theorem localStep_dummy (v : Fin t.vertices) (j : Fin (padding v)) (p : Fin q) :
    localStep t padding tables v (paddedNew t padding v j) p =
      ExpanderTables.lookup (tables v) (Fin.natAdd (cloudSize t v) j, p) := rfl

@[simp] theorem row_tail_original (v : Fin t.vertices) (x : Cloud (GraphTables.semantics t) v)
    (p : Fin q) :
    (row t padding tables v (paddedOld t padding v x) p).tail.val = x.val.val := by
  rw [row_tail]
  rfl

@[simp] theorem row_tail_dummy (v : Fin t.vertices) (j : Fin (padding v)) (p : Fin q) :
    (row t padding tables v (paddedNew t padding v j) p).tail.val =
      t.darts + PreprocessingPaddingOffsets.offset padding v.val + j.val := by
  rw [row_tail]
  exact PreprocessingPaddingOffsets.vertexOrder_dummy_val t padding v j

/-- The global target number computed from an arbitrary returned cloud index. -/
def selectedIndex (v : Fin t.vertices) (i : Fin (cloudSize t v + padding v)) : Nat :=
  if hi : i.val < cloudSize t v then
    (cloudSelect t v ⟨i.val, hi⟩).val.val
  else t.darts + PreprocessingPaddingOffsets.offset padding v.val + (i.val - cloudSize t v)

/-- Old target indices select the original dart from its actual cloud list. -/
theorem selectedIndex_old (v : Fin t.vertices) (i : Fin (cloudSize t v + padding v))
    (hi : i.val < cloudSize t v) :
    selectedIndex t padding v i = (cloudSelect t v ⟨i.val, hi⟩).val.val := by
  simp only [selectedIndex, dite_eq_left hi]

end UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineCanonicalOutputLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt.transferLeft_tapes _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt.transferRight_tapes _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
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

def completedProgram (P : Program K Λ σ) (chosen : List K) :
    Label Λ chosen → TM2.Stmt (fun _ : K => Bool) (Label Λ chosen) (σ × Option Bool)
  | .inl label => extendedStmt Sum.inl (cleanupEntry chosen) (P.code label)
  | .inr (.inl label) => MachineDrainMany.instruction chosen (cleanupLabel chosen)
      (some (resetLabel chosen)) label
  | .inr (.inr _) => .load (fun _ => (P.initial, none)) .halt

/-- A fixed finite program over the same Boolean tapes as the raw machine. -/
def completedMachine (P : Program K Λ σ) (chosen : List K) : FinTM2 where
  K := K
  k₀ := P.input
  k₁ := P.output
  Γ _ := Bool
  Λ := Label Λ chosen
  main := .inl P.main
  σ := σ × Option Bool
  initialState := (P.initial, none)
  m := completedProgram P chosen

def embeddedCfg (P : Program K Λ σ) (chosen : List K)
    (cfg : (sourceMachine P).Cfg) : (completedMachine P chosen).Cfg :=
  extendedCfg Sum.inl (cleanupEntry chosen) none cfg

theorem step_simulation (P : Program K Λ σ) (chosen : List K)
    (a b : (sourceMachine P).Cfg) (step : (sourceMachine P).step a = some b) :
    (completedMachine P chosen).step (embeddedCfg P chosen a) =
      some (embeddedCfg P chosen b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => simp [FinTM2.step, TM2.step] at step
    | some label =>
      have hb : TM2.stepAux (P.code label) state tapes = b := Option.some.inj step
      rw [← hb]
      change some (TM2.stepAux
        (extendedStmt Sum.inl (cleanupEntry chosen) (P.code label)) (state, none) tapes) = _
      erw [stepAux_extended]
      rfl

@[simp] theorem embedded_init (P : Program K Λ σ) (chosen : List K) (input : List Bool) :
    embeddedCfg P chosen (initList (sourceMachine P) input) =
      initList (completedMachine P chosen) input := rfl

omit [Fintype K] [Fintype Λ] [Fintype σ] in
theorem finalTapes_eq (P : Program K Λ σ) (chosen : List K)
    (complete : ∀ k, k ∈ chosen ↔ k ≠ P.output) (base : K → List Bool) :
    MachineDrainMany.finalTapes chosen base =
      MachineDrainMany.haltTapes P.output (base P.output) := by
  funext k
  rw [MachineDrainMany.finalTapes_apply]
  by_cases h : k = P.output
  · subst k
    simp [MachineDrainMany.haltTapes, complete]
  · simp [MachineDrainMany.haltTapes, complete, h]

theorem haltList_eq (P : Program K Λ σ) (chosen : List K) (output : List Bool) :
    haltList (completedMachine P chosen) output =
      ⟨none, (P.initial, none), MachineDrainMany.haltTapes P.output output⟩ := by
  congr 1

noncomputable def completedTime (P : Program K Λ σ) (chosen : List K)
    (rawTime : Polynomial Nat) : Polynomial Nat :=
  rawTime + Polynomial.C chosen.length *
    (Polynomial.X + rawTime * Polynomial.C (Runtime.programPushBound (sourceMachine P)) + 1) + 1

theorem completedTime_eval (P : Program K Λ σ) (chosen : List K)
    (rawTime : Polynomial Nat) (n : Nat) :
    (completedTime P chosen rawTime).eval n =
      rawTime.eval n + chosen.length *
        (n + rawTime.eval n * Runtime.programPushBound (sourceMachine P) + 1) + 1 := by
  simp [completedTime]

/-- An actual raw terminal execution, with arbitrary remaining state and tapes. -/
structure TerminalRun (P : Program K Λ σ) (input output : List Bool) (budget : Nat) where
  state : σ
  tapes : K → List Bool
  execution : StateTransition.EvalsToInTime (sourceMachine P).step
    (initList (sourceMachine P) input) (some ⟨none, state, tapes⟩) budget
  output_eq : tapes P.output = output

end UniqueGamesTheorem.Foundations.Complexity.MachineCanonicalOutput

namespace UniqueGamesTheorem.Foundations.Complexity.MachineTableRows

open Turing
open PCP.GraphTables

variable {K Λ σ : Type} [DecidableEq K]

omit [DecidableEq K] in
@[simp] theorem fieldBits_length (fields : Fin 3 → K) (base : K → List Bool) :
    (fieldBits fields base).length = fieldSize fields base := by
  simp [fieldBits, fieldSize, Nat.add_assoc]

def prefixTapes (fields : Fin 3 → K) (row : K) (base : K → List Bool) : K → List Bool :=
  Function.update base row (fieldBits fields base ++ base row)

/-- The three actual preserving-copy phases, with exact tape handoffs. -/
theorem prefixTrace (fields : Fin 3 → K) (row output scratch : K)
    (hfields : ∀ i, fields i ≠ row ∧ fields i ≠ scratch)
    (hrowScratch : row ≠ scratch) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (hprogram : ∀ label, program (labels label) = routine fields row output scratch labels exit label)
    (base : K → List Bool) (hscratch : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * (fieldSize fields base + 3)]
      (some ⟨some (labels .relationRead), (ambient, register), base⟩) =
      some ⟨some (labels .appendOld), (ambient, none), prefixTapes fields row base⟩ := by
  let afterRelation := Function.update base row (base (fields 2) ++ base row)
  let afterReverse := Function.update afterRelation row
    (base (fields 1) ++ afterRelation row)
  have hfirst := MachineCopy.copyTrace (fields 2) row scratch
    (hfields 2).1 (hfields 2).2 hrowScratch false
    (labels .relationRead) (labels .relationRestore) (some (labels .reverseRead))
    program (hprogram .relationRead) (hprogram .relationRestore) base hscratch ambient register
  change (MachineComposition.advance (TM2.step program))^[2 * ((base (fields 2)).length + 1)]
    (some ⟨some (labels .relationRead), (ambient, register), base⟩) =
    some ⟨some (labels .reverseRead), (ambient, none), afterRelation⟩ at hfirst
  have hsecond := MachineCopy.copyTrace (fields 1) row scratch
    (hfields 1).1 (hfields 1).2 hrowScratch false
    (labels .reverseRead) (labels .reverseRestore) (some (labels .tailRead))
    program (hprogram .reverseRead) (hprogram .reverseRestore) afterRelation
    (by simp [afterRelation, Ne.symm hrowScratch, hscratch]) ambient none
  have hrev : afterRelation (fields 1) = base (fields 1) := by
    simp [afterRelation, (hfields 1).1]
  rw [hrev] at hsecond
  change (MachineComposition.advance (TM2.step program))^[2 * ((base (fields 1)).length + 1)]
    (some ⟨some (labels .reverseRead), (ambient, none), afterRelation⟩) =
    some ⟨some (labels .tailRead), (ambient, none), afterReverse⟩ at hsecond
  have hthird := MachineCopy.copyTrace (fields 0) row scratch
    (hfields 0).1 (hfields 0).2 hrowScratch false
    (labels .tailRead) (labels .tailRestore) (some (labels .appendOld))
    program (hprogram .tailRead) (hprogram .tailRestore) afterReverse
    (by simp [afterReverse, afterRelation, Ne.symm hrowScratch, hscratch]) ambient none
  have htail : afterReverse (fields 0) = base (fields 0) := by
    simp [afterReverse, afterRelation, (hfields 0).1]
  rw [htail] at hthird
  have hfinal : Function.update afterReverse row
      (base (fields 0) ++ afterReverse row) = prefixTapes fields row base := by
    simp [afterReverse, afterRelation, prefixTapes, fieldBits, List.append_assoc]
  rw [hfinal] at hthird
  rw [show 2 * (fieldSize fields base + 3) =
    2 * ((base (fields 0)).length + 1) +
      (2 * ((base (fields 1)).length + 1) + 2 * ((base (fields 2)).length + 1)) by
        simp only [fieldSize]; omega,
    Function.iterate_add_apply,
    Function.iterate_add_apply (m := 2 * ((base (fields 1)).length + 1))
      (n := 2 * ((base (fields 2)).length + 1)), hfirst, hsecond]
  exact hthird

theorem appendTrace (fields : Fin 3 → K) (row output scratch : K)
    (hfields : ∀ i, fields i ≠ row ∧ fields i ≠ scratch)
    (hrowOutput : row ≠ output) (hrowScratch : row ≠ scratch)
    (houtputScratch : output ≠ scratch) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (hprogram : ∀ label, program (labels label) = routine fields row output scratch labels exit label)
    (base : K → List Bool) (hrow : base row = []) (hscratch : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[
        4 * fieldSize fields base + 2 * (base output).length + 9]
      (some ⟨some (labels .relationRead), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        Function.update base output (base output ++ fieldBits fields base)⟩ := by
  have hprefix := prefixTrace fields row output scratch hfields hrowScratch
    labels exit program hprogram base hscratch ambient register
  have happend := MachineAppendAt.appendTrace row output scratch hrowOutput hrowScratch
    houtputScratch false (labels .appendOld) (labels .appendRow) (labels .appendBack)
    exit program (hprogram .appendOld) (hprogram .appendRow) (hprogram .appendBack)
    (prefixTapes fields row base)
    (by simp [prefixTapes, Ne.symm hrowScratch, hscratch]) ambient none
  have hrowbits : prefixTapes fields row base row = fieldBits fields base := by
    simp [prefixTapes, hrow]
  have hout : prefixTapes fields row base output = base output := by
    simp [prefixTapes, Ne.symm hrowOutput]
  rw [hrowbits, hout, fieldBits_length] at happend
  have hfinal : MachineAppendAt.appendTapes row output (prefixTapes fields row base) =
      Function.update base output (base output ++ fieldBits fields base) := by
    funext k
    by_cases ho : k = output
    · subst k
      simp [MachineAppendAt.appendTapes, hrowbits, hout]
    · by_cases hr : k = row
      · subst k
        simp [MachineAppendAt.appendTapes, Reduction.MachineTransfer.tapesAt,
          prefixTapes, hrowOutput, hrow]
      · simp [MachineAppendAt.appendTapes, Reduction.MachineTransfer.tapesAt,
          prefixTapes, ho, hr]
  rw [hfinal] at happend
  rw [show 4 * fieldSize fields base + 2 * (base output).length + 9 =
      (2 * (fieldSize fields base + (base output).length) + 3) +
        2 * (fieldSize fields base + 3) by omega,
    Function.iterate_add_apply, hprefix]
  exact happend

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

theorem rowBits_length (v e : Nat) : (rowBits v e).length = v + e + 8194 := by
  simp [rowBits, trueBits_length, encodeWord_length]
  omega

variable {σ : Type}

/-- The fixed literal relation is actually emitted by a finite push chain. -/
theorem initializeStep (d v e : Nat) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program d) ⟨some (start d), (ambient, register), initialTapes v e output⟩ =
      some ⟨entry d, (ambient, none), fieldTapes v e output⟩ := by
  change some (TM2.stepAux (program d (start d)) (ambient, register)
    (initialTapes v e output)) = _
  simp only [start, program, stepAux_pushWord, List.reverse_reverse, TM2.stepAux,
    initialTapes, Function.update_self, List.append_nil, Function.update_idem]
  have ht : Function.update (fieldTapes v e output) 2 trueBits = fieldTapes v e output := by
    funext i
    fin_cases i <;> simp [fieldTapes]
  rw [ht, stepAux_continueAt]

theorem rowTrace {d : Nat} (p : Fin d) (v e : Nat) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[
        4 * (v + e + 8194) + 2 * output.length + 9]
      (some ⟨some (rowLabel p .relationRead), (ambient, register), fieldTapes v e output⟩) =
      some ⟨some (bumpLabel p), (ambient, none), fieldTapes v e (output ++ rowBits v e)⟩ := by
  have hfields (i : Fin 3) : fields i ≠ (3 : Fin 6) ∧ fields i ≠ (5 : Fin 6) := by
    fin_cases i <;> decide
  have h := MachineTableRows.appendTrace fields (3 : Fin 6) 4 5 hfields
    (by decide) (by decide) (by decide) (rowLabel p) (some (bumpLabel p))
    (program d) (fun _ => rfl) (fieldTapes v e output) rfl rfl ambient register
  have hbits : MachineTableRows.fieldBits fields (fieldTapes v e output) = rowBits v e := by
    rfl
  have hsize : MachineTableRows.fieldSize fields (fieldTapes v e output) = v + e + 8194 := by
    rw [← MachineTableRows.fieldBits_length, hbits, rowBits_length]
  have ht : Function.update (fieldTapes v e output) 4 (output ++ rowBits v e) =
      fieldTapes v e (output ++ rowBits v e) := by
    funext i
    fin_cases i <;> simp [fieldTapes]
  simpa only [hsize, hbits, show fieldTapes v e output 4 = output from rfl, ht] using h

/-- The reverse index advances by pushing a real unary bit. The delimiter,
all input fields, output, and work tapes have their exact stated contents. -/
theorem bumpStep {d : Nat} (p : Fin d) (v e : Nat) (output : List Bool) (ambient : σ) :
    TM2.step (program d) ⟨some (bumpLabel p), (ambient, none), fieldTapes v e output⟩ =
      some ⟨afterPort p, (ambient, none), fieldTapes v (e + 1) output⟩ := by
  change some (TM2.stepAux (program d (bumpLabel p)) (ambient, none)
    (fieldTapes v e output)) = _
  simp only [bumpLabel, program, TM2.stepAux]
  rw [stepAux_continueAt]
  congr 2
  funext i
  fin_cases i <;> simp [fieldTapes, encodeWord, List.replicate_succ]

/-- The concrete row body and its actual index increment are consecutive
phases of one fixed program; no whole-body trace is supplied as a premise. -/
theorem rowAndBumpTrace {d : Nat} (p : Fin d) (v e : Nat) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[
        4 * (v + e + 8194) + 2 * output.length + 10]
      (some ⟨some (rowLabel p .relationRead), (ambient, register), fieldTapes v e output⟩) =
      some ⟨afterPort p, (ambient, none), fieldTapes v (e + 1) (output ++ rowBits v e)⟩ := by
  rw [show 4 * (v + e + 8194) + 2 * output.length + 10 =
      (4 * (v + e + 8194) + 2 * output.length + 9) + 1 by omega,
    Function.iterate_succ_apply', rowTrace, MachineComposition.advance_some]
  exact bumpStep p v e (output ++ rowBits v e) ambient

/-- Actual execution from any port boundary to the final halt. The finite
control index fixes the remaining number of rows; all unbounded values are
physically stored in `fieldTapes`. -/
theorem suffixTrace {d : Nat} (count : Nat) (p : Fin d) (hp : p.val + count = d)
    (v e : Nat) (output : List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[steps v e output count]
      (some ⟨some (rowLabel p .relationRead), (ambient, register), fieldTapes v e output⟩) =
      some ⟨none, (ambient, none), fieldTapes v (e + count) (output ++ rowsBits v e count)⟩ := by
  induction count generalizing p v e output register with
  | zero =>
    have hlt := p.isLt
    omega
  | succ count ih =>
    rw [steps, Nat.add_comm (4 * (v + e + 8194) + 2 * output.length + 10),
      Function.iterate_add_apply, rowAndBumpTrace]
    by_cases hc : count = 0
    · subst count
      have hlast : ¬ p.val + 1 < d := by omega
      simp [afterPort, hlast, steps, rowsBits]
    · have hnext : p.val + 1 < d := by omega
      rw [afterPort, dite_eq_left hnext]
      have hh := ih ⟨p.val + 1, hnext⟩ (by change (p.val + 1) + count = d; omega)
        v (e + 1) (output ++ rowBits v e) none
      have he : (e + 1) + count = e + (count + 1) := by omega
      simpa only [rowsBits, List.append_assoc, he] using hh

/-- One fixed-relation initialization transition followed by all actual rows.
At zero ports initialization itself halts; no row is spuriously produced. -/
theorem allTrace (d v e : Nat) (output : List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[steps v e output d + 1]
      (some ⟨some (start d), (ambient, register), initialTapes v e output⟩) =
      some ⟨none, (ambient, none), fieldTapes v (e + d) (output ++ rowsBits v e d)⟩ := by
  rw [Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step (program d)))^[steps v e output d]
    (TM2.step (program d) ⟨some (start d), (ambient, register), initialTapes v e output⟩) = _
  rw [initializeStep]
  by_cases hd : 0 < d
  · rw [entry, dite_eq_left hd]
    exact suffixTrace d ⟨0, hd⟩ (by simp) v e output ambient none
  · have hz : d = 0 := by omega
    subst d
    simp [entry, steps, rowsBits]

end UniqueGamesTheorem.Foundations.Complexity.MachineDummyRows

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingPaddingWords
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.initialExtra_scratch _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.initialExtra_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringRowData.basePredicate_walkBits _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringRowData.leftMatches_walkBits _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringRowData.rightMatches_walkBits _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringRowData.rowBits_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTableLayout.vertexRows_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTables.table_vertices _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.lazy_accepts_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.lazy_accepts_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.overlay_accepts_expander _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.overlay_accepts_old
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

/-- The bits of one actual table row, in the existing graph codec. -/
def rowBits (table : Table n d) (v : Fin n) (p : Fin d) : List Bool :=
  encodeWord v.val ++ encodeWord (table.reverseIndex[rowIndex n d (v, p)]).val ++
    encodeWords (GraphTables.relationWords table.relations[rowIndex n d (v, p)])

def vertexBits (table : Table n d) (v : Fin n) : List Bool :=
  (List.ofFn (fun p : Fin d => rowBits table v p)).flatten

/-- Every bit in an original row survives padding unchanged. -/
theorem rowBits_pad_old (table : Table n d) (h : n ≤ m) (v : Fin n) (p : Fin d) :
    rowBits (PreprocessingPaddingTables.pad table h) (v.castLE h) p = rowBits table v p := by
  unfold rowBits
  rw [PreprocessingPaddingTables.reverseIndex_pad_old,
    PreprocessingPaddingTables.relations_pad_old]
  have he : (rowIndex m d ((rotation table (v, p)).1.castLE h,
      (rotation table (v, p)).2)).val = (table.reverseIndex[rowIndex n d (v, p)]).val := by
    rw [← rowIndex_rotation]
    rfl
  rw [he]
  rfl

@[simp] theorem vertexBits_pad_old (table : Table n d) (h : n ≤ m) (v : Fin n) :
    vertexBits (PreprocessingPaddingTables.pad table h) (v.castLE h) = vertexBits table v := by
  simp only [vertexBits, rowBits_pad_old]

end UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingWords

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingRegularWords
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_append _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_nil _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_append _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_nil _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_done _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_head _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_relation _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_reverseIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_words _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRows_acceptsAt _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRows_get _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRows_reverseAt _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_headIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_headValue _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_relation _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_reverseIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_row _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_head _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tableBits _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tableWords _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.boolView_outer _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.caller_initialState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.caller_normalizeState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.clearRegister_initialState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.program_outer _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.program_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.tableExecution_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamilyBounds.familyBudget_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamilyBounds.resizeSum_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.program_firstEmit _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.program_outputEmit _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.program_secondEmit _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.accumulatedVertices_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.caller_boundaryState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.caller_prepareState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.caller_resetState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.caller_rowAfterState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.clearRegister_boundaryState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.prepareState_boundaryState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.program_outer _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.program_row _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.rowAfterState_position _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.rowExecution_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.initialExtra_scratch _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.initialExtra_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRow.rowBlock_at _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Relations.oldPredicate_relationAt _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Relations.relationAt_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.build_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.build_vertices _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.rowList_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.rows_at _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.generatedWords_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.priorVertices_full _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.priorVertices_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.vertexWords_drop_full _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.vertexWords_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables.walkRows_edge _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables.walkRows_head_value _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables.walkRows_tail_value _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringRowData.basePredicate_transposeBits _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringRowData.basePredicate_walkBits _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringRowData.leftMatches_walkBits _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringRowData.rightMatches_walkBits _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringRowData.rowBits_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTableLayout.vertexRows_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTables.table_vertices _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.accepts_materialize _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.lazy_accepts_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.lazy_accepts_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.overlay_accepts_expander _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.overlay_accepts_old _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Complete serialization of the actual regularized table

Each global vertex emits its internal ports in increasing order, then its
inherited port. Original darts are the first global vertices. Dummy vertices
follow in increasing owner and local-dummy order. These are identities for the
actual stored rows and existing codec, with arbitrary actual cloud tables.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords

open DegreeReplacement PreprocessingCloudIndex PreprocessingRegularTables Complexity
open scoped BigOperators

variable (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
variable (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)

/-- Read one row of the actual output, in the chosen global coordinates. -/
def actualRow (x : Vertex t padding) (p : Fin q ⊕ Unit) :
    GraphTables.DartRow (vertexCount t padding) (vertexCount t padding * (q + 1)) :=
  (PortTables.flatRows (ofCloudTables t padding tables))[
    PortTables.rowIndex _ _ (vertexOrder t padding x, portOrder q p)]

/-- A vertex emits every internal port, followed by its inherited port. -/
def vertexRows (x : Vertex t padding) :
    List (GraphTables.DartRow (vertexCount t padding) (vertexCount t padding * (q + 1))) :=
  List.ofFn (fun p : Fin q => actualRow t padding tables x (.inl p)) ++
    [actualRow t padding tables x (.inr ())]

def vertexBits (x : Vertex t padding) : List Bool :=
  encodeWords ((vertexRows t padding tables x).flatMap GraphTables.rowWords)

def originalVertexBits (e : Fin t.darts) : List Bool := vertexBits t padding tables (.inl e)
def dummyVertexBits (v : Fin t.vertices) (j : Fin (padding v)) : List Bool :=
  vertexBits t padding tables (.inr ⟨v, j⟩)

theorem actualRow_eq (x : Vertex t padding) (p : Fin q ⊕ Unit) :
    actualRow t padding tables x p =
      ⟨vertexOrder t padding x,
        (ofCloudTables t padding tables).reverseIndex[
          PortTables.rowIndex _ _ (vertexOrder t padding x, portOrder q p)],
        (ofCloudTables t padding tables).relations[
          PortTables.rowIndex _ _ (vertexOrder t padding x, portOrder q p)]⟩ := by
  simp only [actualRow, PortTables.flatRows, Vector.getElem_ofFn,
    Fin.getElem_fin, Fin.eta, Equiv.symm_apply_apply]

@[simp] theorem actualRow_tail (x : Vertex t padding) (p : Fin q ⊕ Unit) :
    (actualRow t padding tables x p).tail.val = (vertexOrder t padding x).val := by
  rw [actualRow_eq]

@[simp] theorem inherited_original_reverse (e : Fin t.darts) :
    (actualRow t padding tables (.inl e) (.inr ())).reverseIndex.val =
      (q + 1) * t.rows[e].reverseIndex.val + q := by
  rw [actualRow_eq]
  change ((ofCloudTables t padding tables).reverseIndex[PortTables.rowIndex _ _
    (vertexOrder t padding (.inl e), portOrder q (.inr ()))]).val = _
  rw [← PortTables.rowIndex_rotation, rotation_ofCloudTables]
  change (PortTables.rowIndex _ _
    (vertexOrder t padding (.inl (GraphTables.reverseAt t.rows e)), portOrder q (.inr ()))).val = _
  rw [PortTables.rowIndex_val, vertexOrder_original, portOrder_inherited]
  exact Nat.add_comm _ _

@[simp] theorem inherited_dummy_reverse (v : Fin t.vertices) (j : Fin (padding v)) :
    (actualRow t padding tables (.inr ⟨v, j⟩) (.inr ())).reverseIndex.val =
      (q + 1) * (t.darts + PreprocessingPaddingOffsets.offset padding v.val + j.val) + q := by
  rw [actualRow_eq]
  change ((ofCloudTables t padding tables).reverseIndex[PortTables.rowIndex _ _
    (vertexOrder t padding (.inr ⟨v, j⟩), portOrder q (.inr ()))]).val = _
  rw [← PortTables.rowIndex_rotation, rotation_ofCloudTables]
  change (PortTables.rowIndex _ _
    (vertexOrder t padding (.inr ⟨v, j⟩), portOrder q (.inr ()))).val = _
  rw [PortTables.rowIndex_val, PreprocessingPaddingOffsets.vertexOrder_dummy_val,
    portOrder_inherited]
  exact Nat.add_comm _ _

theorem relation_ext {r s : GraphTables.RelationTable}
    (h : ∀ a b, GraphTables.relationAt r a b = GraphTables.relationAt s a b) : r = s := by
  apply Vector.ext
  intro i hi
  simpa only [GraphTables.relationAt, Prod.eta, Equiv.apply_symm_apply,
    Fin.getElem_fin] using h (GraphTables.relationIndex.symm ⟨i, hi⟩).1
      (GraphTables.relationIndex.symm ⟨i, hi⟩).2

@[simp] theorem inherited_original_relation (e : Fin t.darts) :
    (actualRow t padding tables (.inl e) (.inr ())).relation = t.rows[e].relation := by
  rw [actualRow_eq]
  apply relation_ext
  intro a b
  exact accepts_original t padding tables e a b

@[simp] theorem inherited_dummy_relation (v : Fin t.vertices) (j : Fin (padding v)) :
    (actualRow t padding tables (.inr ⟨v, j⟩) (.inr ())).relation =
      MachineDummyRows.trueRelation := by
  rw [actualRow_eq]
  apply relation_ext
  intro a b
  have h := accepts_dummy t padding tables ⟨v, j⟩ a b
  simpa only [PortTables.accepts, MachineDummyRows.trueRelation,
    GraphTables.relationAt, Fin.getElem_fin, Vector.getElem_replicate] using h

end UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOriginalRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Machine execution for an inherited regularization row

The machine reads the original reverse index from the physically stored input
table. The unread working copy then starts at the 4096 original predicate
fields; a fixed finite Boolean block copy retains exactly those fields. Unary
arithmetic computes the new reverse index, and the checked row emitter appends
the three physical fields. No input table or unbounded arithmetic function is
stored in the machine's finite state or instructions.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalRow

open Turing MachineComposition
open PCP PCP.GraphTables PCP.PreprocessingRegularTables

/-! ## The actual stored row and its input word boundaries -/

def suffixWords (t : Table) (e : Fin t.darts) : List Nat :=
  ((rowList t).drop (e.val + 1)).flatMap rowWords

/-! ## One fixed finite program -/

abbrev Buffer := MachineFixedBlockMap.Buffer 4096
abbrev State (σ : Type) := (σ × Buffer) × Option Bool

def copyStateEquiv (σ : Type) : ((σ × Option Bool) × Buffer) ≃ State σ where
  toFun s := ((s.1.1, s.2), s.1.2)
  invFun s := ((s.1.1, s.2), s.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

inductive Label
  | lookup (label : MachineAffineLookup.Label)
  | copyRelation | reverseSeed | reverseScan | reverseRestore
  | emit (label : MachineTableRows.Label)
  deriving DecidableEq, Fintype

def relationCopyAt {K σ Λ : Type} (src dst : K) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (State σ) :=
  MachineStateEquiv.statement (copyStateEquiv σ)
    (PoweringMachineRow.encodedBlockAt src dst (id : Buffer → Buffer) exit)

def instruction {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt Alphabet Λ (State σ)
  | .lookup l => MachineAffineLookup.instruction 0 lookupTape 4098 3
      (fun l => labels (.lookup l)) (some (labels .copyRelation)) l
  | .copyRelation => relationCopyAt 3 7 (some (labels .reverseSeed))
  | .reverseSeed => MachineUnaryAffineAt.seed 6 q (labels .reverseScan)
  | .reverseScan => MachineUnaryAffineAt.scan 4 5 6 (q + 1)
      (labels .reverseScan) (labels .reverseRestore)
  | .reverseRestore => Reduction.MachineTransfer.loopAt 5 4 id false
      (labels .reverseRestore) (some (labels (.emit .relationRead)))
  | .emit l => MachineTableRows.routine fields 8 9 5 (fun l => labels (.emit l)) exit l

/-! ## Physical intermediate tape states -/

def looked (t : Table) (e : Fin t.darts) (base : Tape → List Bool) : Tape → List Bool :=
  MachineAffineLookup.finalTapes lookupTape base (GraphTables.tableWords t) (4098 * e.val + 3)
    t.rows[e].reverseIndex.val

def copied (t : Table) (e : Fin t.darts) (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (Function.update (looked t e base) 3
    (encodeWords (suffixWords t e) ++ base 3)) 7
    (encodeWords (relationWords t.rows[e].relation) ++ base 7)

def affined (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    Tape → List Bool :=
  Function.update (copied t e base) 6
    (encodeWord ((q + 1) * t.rows[e].reverseIndex.val + q) ++ base 6)

def emittedWords (q : Nat) (t : Table) (e : Fin t.darts) : List Nat :=
  e.val :: ((q + 1) * t.rows[e].reverseIndex.val + q) :: relationWords t.rows[e].relation

def rowSteps (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) : Nat :=
  4 * (encodeWords (emittedWords q t e)).length + 2 * (base 9).length + 9

def steps (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) : Nat :=
  MachineAffineLookup.steps (GraphTables.tableWords t) e.val 4098 3 + 1 +
    (2 * (t.rows[e].reverseIndex.val + 1) + 1) + rowSteps q t e base

def finalTapes (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    Tape → List Bool :=
  Function.update (affined q t e base) 9 (base 9 ++ encodeWords (emittedWords q t e))

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalRow

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

abbrev Buffer := MachineRegularOriginalRow.Buffer

end UniqueGamesTheorem.Foundations.Complexity.MachineLazyRows

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineExpanderRowDivision
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
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

/-- Pull the actual target program into division-state coordinates, derive its
trace from its concrete statements, then transport every actual transition back. -/
theorem transportedDivision {K Λ σ τ : Type} [DecidableEq K] [Fintype σ]
    (q : Nat) (positive : 0 < q) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder)
    (states : MachineFixedDivMod.State σ q ≃ τ)
    (scanLabel : Λ) (emitterLabel : Fin q → Λ) (exit : Option Λ)
    (finish : σ → Fin q → σ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ τ)
    (atScan : target scanLabel = MachineControl.statement id states
      (MachineFixedDivMod.scanLoop q positive source quotient scanLabel emitterLabel))
    (atEmitter : ∀ r, target (emitterLabel r) = MachineControl.statement id states
      (MachineFixedDivMod.emitterWithFinish q positive remainder exit finish r))
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (sourceInput : base source = encodeWord n ++ sourceSuffix)
    (quotientInput : base quotient = encodeWord 0 ++ quotientSuffix)
    (remainderInput : base remainder = encodeWord 0 ++ remainderSuffix)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step target))^[n + 2]
      (some (MachineControl.configuration id states
        ⟨some scanLabel, ((ambient, MachineFixedDivMod.residue q positive 0), register), base⟩)) =
      some (MachineControl.configuration id states
        ⟨exit, ((finish ambient (MachineFixedDivMod.residue q positive n),
          MachineFixedDivMod.residue q positive 0), none),
          MachineFixedDivMod.unaryTapes source quotient remainder base 0 (n / q) (n % q)
            sourceSuffix quotientSuffix remainderSuffix⟩) := by
  let sourceProgram := MachineControl.program (Equiv.refl Λ) states.symm target
  have sourceScan : sourceProgram scanLabel =
      MachineFixedDivMod.scanLoop q positive source quotient scanLabel emitterLabel := by
    change MachineControl.statement id states.symm (target scanLabel) = _
    rw [atScan]
    exact controlStatement_inverse states _
  have sourceEmit : ∀ r, sourceProgram (emitterLabel r) =
      MachineFixedDivMod.emitterWithFinish q positive remainder exit finish r := by
    intro r
    change MachineControl.statement id states.symm (target (emitterLabel r)) = _
    rw [atEmitter]
    exact controlStatement_inverse states _
  have htrace := MachineFixedDivMod.divModFromTapesWithFinish q positive source quotient
    remainder sourceQuotient sourceRemainder quotientRemainder scanLabel emitterLabel exit
    finish sourceProgram sourceScan sourceEmit base n sourceSuffix quotientSuffix remainderSuffix
    sourceInput quotientInput remainderInput ambient register
  have roundtrip : MachineControl.program (Equiv.refl Λ) states sourceProgram = target := by
    funext label
    change MachineControl.statement id states
      (MachineControl.statement id states.symm (target label)) = target label
    exact controlStatement_inverse states.symm _
  have simulation : ∀ a b, TM2.step sourceProgram a = some b →
      TM2.step target (MachineControl.configuration id states a) =
        some (MachineControl.configuration id states b) := by
    intro a b hab
    have h := MachineControl.step_simulation (Equiv.refl Λ) states sourceProgram a
    rw [roundtrip, hab] at h
    exact h
  exact MachineComposition.liftSuccessfulTrace (TM2.step sourceProgram) (TM2.step target)
    (MachineControl.configuration id states) simulation (n + 2) _ _ htrace

variable {K Λ ρ : Type} [DecidableEq K] [Fintype ρ]

/-- Exact first lookup-result division, including the receiveFirst control update. -/
theorem firstDivisionTrace {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atProgram : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (sourceInput : base (ports .lookupOutput) = encodeWord n ++ sourceSuffix)
    (quotientInput : base (ports .quotientFirst) = encodeWord 0 ++ quotientSuffix)
    (remainderInput : base (ports .remainderFirst) = encodeWord 0 ++ remainderSuffix)
    (ambient : ρ) (control : Control d) (register : Option Bool) :
    (MachineComposition.advance (TM2.step target))^[n + 2]
      (some ⟨some (labels .firstScan), divisionState positive ambient control register, base⟩) =
      some ⟨some (labels .clearQuery), divisionState positive ambient
        (receiveFirst control (MachineFixedDivMod.residue (degree d)
          (Nat.mul_pos positive positive) n)) none,
        divisionOutput d ports .quotientFirst .remainderFirst base n
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  have hsq : ports .lookupOutput ≠ ports .quotientFirst :=
    fun h => Tape.noConfusion (portsInjective h)
  have hsr : ports .lookupOutput ≠ ports .remainderFirst :=
    fun h => Tape.noConfusion (portsInjective h)
  have hqr : ports .quotientFirst ≠ ports .remainderFirst :=
    fun h => Tape.noConfusion (portsInjective h)
  have hs : target (labels .firstScan) = MachineControl.statement id (divisionStates ρ d)
      (MachineFixedDivMod.scanLoop (degree d) (Nat.mul_pos positive positive)
        (ports .lookupOutput) (ports .quotientFirst) (labels .firstScan)
        (fun r => labels (.firstResidue r))) := atProgram .firstScan
  have he : ∀ r, target (labels (.firstResidue r)) =
      MachineControl.statement id (divisionStates ρ d)
        (MachineFixedDivMod.emitterWithFinish (degree d) (Nat.mul_pos positive positive)
          (ports .remainderFirst) (some (labels .clearQuery)) firstFinish r) :=
    fun r => atProgram (.firstResidue r)
  have h := transportedDivision (degree d) (Nat.mul_pos positive positive)
    (ports .lookupOutput) (ports .quotientFirst) (ports .remainderFirst) hsq hsr hqr
    (divisionStates ρ d) (labels .firstScan) (fun r => labels (.firstResidue r))
    (some (labels .clearQuery)) firstFinish target hs he base n sourceSuffix quotientSuffix
    remainderSuffix sourceInput quotientInput remainderInput ((ambient, control), ()) register
  simpa only [MachineControl.configuration, divisionStates_apply, firstFinish, divisionState,
    divisionOutput, Option.map_some, id_eq] using h

/-- Exact second division, including receiveSecond and the actual output-emitter entry label. -/
theorem secondDivisionTrace {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atProgram : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (sourceInput : base (ports .lookupOutput) = encodeWord n ++ sourceSuffix)
    (quotientInput : base (ports .quotientSecond) = encodeWord 0 ++ quotientSuffix)
    (remainderInput : base (ports .remainderSecond) = encodeWord 0 ++ remainderSuffix)
    (ambient : ρ) (control : Control d) (register : Option Bool) :
    (MachineComposition.advance (TM2.step target))^[n + 2]
      (some ⟨some (labels .secondScan), divisionState positive ambient control register, base⟩) =
      some ⟨some (labels (.outputEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient
          (receiveSecond H control (MachineFixedDivMod.residue (degree d)
            (Nat.mul_pos positive positive) n)) none,
        divisionOutput d ports .quotientSecond .remainderSecond base n
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  have hsq : ports .lookupOutput ≠ ports .quotientSecond :=
    fun h => Tape.noConfusion (portsInjective h)
  have hsr : ports .lookupOutput ≠ ports .remainderSecond :=
    fun h => Tape.noConfusion (portsInjective h)
  have hqr : ports .quotientSecond ≠ ports .remainderSecond :=
    fun h => Tape.noConfusion (portsInjective h)
  have hs : target (labels .secondScan) = MachineControl.statement id (divisionStates ρ d)
      (MachineFixedDivMod.scanLoop (degree d) (Nat.mul_pos positive positive)
        (ports .lookupOutput) (ports .quotientSecond) (labels .secondScan)
        (fun r => labels (.secondResidue r))) := atProgram .secondScan
  have he : ∀ r, target (labels (.secondResidue r)) =
      MachineControl.statement id (divisionStates ρ d)
        (MachineFixedDivMod.emitterWithFinish (degree d) (Nat.mul_pos positive positive)
          (ports .remainderSecond)
          (some (labels (.outputEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))))
          (secondFinish H) r) := fun r => atProgram (.secondResidue r)
  have h := transportedDivision (degree d) (Nat.mul_pos positive positive)
    (ports .lookupOutput) (ports .quotientSecond) (ports .remainderSecond) hsq hsr hqr
    (divisionStates ρ d) (labels .secondScan) (fun r => labels (.secondResidue r))
    (some (labels (.outputEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))))
    (secondFinish H) target hs he base n sourceSuffix quotientSuffix remainderSuffix
    sourceInput quotientInput remainderInput ((ambient, control), ()) register
  simpa only [MachineControl.configuration, divisionStates_apply, secondFinish, divisionState,
    divisionOutput, Option.map_some, id_eq] using h

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

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} [Fintype ρ]

def rowTapes (vertex : Nat) (oldTable output : List Bool) : MachineExpanderRow.Tape → List Bool
  | .inputVertex => encodeWord vertex
  | .table => oldTable
  | .output => output
  | _ => []

def extraTapes (remaining : Nat) (countSuffix result : List Bool) : ExtraTape → List Bool
  | .vertexCount => encodeWord remaining ++ countSuffix
  | .result => result

def boundaryTapes (vertex remaining : Nat) (oldTable output countSuffix result : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  MachineEmbedding.tapes (rowTapes vertex oldTable output) (extraTapes remaining countSuffix result)

/-- Before initialization, only the old table and remaining-count word are
populated. The program itself creates the initial vertex delimiter. -/
def initialTapes (vertices : Nat) (oldTable countSuffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  MachineEmbedding.tapes
    (fun tape => match tape with | .table => oldTable | _ => [])
    (extraTapes vertices countSuffix [])

def finalTapes (vertices : Nat) (oldTable output countSuffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  boundaryTapes vertices 0 oldTable [] countSuffix output

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

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

theorem toBoolTapes_eq_transport (base : (tape : Tape) → List (Alphabet tape)) :
    toBoolTapes base = MachineAlphabetTransport.tapes alphabet_eq base := by
  funext tape
  rw [transport_tapes_apply]
  rcases tape with tape | tape
  · cases tape <;> rfl
  · rfl

theorem fromBoolTapes_eq_transport (base : Tape → List Bool) :
    fromBoolTapes base = MachineAlphabetTransport.tapes alphabet_eq.symm base := by
  funext tape
  rw [transport_tapes_apply]
  rcases tape with tape | tape
  · cases tape <;> rfl
  · rfl

theorem configuration_fromBool {ρ : Type} {d : Nat} (label : Option (Label d))
    (state : State ρ d) (base : Tape → List Bool) :
    MachineAlphabetTransport.configuration alphabet_eq.symm ⟨label, state, base⟩ =
      ⟨label, state, fromBoolTapes base⟩ := by
  rw [MachineAlphabetTransport.configuration_mk, fromBoolTapes_eq_transport]

theorem configuration_toBool {ρ : Type} {d : Nat} (label : Option (Label d))
    (state : State ρ d) (base : (tape : Tape) → List (Alphabet tape)) :
    MachineAlphabetTransport.configuration alphabet_eq ⟨label, state, base⟩ =
      ⟨label, state, toBoolTapes base⟩ := by
  rw [MachineAlphabetTransport.configuration_mk, toBoolTapes_eq_transport]

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineExpanderFamilyTransferLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.toBool_cycleTapes _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamilyBounds.familyBudget_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamilyBounds.resizeSum_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.RowData.firstValue_div_degree _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.RowData.firstValue_mod_degree _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.RowData.secondValue_div_degree _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.RowData.secondValue_mod_degree _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.cleanupTapes_dirty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.cleanupTapes_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.cleanupTapes_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.cleanupTapes_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_emitScratch _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_emitScratch _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_lookupRestore _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_lookupWork _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_emitScratch _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_lookupRestore _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_lookupWork _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.program_firstEmit _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.program_outputEmit _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.program_secondEmit _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.accumulatedVertices_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.caller_rowAfterState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.clearRegister_position _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.clearRegister_register _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.rowAfterState_position _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.ceilingStates_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.familyView_left _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt.transferLeft_tapes _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt.transferRight_tapes _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.atGuard _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.generatedWords_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.priorVertices_full _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.priorVertices_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.vertexWords_drop_full _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.vertexWords_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.overlay_accepts_expander _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.overlay_accepts_old _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_internal _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.actualRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.dirtyTape_five _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.dirtyTape_four _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.dirtyTape_one _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.dirtyTape_three _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.dirtyTape_two _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.dirtyTape_zero
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

theorem controlDrainTrace {K Λ σ τ : Type} [DecidableEq K]
    (states : (σ × Option Bool) ≃ τ) (source : K) (again : Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ τ)
    (code : target again = MachineControl.statement id states
      (MachineDrain.drain source again exit))
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step target))^[(base source).length + 1]
      (some ⟨some again, states (ambient, register), base⟩) =
      some ⟨exit, states (ambient, none), Function.update base source []⟩ := by
  let raw := MachineControl.program (Equiv.refl Λ) states.symm target
  have atRaw : raw again = MachineDrain.drain source again exit := by
    change MachineControl.statement id states.symm (target again) = _
    rw [code]
    exact controlStatementInverse states _
  have run := MachineDrain.drainTrace source again exit raw atRaw base (base source) ambient register
  simp only [Function.update_eq_self] at run
  simpa only [MachineControl.configuration, Option.map_some, id_eq, Option.map_id] using
    controlTrace states target ((base source).length + 1) _ _ run

section TransferVariables

variable {ρ : Type} {d : Nat}

variable [Fintype ρ]

/-- The Boolean view is the same actual program under alphabet equality. -/
theorem boolTraceActual (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (n : Nat)
    (start finish : TM2.Cfg BoolAlphabet (Label d) (State ρ d))
    (run : (advance (TM2.step (boolView positive H growth)))^[n] (some start) = some finish) :
    (advance (TM2.step (program positive H growth)))^[n]
      (some (MachineAlphabetTransport.configuration alphabet_eq.symm start)) =
      some (MachineAlphabetTransport.configuration alphabet_eq.symm finish) := by
  have h := MachineAlphabetTransport.successfulTrace alphabet_eq.symm
    (boolView positive H growth) n start finish run
  simpa only [boolView, MachineAlphabetTransport.program_symm_roundtrip] using h

theorem drainBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (source : Tape) (again next : OuterLabel)
    (code : boolOuterStatement (ρ := ρ) positive H again = drainStatement source again next)
    (base : Tape → List Bool) (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[(base source).length + 1]
      (some ⟨some (.inr again), state, base⟩) =
      some ⟨some (.inr next), clearRegister state, Function.update base source []⟩ := by
  have atLoop : boolView (ρ := ρ) positive H growth (.inr again) =
      MachineControl.statement id (registerStates ρ d)
        (MachineDrain.drain source (.inr again) (some (.inr next))) := by
    rw [boolView_outer, code]
    rfl
  have h := controlDrainTrace (registerStates ρ d) source (.inr again) (some (.inr next))
    (boolView positive H growth) atLoop base
    ((registerStates ρ d).symm state).1 ((registerStates ρ d).symm state).2
  simpa only [Prod.mk.eta, Equiv.apply_symm_apply, registerStates_reset] using h

theorem transferBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (source destination : Tape) (distinct : source ≠ destination)
    (again next : OuterLabel)
    (code : boolOuterStatement (ρ := ρ) positive H again =
      MachineControl.statement id (registerStates ρ d)
        (Reduction.MachineTransfer.loopAt (Γ := BoolAlphabet) source destination id false
          (.inr again) (some (.inr next))))
    (base : Tape → List Bool) (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[(base source).length + 1]
      (some ⟨some (.inr again), state, base⟩) =
      some ⟨some (.inr next), clearRegister state,
        Reduction.MachineTransfer.tapesAt source destination base []
          ((base source).reverse ++ base destination)⟩ := by
  have atLoop : boolView (ρ := ρ) positive H growth (.inr again) =
      MachineControl.statement id (registerStates ρ d)
        (Reduction.MachineTransfer.loopAt source destination id false
          (.inr again) (some (.inr next))) := by
    rw [boolView_outer, code]
  have h := controlTransferTrace (registerStates ρ d) source destination distinct
    (.inr again) (some (.inr next)) (boolView positive H growth) atLoop base
    ((registerStates ρ d).symm state).1 ((registerStates ρ d).symm state).2
  simpa only [Prod.mk.eta, Equiv.apply_symm_apply, registerStates_reset] using h

/-- Only these four tape words change during installation. -/
def installedTapes (base : Tape → List Bool) (newWord : List Bool) : Tape → List Bool :=
  Function.update
    (Function.update
      (Function.update (Function.update base tableTape newWord) resultTape [])
      (.inr .tableReverse) [])
    (.inr .currentSize) []

def cleanedCounterTapes (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (Function.update base inputVertexTape []) vertexCountTape []

theorem installTableBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (newWord : List Bool)
    (resultWord : base resultTape = newWord) (reverseEmpty : base (.inr .tableReverse) = [])
    (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[
        (base tableTape).length + 2 * newWord.length + (base (.inr .currentSize)).length + 4]
      (some ⟨some (.inr .clearOldTable), state, base⟩) =
      some ⟨some (.inr (.affine .multiplySize .seed)), clearRegister state,
        installedTapes base newWord⟩ := by
  let b0 := Function.update base tableTape []
  let b1 := Function.update (Function.update b0 resultTape []) (.inr .tableReverse) newWord.reverse
  let b2 := Function.update (Function.update b1 (.inr .tableReverse) []) tableTape newWord
  let b3 := Function.update b2 (.inr .currentSize) []
  have h0 := drainBoolTrace positive H growth tableTape .clearOldTable .reverseResult rfl base state
  have b0Result : b0 resultTape = newWord := by
    simpa [b0, tableTape, resultTape] using resultWord
  have b0Reverse : b0 (.inr .tableReverse) = [] := by
    simpa [b0, tableTape] using reverseEmpty
  have h1 : (advance (TM2.step (boolView positive H growth)))^[newWord.length + 1]
      (some ⟨some (.inr .reverseResult), clearRegister state, b0⟩) =
      some ⟨some (.inr .reverseTable), clearRegister state, b1⟩ := by
    simpa only [b0Result, b0Reverse, List.append_nil, Reduction.MachineTransfer.tapesAt,
      clearRegister_idempotent] using
      transferBoolTrace positive H growth resultTape (.inr .tableReverse) (by decide)
        .reverseResult .reverseTable rfl b0 (clearRegister state)
  have b1Reverse : b1 (.inr .tableReverse) = newWord.reverse := by simp [b1]
  have b1Table : b1 tableTape = [] := by simp [b1, b0, tableTape, resultTape]
  have h2 : (advance (TM2.step (boolView positive H growth)))^[newWord.length + 1]
      (some ⟨some (.inr .reverseTable), clearRegister state, b1⟩) =
      some ⟨some (.inr .clearCurrentSize), clearRegister state, b2⟩ := by
    simpa only [b1Reverse, b1Table, List.reverse_reverse, List.length_reverse,
      List.append_nil, Reduction.MachineTransfer.tapesAt, clearRegister_idempotent] using
      transferBoolTrace positive H growth (.inr .tableReverse) tableTape (by decide)
        .reverseTable .clearCurrentSize rfl b1 (clearRegister state)
  have b2Current : b2 (.inr .currentSize) = base (.inr .currentSize) := by
    simp [b2, b1, b0, tableTape, resultTape]
  have h3 : (advance (TM2.step (boolView positive H growth)))^[
      (base (.inr .currentSize)).length + 1]
      (some ⟨some (.inr .clearCurrentSize), clearRegister state, b2⟩) =
      some ⟨some (.inr (.affine .multiplySize .seed)), clearRegister state, b3⟩ := by
    simpa only [b2Current, clearRegister_idempotent] using
      drainBoolTrace positive H growth (.inr .currentSize) .clearCurrentSize
        (.affine .multiplySize .seed) rfl b2 (clearRegister state)
  have final : b3 = installedTapes base newWord := by
    funext tape
    rcases tape with table | extra
    · rcases table with row | tableExtra
      · cases row <;> simp [b3, b2, b1, b0, installedTapes, tableTape, resultTape]
      · cases tableExtra <;> simp [b3, b2, b1, b0, installedTapes, tableTape, resultTape]
    · cases extra <;> simp [b3, b2, b1, b0, installedTapes, tableTape, resultTape]
  rw [show (base tableTape).length + 2 * newWord.length +
        (base (.inr .currentSize)).length + 4 =
      ((base (.inr .currentSize)).length + 1) +
        ((newWord.length + 1) + ((newWord.length + 1) + ((base tableTape).length + 1))) by omega,
    Function.iterate_add_apply _ ((base (.inr .currentSize)).length + 1),
    Function.iterate_add_apply _ (newWord.length + 1) ((newWord.length + 1) + ((base tableTape).length + 1)),
    Function.iterate_add_apply _ (newWord.length + 1) ((base tableTape).length + 1),
    h0, h1, h2, h3, final]

theorem cleanupCountersBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[
        (base inputVertexTape).length + (base vertexCountTape).length + 2]
      (some ⟨some (.inr .drainInputVertex), state, base⟩) =
      some ⟨some (.inr .levelGuard), clearRegister state, cleanedCounterTapes base⟩ := by
  have h0 := drainBoolTrace positive H growth inputVertexTape .drainInputVertex .drainVertexCount
    rfl base state
  have count : (Function.update base inputVertexTape []) vertexCountTape = base vertexCountTape := by
    simp [inputVertexTape, vertexCountTape]
  have h1 := drainBoolTrace positive H growth vertexCountTape .drainVertexCount .levelGuard
    rfl (Function.update base inputVertexTape []) (clearRegister state)
  simp only [count, clearRegister_idempotent] at h1
  rw [show (base inputVertexTape).length + (base vertexCountTape).length + 2 =
      ((base vertexCountTape).length + 1) + ((base inputVertexTape).length + 1) by omega,
    Function.iterate_add_apply, h0]
  exact h1

/-- Actual dependent-alphabet trace for draining the old table, installing the
new forward table by two physical reversals, and clearing the old size word. -/
theorem installTableTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (newWord : List Bool) (resultWord : toBoolTapes base resultTape = newWord)
    (reverseEmpty : toBoolTapes base (.inr .tableReverse) = []) (state : State ρ d) :
    (advance (TM2.step (program positive H growth)))^[
        (toBoolTapes base tableTape).length + 2 * newWord.length +
          (toBoolTapes base (.inr .currentSize)).length + 4]
      (some ⟨some (.inr .clearOldTable), state, base⟩) =
      some ⟨some (.inr (.affine .multiplySize .seed)), clearRegister state,
        fromBoolTapes (installedTapes (toBoolTapes base) newWord)⟩ := by
  have h := installTableBoolTrace positive H growth (toBoolTapes base) newWord resultWord reverseEmpty state
  simpa only [configuration_fromBool, fromBool_toBool] using boolTraceActual positive H growth _ _ _ h

/-- After the checked affine phase, both table-loop counters are physically
drained and the actual family level guard is reached. -/
theorem cleanupCountersTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (state : State ρ d) :
    (advance (TM2.step (program positive H growth)))^[
        (toBoolTapes base inputVertexTape).length + (toBoolTapes base vertexCountTape).length + 2]
      (some ⟨some (.inr .drainInputVertex), state, base⟩) =
      some ⟨some (.inr .levelGuard), clearRegister state,
        fromBoolTapes (cleanedCounterTapes (toBoolTapes base))⟩ := by
  have h := cleanupCountersBoolTrace positive H growth (toBoolTapes base) state
  simpa only [configuration_fromBool, fromBool_toBool] using boolTraceActual positive H growth _ _ _ h

def installTableInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (newWord : List Bool) (resultWord : toBoolTapes base resultTape = newWord)
    (reverseEmpty : toBoolTapes base (.inr .tableReverse) = []) (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .clearOldTable), state, base⟩
      (some ⟨some (.inr (.affine .multiplySize .seed)), clearRegister state,
        fromBoolTapes (installedTapes (toBoolTapes base) newWord)⟩)
      ((toBoolTapes base tableTape).length + 2 * newWord.length +
        (toBoolTapes base (.inr .currentSize)).length + 4) where
  steps := (toBoolTapes base tableTape).length + 2 * newWord.length +
    (toBoolTapes base (.inr .currentSize)).length + 4
  evals_in_steps := installTableTrace positive H growth base newWord resultWord reverseEmpty state
  steps_le_m := Nat.le_refl _

def cleanupCountersInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .drainInputVertex), state, base⟩
      (some ⟨some (.inr .levelGuard), clearRegister state,
        fromBoolTapes (cleanedCounterTapes (toBoolTapes base))⟩)
      ((toBoolTapes base inputVertexTape).length + (toBoolTapes base vertexCountTape).length + 2) where
  steps := (toBoolTapes base inputVertexTape).length + (toBoolTapes base vertexCountTape).length + 2
  evals_in_steps := cleanupCountersTrace positive H growth base state
  steps_le_m := Nat.le_refl _

end TransferVariables

theorem affine_source_ne_scratch (phase : AffinePhase) :
    affineSource phase ≠ .inr .unaryScratch := by cases phase <;> decide

theorem affine_source_ne_destination (phase : AffinePhase) :
    affineSource phase ≠ affineDestination phase := by cases phase <;> decide

theorem affine_scratch_ne_destination (phase : AffinePhase) :
    (.inr .unaryScratch : Tape) ≠ affineDestination phase := by cases phase <;> decide

/-- Exact final dependent tape family, with all other tape contents retained. -/
def affineResultTapes (d : Nat) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) :
    (tape : Tape) → List (Alphabet tape) :=
  Function.update base (affineDestination phase)
    (boolWord (affineDestination phase)
      (encodeWord (affineCoefficient d phase * n) ++ toBoolTapes base (affineDestination phase)))

variable {ρ : Type} [Fintype ρ] {d : Nat}

/-- The concrete Boolean view is pulled into unary-affine state coordinates,
executed from its actual statements, and transported back without extra steps. -/
theorem affinePhaseBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (phase : AffinePhase) (base : Tape → List Bool)
    (n : Nat) (suffix : List Bool)
    (sourceWord : base (affineSource phase) = encodeWord n ++ suffix)
    (scratchEmpty : base (.inr .unaryScratch) = []) (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[2 * (n + 1) + 1]
      (some ⟨some (.inr (.affine phase .seed)), state, base⟩) =
      some ⟨some (affineExit d phase), clearRegister state,
        Function.update base (affineDestination phase)
          (encodeWord (affineCoefficient d phase * n) ++ base (affineDestination phase))⟩ := by
  let states := registerStates ρ d
  let target := boolView (ρ := ρ) positive H growth
  let sourceProgram := MachineControl.program (Equiv.refl (Label d)) states.symm target
  have atSeed : sourceProgram (.inr (.affine phase .seed)) =
      MachineUnaryAffineAt.seed (affineDestination phase) 0 (.inr (.affine phase .scan)) := by
    change MachineControl.statement id states.symm
      (boolView positive H growth (.inr (.affine phase .seed))) = _
    rw [boolView_outer]
    exact controlStatementInverse states _
  have atScan : sourceProgram (.inr (.affine phase .scan)) =
      MachineUnaryAffineAt.scan (affineSource phase) (.inr .unaryScratch)
        (affineDestination phase) (affineCoefficient d phase)
        (.inr (.affine phase .scan)) (.inr (.affine phase .restore)) := by
    change MachineControl.statement id states.symm
      (boolView positive H growth (.inr (.affine phase .scan))) = _
    rw [boolView_outer]
    exact controlStatementInverse states _
  have atRestore : sourceProgram (.inr (.affine phase .restore)) =
      Reduction.MachineTransfer.loopAt (.inr .unaryScratch) (affineSource phase) id false
        (.inr (.affine phase .restore)) (some (affineExit d phase)) := by
    change MachineControl.statement id states.symm
      (boolView positive H growth (.inr (.affine phase .restore))) = _
    rw [boolView_outer]
    exact controlStatementInverse states _
  have raw := MachineUnaryAffineAt.seededAffineTrace
    (affineSource phase) (.inr .unaryScratch) (affineDestination phase)
    (affine_source_ne_scratch phase) (affine_source_ne_destination phase)
    (affine_scratch_ne_destination phase) (affineCoefficient d phase) 0
    (.inr (.affine phase .seed)) (.inr (.affine phase .scan)) (.inr (.affine phase .restore))
    (some (affineExit d phase)) sourceProgram atSeed atScan atRestore base n suffix
    sourceWord scratchEmpty (states.symm state).1 (states.symm state).2
  have run := controlTrace states target (2 * (n + 1) + 1) _ _ raw
  simpa only [states, target, MachineControl.configuration, Option.map_some, id_eq, Prod.mk.eta,
    Equiv.apply_symm_apply, Nat.add_zero, registerStates_reset] using run

/-- Actual family-program execution. Alphabet conversion is static equality
transport; the transition count is exactly the checked unary-affine count. -/
theorem affinePhaseTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) (suffix : List Bool)
    (sourceWord : toBoolTapes base (affineSource phase) = encodeWord n ++ suffix)
    (scratchEmpty : base (.inr .unaryScratch) = []) (state : State ρ d) :
    (advance (TM2.step (program positive H growth)))^[2 * (n + 1) + 1]
      (some ⟨some (.inr (.affine phase .seed)), state, base⟩) =
      some ⟨some (affineExit d phase), clearRegister state,
        affineResultTapes d phase base n⟩ := by
  have raw := affinePhaseBoolTrace positive H growth phase (toBoolTapes base) n suffix
    sourceWord scratchEmpty state
  have transported := boolTraceActual positive H growth (2 * (n + 1) + 1) _ _ raw
  simpa only [configuration_fromBool, fromBoolTapes_update, fromBool_toBool,
    affineResultTapes] using transported

def affinePhaseInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) (suffix : List Bool)
    (sourceWord : toBoolTapes base (affineSource phase) = encodeWord n ++ suffix)
    (scratchEmpty : base (.inr .unaryScratch) = []) (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr (.affine phase .seed)), state, base⟩
      (some ⟨some (affineExit d phase), clearRegister state,
        affineResultTapes d phase base n⟩) (2 * (n + 1) + 1) where
  steps := 2 * (n + 1) + 1
  evals_in_steps := affinePhaseTrace positive H growth phase base n suffix sourceWord scratchEmpty state
  steps_le_m := Nat.le_refl _

def copyCountInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (n : Nat) (sourceWord : base (.inr .currentSize) = encodeWord n)
    (scratchEmpty : base (.inr .unaryScratch) = [])
    (destinationEmpty : base vertexCountTape = []) (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr (.affine .copyCount .seed)), state, base⟩
      (some ⟨some (.inl (.inr .initialize_)), clearRegister state,
        Function.update base vertexCountTape (encodeWord n)⟩) (2 * (n + 1) + 1) := by
  have run := affinePhaseInTime positive H growth .copyCount base n []
    (by simpa only [affineSource, toBoolTapes, toBoolWord, List.append_nil] using sourceWord)
    scratchEmpty state
  change base (.inl (.inr .vertexCount)) = [] at destinationEmpty
  simpa only [affineExit, affineResultTapes, affineDestination, affineCoefficient,
    Nat.one_mul, vertexCountTape, boolWord, toBoolTapes, toBoolWord,
    destinationEmpty, List.append_nil] using run

def multiplySizeInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (n : Nat) (sourceWord : base inputVertexTape = encodeWord n)
    (scratchEmpty : base (.inr .unaryScratch) = [])
    (destinationEmpty : base (.inr .currentSize) = []) (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr (.affine .multiplySize .seed)), state, base⟩
      (some ⟨some (.inr .drainInputVertex), clearRegister state,
        Function.update base (.inr .currentSize) (encodeWord (cloudSize d * n))⟩)
      (2 * (n + 1) + 1) := by
  have run := affinePhaseInTime positive H growth .multiplySize base n []
    (by simpa only [affineSource, inputVertexTape, toBoolTapes, toBoolWord,
      List.append_nil] using sourceWord)
    scratchEmpty state
  simpa only [affineExit, affineResultTapes, affineDestination, affineCoefficient,
    boolWord, toBoolTapes, toBoolWord, destinationEmpty, List.append_nil] using run

end Composition

variable {ρ : Type} {d : Nat}

/-- The guard changes only the physical remaining-level word. -/
theorem boundaryTapes_update_level (remaining current next : Nat)
    (word suffix : List Bool) :
    Function.update (boundaryTapes remaining current word suffix)
      (.inr .remainingLevel) (encodeWord next ++ suffix) =
      boundaryTapes next current word suffix := by
  funext tape
  rcases tape with tape | extra
  · rcases tape with row | extra
    · cases row <;> simp [boundaryTapes, tableFrame, MachineEmbedding.tapes, Function.update]
    · cases extra <;> simp [boundaryTapes, tableFrame, MachineEmbedding.tapes, Function.update]
  · cases extra <;> simp [boundaryTapes, extraFrame, MachineEmbedding.tapes, Function.update]

/-- The two literal prefixes install the actual level-zero table and unary one. -/
theorem initialTapes_initialize (level : Nat) (suffix : List Bool) :
    Function.update
      (Function.update (initialTapes level suffix) tableTape (initialEncoding d))
      (.inr .currentSize) (encodeWord 1) =
      boundaryTapes level 1 (initialEncoding d) suffix := by
  funext tape
  rcases tape with tape | extra
  · rcases tape with row | extra
    · cases row <;> simp [initialTapes, boundaryTapes, tableFrame,
        MachineEmbedding.tapes, Function.update, tableTape]
    · cases extra <;> simp [initialTapes, boundaryTapes, tableFrame,
        MachineEmbedding.tapes, Function.update, tableTape]
  · cases extra <;> simp [initialTapes, boundaryTapes, extraFrame,
      MachineEmbedding.tapes, Function.update, tableTape]

variable [Fintype ρ]

/-- Static alphabet transport preserves this actual single transition. -/
theorem actualStep_of_boolStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d)
    (start finish : TM2.Cfg BoolAlphabet (Label d) (State ρ d))
    (run : TM2.step (boolView positive H growth) start = some finish) :
    TM2.step (program positive H growth)
      (MachineAlphabetTransport.configuration alphabet_eq.symm start) =
      some (MachineAlphabetTransport.configuration alphabet_eq.symm finish) := by
  have h := MachineAlphabetTransport.step_simulation alphabet_eq.symm
    (boolView positive H growth) start
  rw [run] at h
  simpa only [boolView, MachineAlphabetTransport.program_symm_roundtrip,
    Option.map_some] using h

theorem bool_initializeStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d) :
    TM2.step (boolView positive H growth) ⟨some (.inr .initialize_), state, base⟩ =
      some ⟨some (.inr .levelGuard), normalizeState positive H state,
        Function.update
          (Function.update base tableTape (initialEncoding d ++ base (.inl (.inl .table))))
          (.inr .currentSize) (encodeWord 1 ++ base (.inr .currentSize))⟩ := by
  change some (TM2.stepAux (boolView positive H growth (.inr .initialize_)) state base) = _
  rw [boolView_outer]
  simp only [boolOuterStatement, Reduction.MachineSubstitution.stepAux_pushWord,
    List.reverse_reverse, TM2.stepAux]
  rfl

theorem bool_levelGuard_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d)
    (remaining : Nat) (suffix : List Bool)
    (counter : base (.inr .remainingLevel) = encodeWord (remaining + 1) ++ suffix) :
    TM2.step (boolView positive H growth) ⟨some (.inr .levelGuard), state, base⟩ =
      some ⟨some (.inr (.affine .copyCount .seed)), clearRegister state,
        Function.update base (.inr .remainingLevel) (encodeWord remaining ++ suffix)⟩ := by
  change some (TM2.stepAux (boolView positive H growth (.inr .levelGuard)) state base) = _
  rw [boolView_outer]
  simp [boolOuterStatement, MachineControl.statement, MachineUnaryCounter.guard,
    TM2.stepAux, registerStates, clearRegister, MachineExpanderTable.clearRegister,
    counter, encodeWord, List.replicate_succ]

theorem bool_levelGuard_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d)
    (suffix : List Bool)
    (counter : base (.inr .remainingLevel) = encodeWord 0 ++ suffix) :
    TM2.step (boolView positive H growth) ⟨some (.inr .levelGuard), state, base⟩ =
      some ⟨some (.inr .done), clearRegister state, base⟩ := by
  change some (TM2.stepAux (boolView positive H growth (.inr .levelGuard)) state base) = _
  rw [boolView_outer]
  simp [boolOuterStatement, MachineControl.statement, MachineUnaryCounter.guard,
    TM2.stepAux, registerStates, clearRegister, MachineExpanderTable.clearRegister,
    counter, encodeWord]

theorem bool_doneStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d) :
    TM2.step (boolView positive H growth) ⟨some (.inr .done), state, base⟩ =
      some ⟨none, normalizeState positive H state, base⟩ := by
  change some (TM2.stepAux (boolView positive H growth (.inr .done)) state base) = _
  rw [boolView_outer]
  rfl

/-- The literal initialization executes in one transition of the actual program. -/
theorem initializeStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H growth) ⟨some (.inr .initialize_), state, base⟩ =
      some ⟨some (.inr .levelGuard), normalizeState positive H state,
        Function.update
          (Function.update base tableTape (initialEncoding d ++ base (.inl (.inl .table))))
          (.inr .currentSize) (encodeWord 1 ++ base (.inr .currentSize))⟩ := by
  have h := actualStep_of_boolStep positive H growth _ _
    (bool_initializeStep positive H growth (toBoolTapes base) state)
  simp only [configuration_fromBool, fromBoolTapes_update, fromBool_toBool] at h
  exact h

/-- A positive level physically loses one true bit, retaining its delimiter and suffix. -/
theorem levelGuard_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (remaining : Nat) (suffix : List Bool)
    (counter : base (.inr .remainingLevel) = encodeWord (remaining + 1) ++ suffix) :
    TM2.step (program positive H growth) ⟨some (.inr .levelGuard), state, base⟩ =
      some ⟨some (.inr (.affine .copyCount .seed)), clearRegister state,
        Function.update base (.inr .remainingLevel) (encodeWord remaining ++ suffix)⟩ := by
  have h := actualStep_of_boolStep positive H growth _ _
    (bool_levelGuard_succStep positive H growth (toBoolTapes base) state
      remaining suffix counter)
  simpa only [configuration_fromBool, fromBoolTapes_update, fromBool_toBool,
    boolWord] using h

/-- The zero delimiter is retained when the family loop enters its final halt. -/
theorem levelGuard_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (suffix : List Bool)
    (counter : base (.inr .remainingLevel) = encodeWord 0 ++ suffix) :
    TM2.step (program positive H growth) ⟨some (.inr .levelGuard), state, base⟩ =
      some ⟨some (.inr .done), clearRegister state, base⟩ := by
  have h := actualStep_of_boolStep positive H growth _ _
    (bool_levelGuard_zeroStep positive H growth (toBoolTapes base) state suffix counter)
  simpa only [configuration_fromBool, fromBool_toBool] using h

theorem doneStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H growth) ⟨some (.inr .done), state, base⟩ =
      some ⟨none, normalizeState positive H state, base⟩ := by
  have h := actualStep_of_boolStep positive H growth _ _
    (bool_doneStep positive H growth (toBoolTapes base) state)
  simpa only [configuration_fromBool, fromBool_toBool] using h

theorem initialize_boundaryStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (level : Nat) (suffix : List Bool) (state : State ρ d) :
    TM2.step (program positive H growth)
      ⟨some (.inr .initialize_), state, initialTapes level suffix⟩ =
      some ⟨some (.inr .levelGuard), initialState positive H (caller state),
        boundaryTapes level 1 (initialEncoding d) suffix⟩ := by
  have h := initializeStep positive H growth (initialTapes level suffix) state
  have ht : initialTapes level suffix (.inl (.inl .table)) = [] := rfl
  have hc : initialTapes level suffix (.inr .currentSize) = [] := rfl
  simp only [ht, hc, List.append_nil, normalizeState] at h
  exact h.trans (congrArg
    (fun tapes : ∀ tape, List (Alphabet tape) =>
      (some ⟨some (.inr .levelGuard), initialState positive H (caller state), tapes⟩ :
        Option (TM2.Cfg Alphabet (Label d) (State ρ d))))
    (initialTapes_initialize level suffix))

theorem levelGuard_boundary_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (remaining current : Nat)
    (word suffix : List Bool) (state : State ρ d) :
    TM2.step (program positive H growth)
      ⟨some (.inr .levelGuard), state, boundaryTapes (remaining + 1) current word suffix⟩ =
      some ⟨some (.inr (.affine .copyCount .seed)), clearRegister state,
        boundaryTapes remaining current word suffix⟩ := by
  simpa only [boundaryTapes_update_level] using
    levelGuard_succStep positive H growth
      (boundaryTapes (remaining + 1) current word suffix) state remaining suffix rfl

theorem levelGuard_boundary_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (current : Nat)
    (word suffix : List Bool) (state : State ρ d) :
    TM2.step (program positive H growth)
      ⟨some (.inr .levelGuard), state, boundaryTapes 0 current word suffix⟩ =
      some ⟨some (.inr .done), clearRegister state,
        boundaryTapes 0 current word suffix⟩ :=
  levelGuard_zeroStep positive H growth
    (boundaryTapes 0 current word suffix) state suffix rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily


/-!
# Concrete boundary steps of the expander-table machine

Every execution theorem below reduces the actual common program statement.
States and dependent tape frames are arbitrary; only the relevant unary word
or finite-position branch is specified. No phase execution is a premise.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} {d : Nat}

theorem nextPosition_val_of_lt (positive : 0 < d) (position : Position d)
    (more : position.val + 1 < rowFactor d) :
    (nextPosition positive position).val = position.val + 1 := Nat.mod_eq_of_lt more

/-- Replacing the count word leaves the entire row frame and result unchanged. -/
theorem boundaryTapes_update_count (vertex remaining next : Nat)
    (oldTable output countSuffix result : List Bool) :
    Function.update (boundaryTapes vertex remaining oldTable output countSuffix result)
      (.inr .vertexCount) (encodeWord next ++ countSuffix) =
      boundaryTapes vertex next oldTable output countSuffix result := by
  funext tape
  rcases tape with row | extra
  · cases row <;> simp [boundaryTapes, rowTapes, MachineEmbedding.tapes, Function.update]
  · cases extra <;> simp [boundaryTapes, extraTapes, MachineEmbedding.tapes, Function.update]

/-- The last row's one actual push increments the unary vertex word. -/
theorem boundaryTapes_increment_vertex (vertex remaining : Nat)
    (oldTable output countSuffix result : List Bool) :
    Function.update (boundaryTapes vertex remaining oldTable output countSuffix result)
      (.inl .inputVertex) (true :: encodeWord vertex) =
      boundaryTapes (vertex + 1) remaining oldTable output countSuffix result := by
  funext tape
  rcases tape with row | extra
  · cases row <;>
      simp [boundaryTapes, rowTapes, MachineEmbedding.tapes, Function.update,
        encodeWord, List.replicate_succ]
  · cases extra <;>
      simp [boundaryTapes, extraTapes, MachineEmbedding.tapes, Function.update]

theorem initialTapes_initialize (vertices : Nat) (oldTable countSuffix : List Bool) :
    Function.update (initialTapes vertices oldTable countSuffix) (.inl .inputVertex) [false] =
      boundaryTapes 0 vertices oldTable [] countSuffix [] := by
  funext tape
  rcases tape with row | extra
  · cases row <;>
      simp [initialTapes, boundaryTapes, rowTapes, MachineEmbedding.tapes,
        Function.update, encodeWord]
  · cases extra <;>
      simp [initialTapes, boundaryTapes, extraTapes, MachineEmbedding.tapes,
        Function.update]

variable [Fintype ρ]

theorem initializeStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H) ⟨some (.inr .initialize_), state, base⟩ =
      some ⟨some (.inr .vertexGuard), resetState positive H state,
        Function.update base (.inl .inputVertex) (false :: base (.inl .inputVertex))⟩ := by
  change some (TM2.stepAux (program positive H (.inr .initialize_)) state base) = _
  rw [program_outer]
  rfl

theorem initialize_boundaryStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertices : Nat) (oldTable countSuffix : List Bool) (state : State ρ d) :
    TM2.step (program positive H)
      ⟨some (.inr .initialize_), state, initialTapes vertices oldTable countSuffix⟩ =
      some ⟨some (.inr .vertexGuard), initialState positive H (caller state),
        boundaryTapes 0 vertices oldTable [] countSuffix []⟩ := by
  have h := initializeStep positive H (initialTapes vertices oldTable countSuffix) state
  have input : initialTapes vertices oldTable countSuffix (.inl .inputVertex) = [] := rfl
  simp only [input, resetState] at h
  exact h.trans (congrArg
    (fun tapes : ∀ tape, List (Alphabet tape) =>
      (some ⟨some (.inr .vertexGuard), initialState positive H (caller state), tapes⟩ :
        Option (TM2.Cfg Alphabet (Label d) (State ρ d))))
    (initialTapes_initialize vertices oldTable countSuffix))

/-- A positive vertex counter is physically decremented; its suffix remains. -/
theorem vertexGuard_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (remaining : Nat) (suffix : List Bool)
    (counter : base (.inr .vertexCount) = encodeWord (remaining + 1) ++ suffix) :
    TM2.step (program positive H) ⟨some (.inr .vertexGuard), state, base⟩ =
      some ⟨some (.inr .prepareRow), clearRegister state,
        Function.update base (.inr .vertexCount) (encodeWord remaining ++ suffix)⟩ := by
  change some (TM2.stepAux (program positive H (.inr .vertexGuard)) state base) = _
  rw [program_outer]
  simp [outerStatement, MachineControl.statement, vertexGuardCore, TM2.stepAux,
    guardStates, clearRegister, counter, encodeWord, List.replicate_succ]

/-- The zero delimiter is retained when the loop enters output reversal. -/
theorem vertexGuard_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (suffix : List Bool)
    (counter : base (.inr .vertexCount) = encodeWord 0 ++ suffix) :
    TM2.step (program positive H) ⟨some (.inr .vertexGuard), state, base⟩ =
      some ⟨some (.inr .reverseOutput), clearRegister state, base⟩ := by
  change some (TM2.stepAux (program positive H (.inr .vertexGuard)) state base) = _
  rw [program_outer]
  simp [outerStatement, MachineControl.statement, vertexGuardCore, TM2.stepAux,
    guardStates, clearRegister, counter, encodeWord]

theorem vertexGuard_boundary_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    TM2.step (program positive H)
      ⟨some (.inr .vertexGuard), state,
        boundaryTapes vertex (remaining + 1) oldTable output countSuffix result⟩ =
      some ⟨some (.inr .prepareRow), clearRegister state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩ := by
  simpa only [boundaryTapes_update_count] using
    vertexGuard_succStep positive H
      (boundaryTapes vertex (remaining + 1) oldTable output countSuffix result)
      state remaining countSuffix rfl

theorem vertexGuard_boundary_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex : Nat) (oldTable output countSuffix result : List Bool) (state : State ρ d) :
    TM2.step (program positive H)
      ⟨some (.inr .vertexGuard), state,
        boundaryTapes vertex 0 oldTable output countSuffix result⟩ =
      some ⟨some (.inr .reverseOutput), clearRegister state,
        boundaryTapes vertex 0 oldTable output countSuffix result⟩ :=
  vertexGuard_zeroStep positive H
    (boundaryTapes vertex 0 oldTable output countSuffix result) state countSuffix rfl

/-- Preparing a row modifies finite control only, preserving every tape. -/
theorem prepareRowStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H) ⟨some (.inr .prepareRow), state, base⟩ =
      some ⟨some (.inl .initialize_), prepareState positive H state, base⟩ := by
  change some (TM2.stepAux (program positive H (.inr .prepareRow)) state base) = _
  rw [program_outer]
  rfl

/-- A nonfinal row advances the finite position without changing tapes. -/
theorem afterRow_moreStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (more : state.2.val + 1 < rowFactor d) :
    TM2.step (program positive H) ⟨some (.inr .afterRow), state, base⟩ =
      some ⟨some (.inr .prepareRow), advancePositionState positive state, base⟩ := by
  change some (TM2.stepAux (program positive H (.inr .afterRow)) state base) = _
  rw [program_outer]
  simp [outerStatement, TM2.stepAux, more]

/-- The final row increments the tape vertex and resets the finite position. -/
theorem afterRow_lastStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (last : ¬ state.2.val + 1 < rowFactor d) :
    TM2.step (program positive H) ⟨some (.inr .afterRow), state, base⟩ =
      some ⟨some (.inr .vertexGuard), resetPositionState positive state,
        Function.update base (.inl .inputVertex) (true :: base (.inl .inputVertex))⟩ := by
  change some (TM2.stepAux (program positive H (.inr .afterRow)) state base) = _
  rw [program_outer]
  simp [outerStatement, TM2.stepAux, last]

theorem afterRow_last_boundaryStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) (last : ¬ state.2.val + 1 < rowFactor d) :
    TM2.step (program positive H)
      ⟨some (.inr .afterRow), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩ =
      some ⟨some (.inr .vertexGuard), resetPositionState positive state,
        boundaryTapes (vertex + 1) remaining oldTable output countSuffix result⟩ := by
  have input : boundaryTapes vertex remaining oldTable output countSuffix result
      (.inl .inputVertex) = encodeWord vertex := rfl
  have h := afterRow_lastStep positive H
    (boundaryTapes vertex remaining oldTable output countSuffix result) state last
  simp only [input] at h
  exact h.trans (congrArg
    (fun tapes : ∀ tape, List (Alphabet tape) =>
      (some ⟨some (.inr .vertexGuard), resetPositionState positive state, tapes⟩ :
        Option (TM2.Cfg Alphabet (Label d) (State ρ d))))
    (boundaryTapes_increment_vertex vertex remaining oldTable output countSuffix result))

/-- One reversal step moves an actual symbol and preserves the finite position. -/
theorem reverseOutput_consStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (symbol : Bool) (word : List Bool) (source : base (.inl .output) = symbol :: word) :
    TM2.step (program positive H) ⟨some (.inr .reverseOutput), state, base⟩ =
      some ⟨some (.inr .reverseOutput), ((state.1.1, some symbol), state.2),
        Function.update (Function.update base (.inl .output) word)
          (.inr .result) (symbol :: base (.inr .result))⟩ := by
  change some (TM2.stepAux (program positive H (.inr .reverseOutput)) state base) = _
  rw [program_outer]
  simp [outerStatement, MachineControl.statement, Reduction.MachineTransfer.loopAt,
    Reduction.MachineTransfer.exitAt, TM2.stepAux, guardStates, source]

theorem reverseOutput_nilStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (source : base (.inl .output) = []) :
    TM2.step (program positive H) ⟨some (.inr .reverseOutput), state, base⟩ =
      some ⟨some (.inr .done), clearRegister state, base⟩ := by
  have same : Function.update base (.inl .output) [] = base := by
    simpa only [source] using Function.update_eq_self (.inl .output) base
  change some (TM2.stepAux (program positive H (.inr .reverseOutput)) state base) = _
  rw [program_outer]
  simp [outerStatement, MachineControl.statement, Reduction.MachineTransfer.loopAt,
    Reduction.MachineTransfer.exitAt, TM2.stepAux, guardStates, clearRegister, source, same]

theorem doneStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H) ⟨some (.inr .done), state, base⟩ =
      some ⟨none, state, base⟩ := by
  change some (TM2.stepAux (program positive H (.inr .done)) state base) = _
  rw [program_outer]
  rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineExpanderRowCleanup
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.boolView_outer _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.caller_initialState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.caller_normalizeState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.clearRegister_initialState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.clearRegister_position _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.clearRegister_register _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.fromBoolTapes_update _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.program_outer _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.program_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.registerStates_symm_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.tableExecution_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.toBoolTapes_update _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamilyBounds.familyBudget_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamilyBounds.resizeSum_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.RowData.firstValue_div_degree _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.RowData.firstValue_mod_degree _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.RowData.secondValue_div_degree _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.RowData.secondValue_mod_degree _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionStates_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_emitScratch _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_emitScratch _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_lookupRestore _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_lookupWork _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_emitScratch _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_lookupRestore _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_lookupWork _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.program_firstEmit _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.program_outputEmit _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.program_secondEmit _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.accumulatedVertices_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.caller_boundaryState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.caller_prepareState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.caller_resetState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.caller_rowAfterState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.clearRegister_boundaryState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.clearRegister_position _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.clearRegister_register _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.guardStates_symm_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.prepareState_boundaryState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.program_outer _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.program_row _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.rowAfterState_position _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.rowExecution_steps _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.generatedWords_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.priorVertices_full _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.priorVertices_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.vertexWords_drop_full _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.vertexWords_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.overlay_accepts_expander _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.overlay_accepts_old _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_internal _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.actualRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {K Λ ρ : Type} [DecidableEq K]

variable [Fintype ρ] {d : Nat}

/-- One cleanup phase follows the actual drain instruction at its placed label. -/
theorem cleanupOneTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (i : Fin 6) (base : K → List Bool) (state : State ρ d) :
    (advance (TM2.step target))^[((base (ports (dirtyTape i))).length + 1)]
      (some ⟨some (labels (.cleanup i)), state, base⟩) =
      some ⟨some (if hi : i.val + 1 < 6 then labels (.cleanup ⟨i.val + 1, hi⟩)
          else labels .done),
        (state.1, none), Function.update base (ports (dirtyTape i)) []⟩ := by
  have run := MachineDrain.drainTrace (ports (dirtyTape i)) (labels (.cleanup i))
    (some (if hi : i.val + 1 < 6 then labels (.cleanup ⟨i.val + 1, hi⟩)
      else labels .done)) target
    (by simpa only [statement] using code (.cleanup i))
    base (base (ports (dirtyTape i))) state.1 state.2
  simpa only [Function.update_eq_self] using run

/-- All six phases execute in the common program, with exactly the sum of
the six initial word lengths plus one empty-branch transition per tape. -/
theorem cleanupTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (distinct : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    (advance (TM2.step target))^[cleanupSteps ports base]
      (some ⟨some (labels (.cleanup 0)), state, base⟩) =
      some ⟨some (labels .done), (state.1, none), cleanupTapes ports base⟩ := by
  let t1 := Function.update base (ports .queryIndex) []
  let t2 := Function.update t1 (ports .lookupOutput) []
  let t3 := Function.update t2 (ports .quotientFirst) []
  let t4 := Function.update t3 (ports .quotientSecond) []
  let t5 := Function.update t4 (ports .remainderFirst) []
  have h0 := cleanupOneTraceAt positive H ports labels exit target code 0 base state
  have h1 := cleanupOneTraceAt positive H ports labels exit target code 1 t1 (state.1, none)
  have h2 := cleanupOneTraceAt positive H ports labels exit target code 2 t2 (state.1, none)
  have h3 := cleanupOneTraceAt positive H ports labels exit target code 3 t3 (state.1, none)
  have h4 := cleanupOneTraceAt positive H ports labels exit target code 4 t4 (state.1, none)
  have h5 := cleanupOneTraceAt positive H ports labels exit target code 5 t5 (state.1, none)
  simp [t1, t2, t3, t4, t5, distinct.eq_iff,
    -Function.iterate_succ] at h0 h1 h2 h3 h4 h5
  have finished := join_trace (join_trace (join_trace (join_trace (join_trace h0 h1) h2) h3) h4) h5
  simpa only [cleanupSteps, cleanupTapes] using finished

/-- The done label transfers control without inspecting or modifying any tape. -/
theorem doneStepAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    TM2.step target ⟨some (labels .done), state, base⟩ = some ⟨exit, state, base⟩ := by
  change some (TM2.stepAux (target (labels .done)) state base) = _
  rw [code]
  cases exit <;> rfl

/-- Cleanup followed by the actual done-to-caller transition. -/
theorem cleanupExitTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (distinct : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    (advance (TM2.step target))^[cleanupSteps ports base + 1]
      (some ⟨some (labels (.cleanup 0)), state, base⟩) =
      some ⟨exit, (state.1, none), cleanupTapes ports base⟩ := by
  have cleaned := cleanupTraceAt positive H ports distinct labels exit target code base state
  have done : (advance (TM2.step target))^[1]
      (some ⟨some (labels .done), (state.1, none), cleanupTapes ports base⟩) =
      some ⟨exit, (state.1, none), cleanupTapes ports base⟩ := by
    simpa only [Function.iterate_one, advance_some] using
      doneStepAt positive H ports labels exit target code (cleanupTapes ports base) (state.1, none)
  exact join_trace cleaned done

/-- Initialization physically pushes four delimiters and resets the bit register. -/
theorem initializeStepAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (distinct : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    TM2.step target ⟨some (labels .initialize_), state, base⟩ =
      some ⟨some (labels (.firstEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))),
        (state.1, none), initializedTapes ports base⟩ := by
  change some (TM2.stepAux (target (labels .initialize_)) state base) = _
  rw [code]
  simp [statement, TM2.stepAux, initializedTapes, distinct.eq_iff]

/-- The query-clear phase removes one symbol from each of its two tapes and
preserves the complete finite state and every other tape. -/
theorem clearQueryStepAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (distinct : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    TM2.step target ⟨some (labels .clearQuery), state, base⟩ =
      some ⟨some (labels (.secondEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))),
        state, clearedQueryTapes ports base⟩ := by
  change some (TM2.stepAux (target (labels .clearQuery)) state base) = _
  rw [code]
  simp [statement, TM2.stepAux, clearedQueryTapes, distinct.eq_iff]

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineExpanderRowEmitLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

section

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.AlphabetTable

theorem affinePlan_bits {σ : Type} {bound : Nat} (coefficient : Nat)
    (offset : σ → Fin bound) (n : Nat) (ambient : σ) :
    Emitter.prefixBits (affinePlan coefficient offset) (fun _ : Fin 1 => n) ambient 3 =
      encodeWord (coefficient * n + (offset ambient).val) := by
  change Emitter.prefixBits
    (Emitter.listCommands (Emitter.affineCommands [((0 : Fin 1), coefficient)] offset))
    (fun _ : Fin 1 => n) ambient
    (Emitter.affineCommands [((0 : Fin 1), coefficient)] offset).length = _
  rw [Emitter.bits_listCommands, Emitter.affineCommands_bits]
  simp [Emitter.affineValue]

theorem affinePlan_steps {σ : Type} {bound : Nat} (coefficient : Nat)
    (offset : σ → Fin bound) (n : Nat) :
    Emitter.prefixSteps (affinePlan coefficient offset) (fun _ : Fin 1 => n) 3 + 1 =
      emitSteps n := by
  simp [affinePlan, Emitter.prefixSteps, Emitter.commandAt, Emitter.listCommands,
    Emitter.affineCommands, Emitter.commandSteps, emitSteps]

variable {ρ : Type} [Fintype ρ] {d : Nat}

section Embedded

variable {K Λ : Type} [DecidableEq K]

/-- The code premise identifies concrete statements in a caller's program;
it does not assume any phase execution. -/
theorem firstEmitTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .inputVertex) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step target))^[emitSteps n]
      (some ⟨some (labels (.firstEmit (Emitter.labelAt 3 _ 0 .entry))),
        ((ambient, ()), none), base⟩) =
      some ⟨some (labels .firstReverse), ((ambient, ()), none),
        emittedWord (ports .queryReverse) base (firstAddress n ambient.1.2)⟩ := by
  have code : ∀ l, target (labels (.firstEmit l)) =
      Emitter.statement (firstPlan ρ d) (fun _ : Fin 1 => ports .inputVertex)
        (ports .emitScratch) (ports .queryReverse) (fun k => labels (.firstEmit k))
        (some (labels .firstReverse)) l := by
    intro l
    rw [atLabels]
    rfl
  have run := Emitter.planTrace (firstPlan ρ d) (fun _ : Fin 1 => ports .inputVertex)
    (ports .emitScratch) (ports .queryReverse)
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro h; have h' := portsInjective h; cases h')
    (fun k => labels (.firstEmit k)) (some (labels .firstReverse)) target code
    (fun _ : Fin 1 => n) base (fun _ => source) scratch ambient
  simpa only [firstPlan, affinePlan_steps, affinePlan_bits, Emitter.resultTapes,
    emittedWord, firstAddress] using run

theorem secondEmitTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .quotientFirst) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step target))^[emitSteps n]
      (some ⟨some (labels (.secondEmit (Emitter.labelAt 3 _ 0 .entry))),
        ((ambient, ()), none), base⟩) =
      some ⟨some (labels .secondReverse), ((ambient, ()), none),
        emittedWord (ports .queryReverse) base (secondAddress n ambient.1.2)⟩ := by
  have code : ∀ l, target (labels (.secondEmit l)) =
      Emitter.statement (secondPlan ρ d) (fun _ : Fin 1 => ports .quotientFirst)
        (ports .emitScratch) (ports .queryReverse) (fun k => labels (.secondEmit k))
        (some (labels .secondReverse)) l := by
    intro l
    rw [atLabels]
    rfl
  have run := Emitter.planTrace (secondPlan ρ d) (fun _ : Fin 1 => ports .quotientFirst)
    (ports .emitScratch) (ports .queryReverse)
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro h; have h' := portsInjective h; cases h')
    (fun k => labels (.secondEmit k)) (some (labels .secondReverse)) target code
    (fun _ : Fin 1 => n) base (fun _ => source) scratch ambient
  simpa only [secondPlan, affinePlan_steps, affinePlan_bits, Emitter.resultTapes,
    emittedWord, secondAddress] using run

theorem outputEmitTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .quotientSecond) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step target))^[emitSteps n]
      (some ⟨some (labels (.outputEmit (Emitter.labelAt 3 _ 0 .entry))),
        ((ambient, ()), none), base⟩) =
      some ⟨some (labels (.cleanup 0)), ((ambient, ()), none),
        emittedWord (ports .output) base (outputAddress n ambient.1.2)⟩ := by
  have code : ∀ l, target (labels (.outputEmit l)) =
      Emitter.statement (outputPlan ρ d) (fun _ : Fin 1 => ports .quotientSecond)
        (ports .emitScratch) (ports .output) (fun k => labels (.outputEmit k))
        (some (labels (.cleanup 0))) l := by
    intro l
    rw [atLabels]
    rfl
  have run := Emitter.planTrace (outputPlan ρ d) (fun _ : Fin 1 => ports .quotientSecond)
    (ports .emitScratch) (ports .output)
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro h; have h' := portsInjective h; cases h')
    (fun k => labels (.outputEmit k)) (some (labels (.cleanup 0))) target code
    (fun _ : Fin 1 => n) base (fun _ => source) scratch ambient
  simpa only [outputPlan, affinePlan_steps, affinePlan_bits, Emitter.resultTapes,
    emittedWord, outputAddress] using run

end Embedded

end

/-!
# Actual lookup and reversal phases of the expander row program

The Boolean phase selector chooses the first or second occurrence of the same
preserving lookup. The selected word is proved to be the actual stored reverse
index of the supplied graph row. All execution facts follow from the concrete
program statements; no phase execution is assumed.
-/

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineComposition

def lookupPhaseLabel {d : Nat} (second : Bool)
    (l : MachinePreservingLookupClean.Label) : Label d :=
  if second then .secondLookup l else .firstLookup l

def scanPhaseLabel {d : Nat} (second : Bool) : Label d :=
  if second then .secondScan else .firstScan

def reversePhaseLabel {d : Nat} (second : Bool) : Label d :=
  if second then .secondReverse else .firstReverse

theorem lookupTape_injective : Function.Injective lookupTape := by decide

variable {K Λ ρ : Type} [DecidableEq K] [Fintype ρ]

section Lookup

variable {v d : Nat} (second : Bool) (positive : 0 < d)
    (H : Table (cloudSize d) d) (ports : Tape → K)
    (distinct : Function.Injective ports) (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (base : K → List Bool) (G : Table v (degree d))
    (tableWord : base (ports .table) = encodeWords (rotationWords G))
    (scratchEmpty : base (ports .lookupRestore) = [])
    (x : Fin v × Fin (degree d)) (indexSuffix : List Bool)
    (counterWord : base (ports .queryIndex) =
      encodeWord (rowIndex v (degree d) x).val ++ indexSuffix)
    (workEmpty : base (ports .lookupWork) = [])
    (ambient : (Ambient ρ d × Fin (degree d)) × Unit) (register : Option Bool)

include positive H distinct exit code tableWord scratchEmpty counterWord workEmpty

/-- Actual first/second lookup execution on a stored graph row. The selected
reverse index is obtained from `rotationWords_getElem?`, not a caller premise. -/
theorem lookupPhaseTrace :
    (advance (TM2.step target))^[MachinePreservingLookupClean.steps
        (rotationWords G) (rowIndex v (degree d) x).val]
      (some ⟨some (labels (lookupPhaseLabel second (.run .copyFirst))),
        (ambient, register), base⟩) =
      some ⟨some (labels (scanPhaseLabel second)), (ambient, none),
        lookupResultTapes ports base (reverseIndex G (rowIndex v (degree d) x)).val
          indexSuffix⟩ := by
  apply MachinePreservingLookupClean.traceAt_fromTapes (ports ∘ lookupTape)
    (distinct.comp lookupTape_injective)
    (fun l => labels (lookupPhaseLabel second l)) (some (labels (scanPhaseLabel second)))
    target
  · intro l
    cases second
    · exact code (.firstLookup l)
    · exact code (.secondLookup l)
  · exact tableWord
  · exact scratchEmpty
  · exact rotationWords_getElem? G (rowIndex v (degree d) x)
  · exact counterWord
  · exact workEmpty

end Lookup

variable {d : Nat} (second : Bool) (positive : 0 < d)
    (H : Table (cloudSize d) d) (ports : Tape → K)
    (distinct : Function.Injective ports) (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (base : K → List Bool)
    (ambient : (Ambient ρ d × Fin (degree d)) × Unit) (register : Option Bool)

include positive H distinct exit code

/-- The reversal consumes the reverse query word and prepends its forward
encoding to the index tape, retaining every other tape and finite state. -/
theorem reversePhaseTrace :
    (advance (TM2.step target))^[(base (ports .queryReverse)).length + 1]
      (some ⟨some (labels (reversePhaseLabel second)), (ambient, register), base⟩) =
      some ⟨some (labels (lookupPhaseLabel second (.run .copyFirst))), (ambient, none),
        Reduction.MachineTransfer.tapesAt (ports .queryReverse) (ports .queryIndex) base []
          ((base (ports .queryReverse)).reverse ++ base (ports .queryIndex))⟩ := by
  have h := Reduction.MachineTransfer.transferAt_fromTapes
    (ports .queryReverse) (ports .queryIndex)
    (fun h => (by decide : Tape.queryReverse ≠ .queryIndex) (distinct h))
    id false (labels (reversePhaseLabel second))
    (some (labels (lookupPhaseLabel second (.run .copyFirst)))) target
    (by cases second <;> exact code _) base ambient register
  unfold Reduction.MachineTransfer.nextAt at h
  unfold advance
  simpa only [List.map_id] using h

/-- Reversing an actual emitted unary field takes exactly `index + 2` steps.
This includes consuming the field's delimiter and leaving the reversal loop. -/
theorem reversePhaseTrace_unary (index : Nat) (suffix : List Bool)
    (queryWord : base (ports .queryReverse) = (encodeWord index).reverse)
    (indexWord : base (ports .queryIndex) = suffix) :
    (advance (TM2.step target))^[index + 2]
      (some ⟨some (labels (reversePhaseLabel second)), (ambient, register), base⟩) =
      some ⟨some (labels (lookupPhaseLabel second (.run .copyFirst))), (ambient, none),
        Reduction.MachineTransfer.tapesAt (ports .queryReverse) (ports .queryIndex) base []
          (encodeWord index ++ suffix)⟩ := by
  have h := reversePhaseTrace second positive H ports distinct labels exit target code
    base ambient register
  simpa only [queryWord, indexWord, List.length_reverse, encodeWord_length,
    List.reverse_reverse, Nat.add_assoc] using h

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineExpanderRowFrames
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.clearRegister_register _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.fromBoolTapes_update _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.registerStates_symm_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.tableExecution_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.toBoolTapes_update _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.accumulatedVertices_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.caller_rowAfterState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.clearRegister_register _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.guardStates_symm_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.program_row _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.rowAfterState_position _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.rowExecution_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.generatedWords_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.priorVertices_full _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.priorVertices_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.vertexWords_drop_full _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.vertexWords_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Concrete data and tape frames for an actual expander-row computation

Only the five actual row inputs are stored. Every address, table return and
finite control value below is computed from those inputs. The thirteen tape
frames use the existing phase-output functions. These are data identities and
size bounds, not assumed machine executions. Kernel-checked with Lean 4.33.1.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

namespace RowData

variable {v d : Nat} (r : RowData v d)

def tableLength : Nat := (encodeWords (rotationWords r.oldTable)).length

theorem query1_eq_firstRow : r.query1 = r.firstRow.val :=
  firstAddress_eq_rowIndex r.inputVertex r.control0

theorem query2_eq_secondRow : r.query2 = r.secondRow.val :=
  secondAddress_eq_rowIndex r.firstVertex r.control1

theorem firstReturn_eq_residue (positive : 0 < d) :
    r.firstReturn = MachineFixedDivMod.residue (degree d) (Nat.mul_pos positive positive)
      r.firstValue := Fin.ext rfl

theorem secondReturn_eq_residue (positive : 0 < d) :
    r.secondReturn = MachineFixedDivMod.residue (degree d) (Nat.mul_pos positive positive)
      r.secondValue := Fin.ext rfl

theorem rows_le_tableLength : v * degree d ≤ r.tableLength := by
  simp only [tableLength, encodeWords_length, rotationWords_length]
  omega

theorem query1_le_tableLength : r.query1 ≤ r.tableLength := by
  rw [query1_eq_firstRow]
  exact r.firstRow.isLt.le.trans r.rows_le_tableLength

theorem query2_le_tableLength : r.query2 ≤ r.tableLength := by
  rw [query2_eq_secondRow]
  exact r.secondRow.isLt.le.trans r.rows_le_tableLength

theorem firstValue_le_tableLength : r.firstValue ≤ r.tableLength :=
  (reverseIndex r.oldTable r.firstRow).isLt.le.trans r.rows_le_tableLength

theorem secondValue_le_tableLength : r.secondValue ≤ r.tableLength :=
  (reverseIndex r.oldTable r.secondRow).isLt.le.trans r.rows_le_tableLength

theorem inputVertex_le_tableLength : r.inputVertex.val ≤ r.tableLength := by
  have hq : 1 ≤ degree d := Nat.zero_lt_of_lt r.inputPort.isLt
  have hv : v ≤ v * degree d := by simpa using Nat.mul_le_mul_left v hq
  exact r.inputVertex.isLt.le.trans (hv.trans r.rows_le_tableLength)

theorem firstVertex_le_tableLength : r.firstVertex.val ≤ r.tableLength := by
  rw [← firstValue_div_degree]
  exact (Nat.div_le_self r.firstValue (degree d)).trans r.firstValue_le_tableLength

theorem secondVertex_le_tableLength : r.secondVertex.val ≤ r.tableLength := by
  rw [← secondValue_div_degree]
  exact (Nat.div_le_self r.secondValue (degree d)).trans r.secondValue_le_tableLength

theorem firstReturn_le_tableLength : r.firstReturn.val ≤ r.tableLength := by
  rw [← firstValue_mod_degree]
  exact (Nat.mod_le r.firstValue (degree d)).trans r.firstValue_le_tableLength

theorem secondReturn_le_tableLength : r.secondReturn.val ≤ r.tableLength := by
  rw [← secondValue_mod_degree]
  exact (Nat.mod_le r.secondValue (degree d)).trans r.secondValue_le_tableLength

end RowData

variable {v d : Nat}

theorem final_frame_eq (r : RowData v d) (output : List Bool) :
    frame12 r output = emittedWord .output (frame0 r output) r.finalValue := by
  funext tape
  cases tape <;> simp [frame0, emittedWord, frameContents]

/-! Direct input facts for the individual checked phase traces. -/

theorem cleanupSteps_le_tableLength (r : RowData v d) (output : List Bool) :
    cleanupSteps id (frame11 r output) ≤ 6 * (r.tableLength + 1) + 6 := by
  have h1 := r.firstVertex_le_tableLength
  have h2 := r.secondVertex_le_tableLength
  have h3 := r.firstReturn_le_tableLength
  have h4 := r.secondReturn_le_tableLength
  simp only [cleanupSteps, frame11_eq, id_eq, frameContents, encodeWord_length]
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineExpanderRow
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.clearRegister_position _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.clearRegister_register _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.fromBoolTapes_update _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.registerStates_symm_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.tableExecution_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.toBoolTapes_update _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.accumulatedVertices_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.caller_rowAfterState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.clearRegister_position _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.clearRegister_register _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.guardStates_symm_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.program_outer _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.program_row _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.rowAfterState_position _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.rowExecution_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt.transferLeft_tapes _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt.transferRight_tapes _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.generatedWords_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.priorVertices_full _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.priorVertices_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.vertexWords_drop_full _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.vertexWords_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Complete execution of one expander-table row

The actual finite program performs both stored-table lookups, splits their
results by its fixed degree, emits the resulting square/zigzag reverse index,
and clears its work tapes. Its transition bound is linear in the unary input
table length. The output accumulator and finite caller state are arbitrary.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords PCP.AlphabetTable

/-- The actual number of transitions, retaining both concrete lookup costs. -/
def rowSteps {v d : Nat} (r : RowData v d) (output : List Bool) : Nat :=
  1 + emitSteps r.inputVertex.val + (r.query1 + 2) +
    MachinePreservingLookupClean.steps (rotationWords r.oldTable) r.firstRow.val +
    (r.firstValue + 2) + 1 + emitSteps r.firstVertex.val + (r.query2 + 2) +
    MachinePreservingLookupClean.steps (rotationWords r.oldTable) r.secondRow.val +
    (r.secondValue + 2) + emitSteps r.secondVertex.val +
    (cleanupSteps id (frame11 r output) + 1)

section Execution

variable {v d : Nat} {ρ Λ : Type} [Fintype ρ]
    (positive : 0 < d) (r : RowData v d) (output : List Bool) (ambient : ρ)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : Tape => Bool) Λ (State ρ d))
    (code : ∀ l, target (labels l) = statement positive r.smallTable id labels exit l)

include code

/-- The complete execution follows the concrete program. The only code premise
places its instructions in a caller; every lookup is derived from `oldTable`. -/
theorem rowTraceAt :
    (advance (TM2.step target))^[rowSteps r output]
      (some ⟨some (labels .initialize_), divisionState positive ambient r.control0 none,
        frame0 r output⟩) =
      some ⟨exit, divisionState positive ambient r.control2 none,
        emittedWord .output (frame0 r output) r.finalValue⟩ := by
  let zero := MachineFixedDivMod.residue (degree d) (Nat.mul_pos positive positive) 0
  have h0 : (advance (TM2.step target))^[1]
      (some ⟨some (labels .initialize_), divisionState positive ambient r.control0 none,
        frame0 r output⟩) =
      some ⟨some (labels (.firstEmit (Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient r.control0 none, frame1 r output⟩ := by
    simpa only [Function.iterate_one, advance_some, divisionState, frame1] using
      initializeStepAt positive r.smallTable id Function.injective_id labels exit target code
        (frame0 r output) (divisionState positive ambient r.control0 none)
  have h1 := firstEmitTraceAt positive r.smallTable id Function.injective_id
    labels exit target code r.inputVertex.val (frame1 r output)
    (by simp) (by simp) ((ambient,r.control0),zero)
  change (advance (TM2.step target))^[emitSteps r.inputVertex.val]
      (some ⟨some (labels (.firstEmit (Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient r.control0 none, frame1 r output⟩) =
      some ⟨some (labels .firstReverse), divisionState positive ambient r.control0 none,
        frame2 r output⟩ at h1
  have h2 := reversePhaseTrace_unary false positive r.smallTable id Function.injective_id
    labels exit target code (frame2 r output) (((ambient,r.control0),zero),()) none
    r.query1 [] (by simp) (by simp)
  simp only [List.append_nil] at h2
  change (advance (TM2.step target))^[r.query1 + 2]
      (some ⟨some (labels .firstReverse), divisionState positive ambient r.control0 none,
        frame2 r output⟩) =
      some ⟨some (labels (.firstLookup (.run .copyFirst))),
        divisionState positive ambient r.control0 none, frame3 r output⟩ at h2
  have h3 := lookupPhaseTrace false positive r.smallTable id Function.injective_id
    labels exit target code (frame3 r output) r.oldTable
    (by simp) (by simp)
    (r.inputVertex, firstOffset r.control0) []
    (by simpa [frameContents, RowData.firstRow] using
      congrArg encodeWord r.query1_eq_firstRow)
    (by simp) (((ambient,r.control0),zero),()) none
  change (advance (TM2.step target))^[MachinePreservingLookupClean.steps
      (rotationWords r.oldTable) r.firstRow.val]
      (some ⟨some (labels (.firstLookup (.run .copyFirst))),
        divisionState positive ambient r.control0 none, frame3 r output⟩) =
      some ⟨some (labels .firstScan), divisionState positive ambient r.control0 none,
        frame4 r output⟩ at h3
  have h4 := firstDivisionTrace positive r.smallTable id Function.injective_id labels exit
    target code (frame4 r output) r.firstValue [] [] []
    (by simp) (by simp) (by simp)
    ambient r.control0 none
  rw [← r.firstReturn_eq_residue positive] at h4
  change (advance (TM2.step target))^[r.firstValue + 2]
      (some ⟨some (labels .firstScan), divisionState positive ambient r.control0 none,
        frame4 r output⟩) =
      some ⟨some (labels .clearQuery), divisionState positive ambient r.control1 none,
        frame5 r output⟩ at h4
  have h5 : (advance (TM2.step target))^[1]
      (some ⟨some (labels .clearQuery), divisionState positive ambient r.control1 none,
        frame5 r output⟩) =
      some ⟨some (labels (.secondEmit (Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient r.control1 none, frame6 r output⟩ := by
    simpa only [Function.iterate_one, advance_some, frame6] using
      clearQueryStepAt positive r.smallTable id Function.injective_id labels exit target code
        (frame5 r output) (divisionState positive ambient r.control1 none)
  have h6 := secondEmitTraceAt positive r.smallTable id Function.injective_id
    labels exit target code r.firstVertex.val (frame6 r output)
    (by simp) (by simp) ((ambient,r.control1),zero)
  change (advance (TM2.step target))^[emitSteps r.firstVertex.val]
      (some ⟨some (labels (.secondEmit (Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient r.control1 none, frame6 r output⟩) =
      some ⟨some (labels .secondReverse), divisionState positive ambient r.control1 none,
        frame7 r output⟩ at h6
  have h7 := reversePhaseTrace_unary true positive r.smallTable id Function.injective_id
    labels exit target code (frame7 r output) (((ambient,r.control1),zero),()) none
    r.query2 [] (by simp) (by simp)
  simp only [List.append_nil] at h7
  change (advance (TM2.step target))^[r.query2 + 2]
      (some ⟨some (labels .secondReverse), divisionState positive ambient r.control1 none,
        frame7 r output⟩) =
      some ⟨some (labels (.secondLookup (.run .copyFirst))),
        divisionState positive ambient r.control1 none, frame8 r output⟩ at h7
  have h8 := lookupPhaseTrace true positive r.smallTable id Function.injective_id
    labels exit target code (frame8 r output) r.oldTable
    (by simp) (by simp)
    (r.firstVertex, secondOffset r.control1) []
    (by simpa [frameContents, RowData.secondRow] using
      congrArg encodeWord r.query2_eq_secondRow)
    (by simp) (((ambient,r.control1),zero),()) none
  change (advance (TM2.step target))^[MachinePreservingLookupClean.steps
      (rotationWords r.oldTable) r.secondRow.val]
      (some ⟨some (labels (.secondLookup (.run .copyFirst))),
        divisionState positive ambient r.control1 none, frame8 r output⟩) =
      some ⟨some (labels .secondScan), divisionState positive ambient r.control1 none,
        frame9 r output⟩ at h8
  have h9 := secondDivisionTrace positive r.smallTable id Function.injective_id labels exit
    target code (frame9 r output) r.secondValue [] [] []
    (by simp) (by simp) (by simp)
    ambient r.control1 none
  rw [← r.secondReturn_eq_residue positive] at h9
  change (advance (TM2.step target))^[r.secondValue + 2]
      (some ⟨some (labels .secondScan), divisionState positive ambient r.control1 none,
        frame9 r output⟩) =
      some ⟨some (labels (.outputEmit (Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient r.control2 none, frame10 r output⟩ at h9
  have h10 := outputEmitTraceAt positive r.smallTable id Function.injective_id
    labels exit target code r.secondVertex.val (frame10 r output)
    (by simp) (by simp) ((ambient,r.control2),zero)
  change (advance (TM2.step target))^[emitSteps r.secondVertex.val]
      (some ⟨some (labels (.outputEmit (Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient r.control2 none, frame10 r output⟩) =
      some ⟨some (labels (.cleanup 0)), divisionState positive ambient r.control2 none,
        frame11 r output⟩ at h10
  have h11 := cleanupExitTraceAt positive r.smallTable id Function.injective_id
    labels exit target code (frame11 r output) (divisionState positive ambient r.control2 none)
  change (advance (TM2.step target))^[cleanupSteps id (frame11 r output) + 1]
      (some ⟨some (labels (.cleanup 0)), divisionState positive ambient r.control2 none,
        frame11 r output⟩) =
      some ⟨exit, divisionState positive ambient r.control2 none, frame12 r output⟩ at h11
  rw [final_frame_eq] at h11
  exact concatenate (concatenate (concatenate (concatenate (concatenate
    (concatenate (concatenate (concatenate (concatenate (concatenate
      (concatenate h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11

end Execution

theorem rowSteps_le {v d : Nat} (r : RowData v d) (output : List Bool) :
    rowSteps r output ≤ 80 * (r.tableLength + 1) := by
  have lookup1 := MachinePreservingLookupClean.steps_le (rotationWords r.oldTable)
    r.firstRow.val r.firstValue (rotationWords_getElem? r.oldTable r.firstRow)
  have lookup2 := MachinePreservingLookupClean.steps_le (rotationWords r.oldTable)
    r.secondRow.val r.secondValue (rotationWords_getElem? r.oldTable r.secondRow)
  have h0 := r.inputVertex_le_tableLength
  have h1 := r.query1_le_tableLength
  have h2 := r.firstValue_le_tableLength
  have h3 := r.firstVertex_le_tableLength
  have h4 := r.query2_le_tableLength
  have h5 := r.secondValue_le_tableLength
  have h6 := r.secondVertex_le_tableLength
  have clean := cleanupSteps_le_tableLength r output
  change _ ≤ 6 * r.tableLength + 4 at lookup1 lookup2
  simp only [rowSteps, emitSteps]
  omega

/-- The actual row program has a linear transition bound, with all temporary
tapes empty at return. The bound holds for every valid finite input table. -/
def rowInTimeAt {v d : Nat} {ρ Λ : Type} [Fintype ρ]
    (positive : 0 < d) (r : RowData v d) (output : List Bool) (ambient : ρ)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : Tape => Bool) Λ (State ρ d))
    (code : ∀ l, target (labels l) = statement positive r.smallTable id labels exit l) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels .initialize_), divisionState positive ambient r.control0 none,
        frame0 r output⟩
      (some ⟨exit, divisionState positive ambient r.control2 none,
        emittedWord .output (frame0 r output) r.finalValue⟩)
      (80 * (r.tableLength + 1)) where
  steps := rowSteps r output
  evals_in_steps := rowTraceAt positive r output ambient labels exit target code
  steps_le_m := rowSteps_le r output

/-- Specialization to the standalone finite row program. -/
def rowInTime {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (r : RowData v d) (output : List Bool) (ambient : ρ) :
    StateTransition.EvalsToInTime (TM2.step (program positive r.smallTable))
      ⟨some .initialize_, divisionState positive ambient r.control0 none, frame0 r output⟩
      (some ⟨none, divisionState positive ambient r.control2 none,
        emittedWord .output (frame0 r output) r.finalValue⟩)
      (80 * (r.tableLength + 1)) :=
  rowInTimeAt positive r output ambient id none (program positive r.smallTable) (fun _ => rfl)

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_ExpanderTableEnumeration
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_archive _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.boolView_outer _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.caller_initialState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.caller_normalizeState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.clearRegister_initialState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.clearRegister_register _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.program_outer _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.program_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.registerStates_symm_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.tableExecution_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamilyBounds.familyBudget_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamilyBounds.resizeSum_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.RowData.firstValue_div_degree _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.RowData.firstValue_mod_degree _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.RowData.secondValue_div_degree _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.RowData.secondValue_mod_degree _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionStates_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.program_firstEmit _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.program_outputEmit _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.program_secondEmit _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.accumulatedVertices_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.caller_boundaryState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.caller_prepareState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.caller_resetState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.caller_rowAfterState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.clearRegister_boundaryState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.clearRegister_register _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.guardStates_symm_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.prepareState_boundaryState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.program_outer _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.program_row _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.rowAfterState_position _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.rowExecution_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec.decodeWords_encodeWord _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter.counterTapes_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.overlay_accepts_expander _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.overlay_accepts_old _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_internal _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.actualRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Exact row enumeration and accumulator contents for an expander-table step

The outer loop enumerates original vertices, and the inner loop enumerates
cloud/port positions in increasing mixed-radix order. The resulting list is
the actual next table's stored rotation-word list. Prefix and reverse-encoding
identities describe data accumulated by a row loop; they assert no runtime.
-/

namespace UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration

open ExpanderTables ExpanderRowControl ExpanderTableWords
open UniqueGamesTheorem.Foundations.Complexity

variable {v d : Nat}

theorem vertexWords_drop_succ (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (position : Fin (rowFactor d)) :
    (vertexWords G H vertex).drop position.val =
      rowValue G H vertex position :: (vertexWords G H vertex).drop (position.val + 1) := by
  rw [List.drop_eq_getElem_cons (by simp)]
  simp [vertexWords]

theorem vertexWords_drop_last (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (position : Fin (rowFactor d))
    (last : position.val + 1 = rowFactor d) :
    (vertexWords G H vertex).drop position.val = [rowValue G H vertex position] := by
  rw [vertexWords_drop_succ, last, vertexWords_drop_full]

theorem priorVertices_succ (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (k : Nat) (hk : k < v) :
    priorVertices G H (k + 1) = priorVertices G H k ++ vertexWords G H ⟨k, hk⟩ := by
  unfold priorVertices
  rw [List.take_succ_eq_append_getElem (by simpa using hk), List.flatten_append]
  simp

theorem accumulate_eq (values : List Nat) (initial : List Bool) :
    accumulate values initial = (encodeWords values).reverse ++ initial := by
  induction values generalizing initial with
  | nil => simp [accumulate, encodeWords]
  | cons value values ih =>
      simpa only [accumulate, List.foldl_cons, encodeWords, List.reverse_append,
        List.append_assoc] using ih ((encodeWord value).reverse ++ initial)

theorem accumulate_append (first second : List Nat) (initial : List Bool) :
    accumulate (first ++ second) initial = accumulate second (accumulate first initial) := by
  simp only [accumulate, List.foldl_append]

theorem accumulate_generatedWords (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (initial : List Bool) :
    accumulate (generatedWords G H) initial =
      (encodeWords (rotationWords (step G H))).reverse ++ initial := by
  rw [accumulate_eq, generatedWords_eq_rotationWords]

theorem encode_generatedWords_length_le (G : Table v (degree d)) (H : Table (cloudSize d) d) :
    (encodeWords (generatedWords G H)).length ≤
      (v * rowFactor d) * (v * rowFactor d + 1) := by
  rw [generatedWords_eq_rotationWords, rowCount_eq]
  exact encode_rotationWords_length_le (step G H)

end UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineExpanderTableRows
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamilyBounds.familyBudget_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamilyBounds.resizeSum_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.accumulatedVertices_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.clearRegister_position _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.clearRegister_register _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.overlay_accepts_expander _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.overlay_accepts_old _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_internal _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.actualRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual execution of all expander-table positions for one vertex

The inner loop calls the complete row machine once per fixed cloud/port position.
The returned state and the successful machine execution are constructed together.
Neither a row execution nor an inner-loop execution is a caller premise.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

theorem tableRowData_finalValue {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (position : Position d) :
    (tableRowData G H vertex position).finalValue = rowValue G H vertex position := rfl

theorem tableRowData_frame0 {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (position : Position d) (output : List Bool) :
    MachineExpanderRow.frame0 (tableRowData G H vertex position) output =
      rowTapes vertex.val (encodeWords (rotationWords G)) output := by
  funext tape
  cases tape <;> rfl

theorem tableRowData_finalFrame {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (position : Position d) (output : List Bool) :
    MachineExpanderRow.emittedWord .output
      (MachineExpanderRow.frame0 (tableRowData G H vertex position) output)
      (tableRowData G H vertex position).finalValue =
      rowTapes vertex.val (encodeWords (rotationWords G))
        ((encodeWord (rowValue G H vertex position)).reverse ++ output) := by
  rw [tableRowData_frame0, tableRowData_finalValue]
  funext tape
  cases tape <;> simp [MachineExpanderRow.emittedWord, rowTapes]

variable {ρ : Type} [Fintype ρ] {v d : Nat}

/-- Preparation and one actual embedded row call, with the two extra tapes
retained. The row value is computed from the actual old and small tables. -/
def preparedRowInTime (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d)
    (remaining : Nat) (output countSuffix result : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.inr .prepareRow), state,
        boundaryTapes vertex.val remaining (encodeWords (rotationWords G)) output countSuffix result⟩
      (some ⟨some (.inr .afterRow), rowAfterState positive G H vertex state,
        boundaryTapes vertex.val remaining (encodeWords (rotationWords G))
          ((encodeWord (rowValue G H vertex state.2)).reverse ++ output) countSuffix result⟩)
      (1 + 80 * ((encodeWords (rotationWords G)).length + 1)) := by
  have raw := rowExecution positive H state.2 (extraTapes remaining countSuffix result)
    (MachineExpanderRow.rowInTime positive (tableRowData G H vertex state.2) output (caller state))
  have run : StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.inl .initialize_), prepareState positive H state,
        boundaryTapes vertex.val remaining (encodeWords (rotationWords G)) output countSuffix result⟩
      (some ⟨some (.inr .afterRow), rowAfterState positive G H vertex state,
        boundaryTapes vertex.val remaining (encodeWords (rotationWords G))
          ((encodeWord (rowValue G H vertex state.2)).reverse ++ output) countSuffix result⟩)
      (80 * ((encodeWords (rotationWords G)).length + 1)) := by
    rw [tableRowData_finalFrame, tableRowData_frame0] at raw
    simpa only [MachineEmbedding.configuration, MachineEmbedding.label, rowReturn,
      prepareState, boundaryState, rowAfterState, boundaryTapes,
      MachineExpanderRow.RowData.tableLength, MachineExpanderRow.RowData.control0,
      tableRowData, MachineExpanderRow.rowData] using raw
  exact sequence
    (singleStep _ _ _ (prepareRowStep positive H
      (boundaryTapes vertex.val remaining (encodeWords (rotationWords G)) output countSuffix result)
      state)) run

/-- A successful suffix of the finite position loop, returning actual finite
state together with the execution certificate and its preserved caller. -/
structure VertexSuffixRun (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d)
    (remaining : Nat) (output countSuffix result : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  position_zero : finalState.2 = zeroPosition positive
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H))
    ⟨some (.inr .prepareRow), state,
      boundaryTapes vertex.val remaining (encodeWords (rotationWords G)) output countSuffix result⟩
    (some ⟨some (.inr .vertexGuard), finalState,
      boundaryTapes (vertex.val + 1) remaining (encodeWords (rotationWords G))
        (accumulate ((vertexWords G H vertex).drop state.2.val) output) countSuffix result⟩)
    ((rowFactor d - state.2.val) * (80 * ((encodeWords (rotationWords G)).length + 1) + 2))

def suffixRun_aux (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (remaining : Nat)
    (countSuffix result : List Bool) (n : Nat) :
    (state : State ρ d) → state.2.val + n = rowFactor d → (output : List Bool) →
      VertexSuffixRun positive G H vertex state remaining output countSuffix result := by
  induction n with
  | zero =>
      intro state count output
      have hp := state.2.isLt
      exact False.elim (by omega)
  | succ n ih =>
      intro state count output
      let after := rowAfterState positive G H vertex state
      let nextOutput := (encodeWord (rowValue G H vertex state.2)).reverse ++ output
      have row := preparedRowInTime positive G H vertex state remaining output countSuffix result
      by_cases last : n = 0
      · have hp : state.2.val + 1 = rowFactor d := by omega
        have finish := singleStep _ _ _ (afterRow_last_boundaryStep positive H vertex.val remaining
          (encodeWords (rotationWords G)) nextOutput countSuffix result after (by
            change ¬ state.2.val + 1 < rowFactor d
            omega))
        refine ⟨resetPositionState positive after, ?_, rfl, ?_⟩
        · rfl
        · have all := sequence row finish
          have words : accumulate ((vertexWords G H vertex).drop state.2.val) output =
              nextOutput := by
            rw [vertexWords_drop_last G H vertex state.2 hp]
            rfl
          have budget : rowFactor d - state.2.val = 1 := by omega
          rw [words, budget, Nat.one_mul]
          exact widen all (by omega)
      · have more : state.2.val + 1 < rowFactor d := by omega
        let next := advancePositionState positive after
        have nextPositionValue : next.2.val = state.2.val + 1 :=
          nextPosition_val_of_lt positive state.2 more
        have nextCount : next.2.val + n = rowFactor d := by omega
        let tail := ih next nextCount nextOutput
        have advance := singleStep _ _ _ (afterRow_moreStep positive H
          (boundaryTapes vertex.val remaining (encodeWords (rotationWords G))
            nextOutput countSuffix result) after more)
        have all := sequence (sequence row advance) tail.execution
        refine ⟨tail.finalState, ?_, tail.position_zero, ?_⟩
        · exact tail.caller_preserved
        · have words : accumulate ((vertexWords G H vertex).drop state.2.val) output =
              accumulate ((vertexWords G H vertex).drop next.2.val) nextOutput := by
            rw [vertexWords_drop_succ G H vertex state.2, nextPositionValue]
            rfl
          rw [words]
          apply widen all
          have hcount : rowFactor d - state.2.val = n + 1 := by omega
          have hnext : rowFactor d - next.2.val = n := by omega
          rw [hcount, hnext, Nat.add_mul, Nat.one_mul]
          omega

def suffixInTime (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d)
    (remaining : Nat) (output countSuffix result : List Bool) :
    VertexSuffixRun positive G H vertex state remaining output countSuffix result :=
  suffixRun_aux positive G H vertex remaining countSuffix result
    (rowFactor d - state.2.val) state (by have h := state.2.isLt; omega) output

/-- The complete inner loop for one vertex, starting at position zero. -/
structure VertexRun (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d)
    (remaining : Nat) (output countSuffix result : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  position_zero : finalState.2 = zeroPosition positive
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H))
    ⟨some (.inr .prepareRow), state,
      boundaryTapes vertex.val remaining (encodeWords (rotationWords G)) output countSuffix result⟩
    (some ⟨some (.inr .vertexGuard), finalState,
      boundaryTapes (vertex.val + 1) remaining (encodeWords (rotationWords G))
        (accumulate (vertexWords G H vertex) output) countSuffix result⟩)
    (rowFactor d * (80 * ((encodeWords (rotationWords G)).length + 1) + 2))

def vertexInTime (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d)
    (position : state.2 = zeroPosition positive)
    (remaining : Nat) (output countSuffix result : List Bool) :
    VertexRun positive G H vertex state remaining output countSuffix result := by
  let run := suffixInTime positive G H vertex state remaining output countSuffix result
  refine ⟨run.finalState, run.caller_preserved, run.position_zero, ?_⟩
  have zero : state.2.val = 0 := congrArg Fin.val position
  simpa only [zero, List.drop_zero, Nat.sub_zero] using run.execution

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineExpanderTableLoop
attribute [-simp] _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamilyBounds.familyBudget_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamilyBounds.resizeSum_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.clearRegister_register _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.overlay_accepts_expander _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.overlay_accepts_old _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_internal _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.actualRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual outer vertex iteration for expander tables

The invariant is the reversed unary encoding of all completed vertices. Each
positive unary guard invokes the proved complete fixed-position row loop;
the zero guard enters the actual output-reversal phase. No execution premise
is supplied by the caller.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

theorem accumulatedVertices_succ {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (current : Nat) (valid : current < v) :
    accumulatedVertices G H (current + 1) =
      accumulate (vertexWords G H ⟨current, valid⟩) (accumulatedVertices G H current) := by
  simp only [accumulatedVertices, priorVertices_succ G H current valid, accumulate_append]

theorem accumulatedVertices_full {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) : accumulatedVertices G H v =
      (encodeWords (rotationWords (step G H))).reverse := by
  simp [accumulatedVertices, accumulate_generatedWords]

def vertexBodyBudget {v d : Nat} (G : Table v (degree d)) : Nat :=
  rowFactor d * (80 * ((oldTableWord G).length + 1) + 2)

def vertexLoopBudget {v d : Nat} (G : Table v (degree d)) (remaining : Nat) : Nat :=
  remaining * (vertexBodyBudget G + 1) + 1

def vertexLoopTapes {v d : Nat} (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (current remaining : Nat) (suffix : List Bool) : ∀ tape, List (Alphabet tape) :=
  boundaryTapes current remaining (oldTableWord G) (accumulatedVertices G H current) suffix []

structure VertexLoopRun {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (current remaining : Nat) (state : State ρ d) (suffix : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  position_zero : finalState.2 = zeroPosition positive
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H))
    ⟨some (.inr .vertexGuard), state, vertexLoopTapes G H current remaining suffix⟩
    (some ⟨some (.inr .reverseOutput), finalState, vertexLoopTapes G H v 0 suffix⟩)
    (vertexLoopBudget G remaining)

/-- Execute every remaining vertex in the common finite table program. -/
def vertexLoopInTime {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (current remaining : Nat) (state : State ρ d) (suffix : List Bool)
    (count : current + remaining = v) (position : state.2 = zeroPosition positive) :
    VertexLoopRun positive G H current remaining state suffix := by
  induction remaining generalizing current state with
  | zero =>
      have hc : current = v := by omega
      subst current
      refine ⟨clearRegister state, caller_clearRegister state, ?_, ?_⟩
      · simpa only [clearRegister] using position
      · simpa only [vertexLoopBudget, Nat.zero_mul, Nat.zero_add, vertexLoopTapes] using
          boundarySingleStep _ _ _ (vertexGuard_boundary_zeroStep positive H v (oldTableWord G)
            (accumulatedVertices G H v) suffix [] state)
  | succ remaining ih =>
      have valid : current < v := by omega
      let vertex : Fin v := ⟨current, valid⟩
      let body := vertexInTime positive G H vertex (clearRegister state)
        (by simpa only [clearRegister] using position) remaining
        (accumulatedVertices G H current) suffix []
      have nextCount : current + 1 + remaining = v := by omega
      let rest := ih (current + 1) body.finalState nextCount body.position_zero
      have output_eq : accumulate (vertexWords G H vertex)
          (accumulatedVertices G H current) = accumulatedVertices G H (current + 1) :=
        (accumulatedVertices_succ G H current valid).symm
      let guard := boundarySingleStep _ _ _
        (vertexGuard_boundary_succStep positive H current remaining (oldTableWord G)
          (accumulatedVertices G H current) suffix [] state)
      have bodyRun : StateTransition.EvalsToInTime (TM2.step (program positive H))
          ⟨some (.inr .prepareRow), clearRegister state,
            boundaryTapes current remaining (oldTableWord G)
              (accumulatedVertices G H current) suffix []⟩
          (some ⟨some (.inr .vertexGuard), body.finalState,
            vertexLoopTapes G H (current + 1) remaining suffix⟩)
          (vertexBodyBudget G) := by
        simpa only [vertexLoopTapes, vertexBodyBudget, oldTableWord, output_eq] using body.execution
      let first := StateTransition.EvalsToInTime.trans (TM2.step (program positive H))
        _ _ _ _ _ guard bodyRun
      let all := StateTransition.EvalsToInTime.trans (TM2.step (program positive H))
        _ _ _ _ _ first rest.execution
      refine ⟨rest.finalState, ?_, rest.position_zero, ?_⟩
      · exact rest.caller_preserved.trans
          (body.caller_preserved.trans (caller_clearRegister state))
      · refine { toEvalsTo := all.toEvalsTo, steps_le_m := ?_ }
        have bound := all.steps_le_m
        simp only [vertexLoopBudget, Nat.succ_mul] at bound ⊢
        omega

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineExpanderTableReverse
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.cleanupTapes_dirty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.cleanupTapes_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.cleanupTapes_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.cleanupTapes_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_emitScratch _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_emitScratch _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_lookupRestore _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_lookupWork _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_emitScratch _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_lookupRestore _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_lookupWork _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.program_firstEmit _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.program_outputEmit _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.program_secondEmit _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.caller_rowAfterState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.rowAfterState_position _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.dirtyTape_five _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.dirtyTape_four _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.dirtyTape_one _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.dirtyTape_three _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.dirtyTape_two _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.dirtyTape_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

open Turing
open MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} {d : Nat}

@[simp] theorem clearRegister_idempotent (state : State ρ d) :
    clearRegister (clearRegister state) = clearRegister state := rfl

theorem boundaryTapes_reverse_update (vertex remaining : Nat)
    (oldTable output countSuffix result nextOutput nextResult : List Bool) :
    Function.update
      (Function.update (boundaryTapes vertex remaining oldTable output countSuffix result)
        (.inl .output) nextOutput)
      (.inr .result) nextResult =
      boundaryTapes vertex remaining oldTable nextOutput countSuffix nextResult := by
  funext tape
  rcases tape with row | extra
  · cases row <;>
      simp [boundaryTapes, rowTapes, MachineEmbedding.tapes, Function.update]
  · cases extra <;>
      simp [boundaryTapes, extraTapes, MachineEmbedding.tapes, Function.update]

variable [Fintype ρ]

/-- Exact execution of the entire final reverse loop, including its empty
test. No reversal-execution hypothesis is assumed. -/
theorem reverseOutputTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    (advance (TM2.step (program positive H)))^[output.length + 1]
      (some ⟨some (.inr .reverseOutput), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩) =
      some ⟨some (.inr .done), clearRegister state,
        boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result)⟩ := by
  induction output generalizing result state with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, advance_some,
        List.reverse_nil, List.nil_append] using
        reverseOutput_nilStep positive H
          (boundaryTapes vertex remaining oldTable [] countSuffix result) state rfl
  | cons symbol output ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [reverseOutput_consStep positive H
        (boundaryTapes vertex remaining oldTable (symbol :: output) countSuffix result)
        state symbol output rfl]
      change (advance (TM2.step (program positive H)))^[output.length + 1]
        (some ⟨some (.inr .reverseOutput), ((state.1.1, some symbol), state.2),
          Function.update
            (Function.update
              (boundaryTapes vertex remaining oldTable (symbol :: output) countSuffix result)
              (.inl .output) output)
            (.inr .result) (symbol :: result)⟩) = _
      rw [boundaryTapes_reverse_update]
      simpa only [clearRegister, List.reverse_cons, List.append_assoc,
        List.singleton_append] using
        ih (symbol :: result) ((state.1.1, some symbol), state.2)

/-- The actual `done` statement halts one transition after reversal completes. -/
theorem reverseOutputHaltTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    (advance (TM2.step (program positive H)))^[output.length + 2]
      (some ⟨some (.inr .reverseOutput), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩) =
      some ⟨none, clearRegister state,
        boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result)⟩ := by
  rw [show output.length + 2 = (output.length + 1) + 1 by omega,
    Function.iterate_succ_apply',
    reverseOutputTrace positive H vertex remaining oldTable output countSuffix result state]
  exact doneStep positive H
    (boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result))
    (clearRegister state)

def reverseOutputHaltInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.inr .reverseOutput), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩
      (some ⟨none, clearRegister state,
        boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result)⟩)
      (output.length + 2) where
  steps := output.length + 2
  evals_in_steps := reverseOutputHaltTrace positive H vertex remaining oldTable output countSuffix result state
  steps_le_m := Nat.le_refl _

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineExpanderTable
attribute [-simp] _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamilyBounds.familyBudget_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamilyBounds.resizeSum_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.overlay_accepts_expander _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.overlay_accepts_old _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_internal _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.actualRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Complete finite machine execution for the next expander table

The initialized old table and unary vertex count are consumed by one actual
finite program. The machine writes precisely the complete square/zigzag
rotation table, preserving its old table and all promised framing. The bound
is quadratic in the unary old-table length for each fixed small graph.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

def completeBudget {v d : Nat} (G : Table v (degree d)) (H : Table (cloudSize d) d) : Nat :=
  1 + vertexLoopBudget G v + ((encodeWords (rotationWords (step G H))).length + 2)

theorem vertices_le_word_length {v d : Nat} (positive : 0 < d)
    (G : Table v (degree d)) : v ≤ (oldTableWord G).length := by
  have hq : 1 ≤ degree d := Nat.mul_pos positive positive
  have hv : v ≤ v * degree d := by simpa using Nat.mul_le_mul_left v hq
  have hr : v * degree d ≤ (oldTableWord G).length := by
    simp only [oldTableWord, encodeWords_length, rotationWords_length]
    omega
  exact hv.trans hr

/-- All actual loop, row, and final reversal costs are bounded quadratically. -/
theorem completeBudget_le {v d : Nat} (positive : 0 < d)
    (G : Table v (degree d)) (H : Table (cloudSize d) d) :
    completeBudget G H ≤ (timePolynomial d).eval (oldTableWord G).length := by
  let L := (oldTableWord G).length
  let M := rowFactor d
  have vBound : v ≤ L + 1 := (vertices_le_word_length positive G).trans (Nat.le_succ L)
  have emitBound : 80 * (L + 1) + 2 ≤ 82 * (L + 1) := by omega
  have bodyBound : vertexBodyBudget G + 1 ≤ (82 * M + 1) * (L + 1) := by
    have mulBound := Nat.mul_le_mul_left M emitBound
    change M * (80 * (L + 1) + 2) + 1 ≤ _
    nlinarith
  have iterations := Nat.mul_le_mul vBound bodyBound
  have loopBound : v * (vertexBodyBudget G + 1) ≤ (82 * M + 1) * (L + 1)^2 := by
    calc
      _ ≤ (L + 1) * ((82 * M + 1) * (L + 1)) := iterations
      _ = _ := by ring
  have rowBound : v * M ≤ M * (L + 1) := by
    simpa only [Nat.mul_comm v M] using Nat.mul_le_mul_left M vBound
  have rowSuccBound : v * M + 1 ≤ (M + 1) * (L + 1) := by nlinarith
  have productBound := Nat.mul_le_mul rowBound rowSuccBound
  have lengthBound : (encodeWords (rotationWords (step G H))).length ≤
      M * (M + 1) * (L + 1)^2 := by
    calc
      _ ≤ (v * M) * (v * M + 1) := by
        simpa only [generatedWords_eq_rotationWords] using encode_generatedWords_length_le G H
      _ ≤ (M * (L + 1)) * ((M + 1) * (L + 1)) := productBound
      _ = _ := by ring
  have oneBound : 1 ≤ (L + 1)^2 := by nlinarith
  have combined := Nat.add_le_add loopBound lengthBound
  simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  change completeBudget G H ≤ (M * (M + 1) + 82 * M + 5) * (L + 1)^2
  unfold completeBudget vertexLoopBudget
  nlinarith

structure TableRun {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (state : State ρ d) (suffix : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  position_zero : finalState.2 = zeroPosition positive
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H))
    ⟨some (.inr .initialize_), state, initialTapes v (oldTableWord G) suffix⟩
    (some ⟨none, finalState,
      finalTapes v (oldTableWord G) (encodeWords (rotationWords (step G H))) suffix⟩)
    ((timePolynomial d).eval (oldTableWord G).length)

def initializeInTime {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (state : State ρ d) (suffix : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.inr .initialize_), state, initialTapes v (oldTableWord G) suffix⟩
      (some ⟨some (.inr .vertexGuard), initialState positive H (caller state),
        vertexLoopTapes G H 0 v suffix⟩) 1 where
  steps := 1
  evals_in_steps := by
    change TM2.step (program (ρ := ρ) positive H)
      ⟨some (.inr .initialize_), state, initialTapes v (oldTableWord G) suffix⟩ =
      some ⟨some (.inr .vertexGuard), initialState positive H (caller state),
        vertexLoopTapes G H 0 v suffix⟩
    simpa only [vertexLoopTapes, accumulatedVertices_zero] using
      initialize_boundaryStep positive H v (oldTableWord G) suffix state
  steps_le_m := Nat.le_refl _

/-- Construct the entire table execution from its actual initialized inputs.
No row trace, loop trace, or abstract computational witness is a hypothesis. -/
def tableInTime {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (state : State ρ d) (suffix : List Bool) : TableRun positive G H state suffix := by
  let loop := vertexLoopInTime positive G H 0 v
    (initialState positive H (caller state)) suffix (by omega) rfl
  let initialRun := initializeInTime positive G H state suffix
  have finish : StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.inr .reverseOutput), loop.finalState, vertexLoopTapes G H v 0 suffix⟩
      (some ⟨none, clearRegister loop.finalState,
        finalTapes v (oldTableWord G) (encodeWords (rotationWords (step G H))) suffix⟩)
      ((encodeWords (rotationWords (step G H))).length + 2) := by
    simpa only [vertexLoopTapes, finalTapes, accumulatedVertices_full, List.reverse_reverse,
      List.append_nil, List.length_reverse] using
      reverseOutputHaltInTime positive H v 0 (oldTableWord G)
        (accumulatedVertices G H v) suffix [] loop.finalState
  let first := StateTransition.EvalsToInTime.trans (TM2.step (program positive H))
    _ _ _ _ _ initialRun loop.execution
  let all := StateTransition.EvalsToInTime.trans (TM2.step (program positive H))
    _ _ _ _ _ first finish
  refine ⟨clearRegister loop.finalState, ?_, ?_, ?_⟩
  · exact (caller_clearRegister loop.finalState).trans loop.caller_preserved
  · simpa only [clearRegister] using loop.position_zero
  · refine { toEvalsTo := all.toEvalsTo, steps_le_m := ?_ }
    have bound := all.steps_le_m
    have polynomialBound := completeBudget_le positive G H
    unfold completeBudget at polynomialBound
    omega

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineExpanderFamilyBoundsLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.familyView_left _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.overlay_accepts_expander _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.overlay_accepts_old _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_internal _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.actualRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
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

def resizeCoefficient (d : Nat) : Nat :=
  MachineExpanderTable.timeCoefficient d * (degree d + 1) ^ 4 +
    3 * (degree d + 1) ^ 2 + 21

/-- The complete unary encoding, including every word delimiter, is counted. -/
theorem wordLength_add_one_le {v q N : Nat} (G : Table v q) (hv : v ≤ N) :
    (encodeWords (rotationWords G)).length + 1 ≤ (q + 1)^2 * (N + 1)^2 := by
  have hlength := encode_rotationWords_length_le G
  have hrow : v * q + 1 ≤ (q + 1) * (N + 1) := by
    have h := Nat.mul_le_mul_right q hv
    nlinarith
  calc
    _ ≤ (v * q + 1)^2 := by nlinarith
    _ ≤ ((q + 1) * (N + 1))^2 := Nat.pow_le_pow_left hrow 2
    _ = _ := by ring

theorem resizeCost_le {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (N : Nat) (hv : v ≤ N)
    (hnext : v * cloudSize d ≤ N) :
    resizeCost G H ≤ resizeCoefficient d * (N + 1)^4 := by
  let oldL := (MachineExpanderTable.oldTableWord G).length
  let newL := (encodeWords (rotationWords (step G H))).length
  have oldBound : oldL + 1 ≤ (degree d + 1)^2 * (N + 1)^2 :=
    wordLength_add_one_le G hv
  have newBound : newL + 1 ≤ (degree d + 1)^2 * (N + 1)^2 :=
    wordLength_add_one_le (step G H) hnext
  have timeBound : (MachineExpanderTable.timePolynomial d).eval oldL ≤
      MachineExpanderTable.timeCoefficient d * (degree d + 1)^4 * (N + 1)^4 := by
    simp only [MachineExpanderTable.timePolynomial, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one]
    calc
      _ ≤ MachineExpanderTable.timeCoefficient d *
          ((degree d + 1)^2 * (N + 1)^2)^2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left oldBound 2)
      _ = _ := by ring
  have pow24 : (N + 1)^2 ≤ (N + 1)^4 :=
    Nat.pow_le_pow_right (Nat.succ_pos N) (by decide)
  have overheadBound : oldL + 2 * newL ≤
      3 * (degree d + 1)^2 * (N + 1)^4 := by
    have h := Nat.mul_le_mul_left ((degree d + 1)^2) pow24
    calc
      _ ≤ 3 * ((degree d + 1)^2 * (N + 1)^2) := by omega
      _ ≤ 3 * ((degree d + 1)^2 * (N + 1)^4) := Nat.mul_le_mul_left 3 h
      _ = _ := by ring
  have npow : N + 1 ≤ (N + 1)^4 := by
    simpa only [pow_one] using
      Nat.pow_le_pow_right (Nat.succ_pos N) (show 1 ≤ 4 by decide)
  have linearBound : 6 * v + 15 ≤ 21 * (N + 1)^4 := by omega
  change (MachineExpanderTable.timePolynomial d).eval oldL + 6 * v + oldL +
    2 * newL + 15 ≤ _
  unfold resizeCoefficient
  nlinarith only [timeBound, overheadBound, linearBound]

theorem resizeSum_succ {d : Nat} (H : Table (cloudSize d) d) (level : Nat) :
    resizeSum H (level + 1) = resizeSum H level + resizeCost (family H level) H := by
  simp only [resizeSum, Finset.sum_range_succ]

theorem resizeSum_le {d : Nat} (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (level : Nat) :
    resizeSum H level ≤ resizeCoefficient d * (vertexCount (degree d) level + 1)^5 := by
  let N := vertexCount (degree d) level
  have positive : 0 < degree d := by
    have h : 1 < degree d * degree d := growth
    nlinarith
  have hmono := vertexCount_monotone positive
  have hlevel : level ≤ N := level_le_vertexCount growth level
  have eachBound : ∀ i ∈ Finset.range level,
      resizeCost (family H i) H ≤ resizeCoefficient d * (N + 1)^4 := by
    intro i hi
    have hi' : i < level := Finset.mem_range.mp hi
    apply resizeCost_le (family H i) H N
    · exact hmono (by omega)
    · exact hmono (show i + 1 ≤ level by omega)
  have sumBound : resizeSum H level ≤ level * (resizeCoefficient d * (N + 1)^4) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range level, resizeCoefficient d * (N + 1)^4 :=
        Finset.sum_le_sum eachBound
      _ = _ := by simp
  calc
    _ ≤ level * (resizeCoefficient d * (N + 1)^4) := sumBound
    _ ≤ (N + 1) * (resizeCoefficient d * (N + 1)^4) :=
      Nat.mul_le_mul_right _ (hlevel.trans (Nat.le_succ N))
    _ = _ := by ring

/-- All actual resize costs plus the counted-loop overhead. -/
theorem familyBudget_le {d : Nat} (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (level : Nat) :
    familyBudget H level ≤
      (resizeCoefficient d + 4) * (vertexCount (degree d) level + 1)^5 := by
  have hsum := resizeSum_le H growth level
  have hlevel := level_le_vertexCount growth level
  have hpow : vertexCount (degree d) level + 1 ≤
      (vertexCount (degree d) level + 1)^5 := by
    simpa only [pow_one] using Nat.pow_le_pow_right
      (Nat.succ_pos (vertexCount (degree d) level)) (show 1 ≤ 5 by decide)
  have overhead : level + 3 ≤ 4 * (vertexCount (degree d) level + 1)^5 := by omega
  unfold familyBudget
  nlinarith only [hsum, overhead]

theorem paddedSize_le_succ_input (k : Nat) :
    PCP.PreprocessingLevels.paddedSize k ≤ PCP.ExpanderFamily.growth * (k + 1) := by
  by_cases hk : k = 0
  · subst k
    have h := PCP.ExpanderFamily.growth_gt_one
    simp only [PCP.PreprocessingLevels.paddedSize_zero, Nat.zero_add, Nat.mul_one]
    omega
  · exact (PCP.PreprocessingLevels.paddedSize_bounds (Nat.pos_of_ne_zero hk)).2.trans
      (Nat.mul_le_mul_left _ (Nat.le_succ k))

def inputCoefficient : Nat :=
  (resizeCoefficient PCP.Expanders.baseDegree + 4) * (PCP.ExpanderFamily.growth + 1)^5

/-- For the fixed base graph, the bounded padding level has a polynomial cost
in the requested unary size, including size zero. -/
theorem familyBudget_at_boundedLevel_le
    (H : Table (cloudSize PCP.Expanders.baseDegree) PCP.Expanders.baseDegree) (k : Nat) :
    familyBudget H (PCP.PreprocessingLevels.boundedLevel k) ≤ inputCoefficient * (k + 1)^5 := by
  have hg : cloudSize PCP.Expanders.baseDegree = PCP.ExpanderFamily.growth := by
    unfold cloudSize degree PCP.ExpanderFamily.growth
    ring
  have growth : 1 < cloudSize PCP.Expanders.baseDegree := by
    rw [hg]
    exact PCP.ExpanderFamily.growth_gt_one
  have bound := familyBudget_le H growth (PCP.PreprocessingLevels.boundedLevel k)
  rw [PCP.PreprocessingLevels.table_vertexCount_eq_paddedSize] at bound
  have sizeBound : PCP.PreprocessingLevels.paddedSize k + 1 ≤
      (PCP.ExpanderFamily.growth + 1) * (k + 1) := by
    have h := paddedSize_le_succ_input k
    nlinarith
  calc
    _ ≤ (resizeCoefficient PCP.Expanders.baseDegree + 4) *
        (PCP.PreprocessingLevels.paddedSize k + 1)^5 := bound
    _ ≤ (resizeCoefficient PCP.Expanders.baseDegree + 4) *
        ((PCP.ExpanderFamily.growth + 1) * (k + 1))^5 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left sizeBound 5)
    _ = _ := by unfold inputCoefficient; ring

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamilyBounds

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

section

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

theorem boundaryTapes_eq_cycleTapes (remaining current : Nat) (word suffix : List Bool) :
    boundaryTapes remaining current word suffix =
      cycleTapes remaining word (encodeWord current) [] [] [] suffix := by
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> rfl
  · cases tape <;> rfl

def copyFrame (remaining current : Nat) (word suffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  MachineEmbedding.tapes (MachineExpanderTable.initialTapes current word [])
    (extraFrame remaining current suffix)

def returnFrame (remaining current : Nat) (oldWord newWord suffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  MachineEmbedding.tapes (MachineExpanderTable.finalTapes current oldWord newWord [])
    (extraFrame remaining current suffix)

def installedFrame (remaining current : Nat) (newWord suffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  cycleTapes remaining newWord [] (encodeWord current) (encodeWord 0) [] suffix

def multipliedFrame (d remaining current : Nat) (newWord suffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  cycleTapes remaining newWord (encodeWord (cloudSize d * current))
    (encodeWord current) (encodeWord 0) [] suffix

theorem copyFrame_eq_cycleTapes (remaining current : Nat) (word suffix : List Bool) :
    copyFrame remaining current word suffix =
      cycleTapes remaining word (encodeWord current) [] (encodeWord current) [] suffix := by
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> simp [copyFrame, MachineEmbedding.tapes,
        MachineExpanderTable.initialTapes, MachineExpanderTable.extraTapes,
        cycleTapes, fromBoolTapes, boolWord, cycleWords]
  · cases tape <;> rfl

theorem returnFrame_eq_cycleTapes (remaining current : Nat)
    (oldWord newWord suffix : List Bool) :
    returnFrame remaining current oldWord newWord suffix =
      cycleTapes remaining oldWord (encodeWord current) (encodeWord current)
        (encodeWord 0) newWord suffix := by
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> simp [returnFrame, MachineEmbedding.tapes,
        MachineExpanderTable.finalTapes, MachineExpanderTable.boundaryTapes,
        MachineExpanderTable.extraTapes, cycleTapes, fromBoolTapes, boolWord, cycleWords]
  · cases tape <;> rfl

theorem copyFrame_eq_update (remaining current : Nat) (word suffix : List Bool) :
    Function.update (boundaryTapes remaining current word suffix)
      vertexCountTape (encodeWord current) = copyFrame remaining current word suffix := by
  rw [boundaryTapes_eq_cycleTapes, copyFrame_eq_cycleTapes]
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> rfl
  · cases tape <;> rfl

theorem multipliedFrame_eq_update (d remaining current : Nat) (word suffix : List Bool) :
    Function.update (installedFrame remaining current word suffix)
      (.inr .currentSize) (encodeWord (cloudSize d * current)) =
      multipliedFrame d remaining current word suffix := by
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> rfl
  · cases tape <;> rfl

end

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineExpanderFamilyBounds

theorem installed_returnFrame (remaining current : Nat) (oldWord newWord suffix : List Bool) :
    fromBoolTapes (installedTapes (toBoolTapes (returnFrame remaining current oldWord newWord suffix))
      newWord) = installedFrame remaining current newWord suffix := by
  rw [returnFrame_eq_cycleTapes, toBool_cycleTapes]
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> rfl
  · cases tape <;> rfl

theorem cleaned_multipliedFrame (d remaining current : Nat) (newWord suffix : List Bool) :
    fromBoolTapes (cleanedCounterTapes
      (toBoolTapes (multipliedFrame d remaining current newWord suffix))) =
      boundaryTapes remaining (current * cloudSize d) newWord suffix := by
  rw [boundaryTapes_eq_cycleTapes]
  unfold multipliedFrame
  rw [toBool_cycleTapes]
  have multiply : cloudSize d * current = current * cloudSize d := Nat.mul_comm _ _
  rw [multiply]
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> rfl
  · cases tape <;> rfl

structure ResizeRun {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (G : Table v (degree d)) (remaining : Nat) (state : State ρ d) (suffix : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
    ⟨some (.inr (.affine .copyCount .seed)), state,
      boundaryTapes remaining v (MachineExpanderTable.oldTableWord G) suffix⟩
    (some ⟨some (.inr .levelGuard), finalState,
      boundaryTapes remaining (v * cloudSize d)
        (encodeWords (rotationWords (step G H))) suffix⟩)
    (resizeCost G H)

/-- The resize certificate is built from actual primitive and table executions;
its caller supplies no phase trace or computational hypothesis. -/
noncomputable def resizeInTime {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (G : Table v (degree d)) (remaining : Nat) (state : State ρ d) (suffix : List Bool) :
    ResizeRun positive H growth G remaining state suffix := by
  let oldWord := MachineExpanderTable.oldTableWord G
  let newWord := encodeWords (rotationWords (step G H))
  have copy := copyCountInTime positive H growth
    (boundaryTapes remaining v oldWord suffix) v rfl rfl rfl state
  rw [copyFrame_eq_update] at copy
  let called := MachineExpanderTable.tableInTime positive G H (clearRegister state).1 []
  let returned : State ρ d := (called.finalState, ())
  have eta : ((clearRegister state).1, ()) = clearRegister state := by
    rcases state with ⟨state, extra⟩
    cases extra
    rfl
  have call : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inl (.inr .initialize_)), clearRegister state,
        copyFrame remaining v oldWord suffix⟩
      (some ⟨some (.inr .clearOldTable), returned,
        returnFrame remaining v oldWord newWord suffix⟩)
      ((MachineExpanderTable.timePolynomial d).eval oldWord.length) := by
    simpa only [MachineEmbedding.configuration, MachineEmbedding.label, tableReturn, eta,
      copyFrame, returnFrame, oldWord, newWord, returned] using
      tableExecution positive H growth (extraFrame remaining v suffix) called.execution
  have install := installTableInTime positive H growth
    (returnFrame remaining v oldWord newWord suffix) newWord
    (by rw [returnFrame_eq_cycleTapes, toBool_cycleTapes]; rfl)
    (by rw [returnFrame_eq_cycleTapes, toBool_cycleTapes]; rfl) returned
  rw [installed_returnFrame] at install
  have installRun : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .clearOldTable), returned, returnFrame remaining v oldWord newWord suffix⟩
      (some ⟨some (.inr (.affine .multiplySize .seed)), clearRegister returned,
        installedFrame remaining v newWord suffix⟩)
      (oldWord.length + 2 * newWord.length + (v + 1) + 4) := by
    simpa only [returnFrame_eq_cycleTapes, toBool_cycleTapes, cycleWords, tableTape,
      encodeWord_length] using install
  have multiply := multiplySizeInTime positive H growth
    (installedFrame remaining v newWord suffix) v rfl rfl rfl (clearRegister returned)
  rw [clearRegister_idempotent, multipliedFrame_eq_update] at multiply
  have clean := cleanupCountersInTime positive H growth
    (multipliedFrame d remaining v newWord suffix) (clearRegister returned)
  rw [clearRegister_idempotent, cleaned_multipliedFrame] at clean
  have cleanRun : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .drainInputVertex), clearRegister returned,
        multipliedFrame d remaining v newWord suffix⟩
      (some ⟨some (.inr .levelGuard), clearRegister returned,
        boundaryTapes remaining (v * cloudSize d) newWord suffix⟩) (v + 4) := by
    simpa only [multipliedFrame, toBool_cycleTapes, cycleWords, inputVertexTape,
      vertexCountTape, encodeWord_length, Nat.zero_add, Nat.add_assoc] using clean
  let a := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
    _ _ _ _ _ copy call
  let b := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
    _ _ _ _ _ a installRun
  let c := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
    _ _ _ _ _ b multiply
  let all := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
    _ _ _ _ _ c cleanRun
  refine ⟨clearRegister returned, ?_, ?_⟩
  · exact (caller_clearRegister returned).trans
      (called.caller_preserved.trans (caller_clearRegister state))
  · refine { toEvalsTo := all.toEvalsTo, steps_le_m := ?_ }
    have bound := all.steps_le_m
    unfold resizeCost
    change _ ≤ (MachineExpanderTable.timePolynomial d).eval oldWord.length +
      6 * v + oldWord.length + 2 * newWord.length + 15
    omega

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineExpanderFamilyLoop
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.overlay_accepts_expander _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.overlay_accepts_old _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_internal _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.actualRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual counted repetition of complete table-expansion cycles. The input
counter is physically decremented, and the invariant carries the exact table
at the completed family level. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineExpanderFamilyBounds

noncomputable def levelLoopCost {d : Nat} (H : Table (cloudSize d) d) : Nat → Nat → Nat
  | _, 0 => 1
  | start, remaining + 1 => 1 + resizeCost (family H start) H +
      levelLoopCost H (start + 1) remaining

theorem levelLoopCost_prefix {d : Nat} (H : Table (cloudSize d) d) (start remaining : Nat) :
    levelLoopCost H start remaining + resizeSum H start =
      resizeSum H (start + remaining) + remaining + 1 := by
  induction remaining generalizing start with
  | zero => simp [levelLoopCost, Nat.add_comm]
  | succ remaining ih =>
      have h := ih (start + 1)
      rw [resizeSum_succ] at h
      have index : start + 1 + remaining = start + (remaining + 1) := by omega
      rw [index] at h
      simp only [levelLoopCost]
      omega

theorem levelLoopCost_zero_start {d : Nat} (H : Table (cloudSize d) d) (remaining : Nat) :
    levelLoopCost H 0 remaining = resizeSum H remaining + remaining + 1 := by
  simpa only [resizeSum_zero, Nat.add_zero, Nat.zero_add] using
    levelLoopCost_prefix H 0 remaining

def levelLoopTapes {d : Nat} (H : Table (cloudSize d) d)
    (completed remaining : Nat) (suffix : List Bool) : ∀ tape, List (Alphabet tape) :=
  boundaryTapes remaining (vertexCount (degree d) completed)
    (encodeWords (rotationWords (family H completed))) suffix

structure LevelLoopRun {d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (completed remaining : Nat) (state : State ρ d) (suffix : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
    ⟨some (.inr .levelGuard), state, levelLoopTapes H completed remaining suffix⟩
    (some ⟨some (.inr .done), finalState, familyTapes H (completed + remaining) suffix⟩)
    (levelLoopCost H completed remaining)

/-- Every body is the already constructed actual resize run. There is no
whole-loop, body-trace, or computational-correctness premise. -/
noncomputable def levelLoopInTime {d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (completed remaining : Nat) (state : State ρ d) (suffix : List Bool) :
    LevelLoopRun positive H growth completed remaining state suffix := by
  induction remaining generalizing completed state with
  | zero =>
      refine ⟨clearRegister state, caller_clearRegister state, ?_⟩
      simpa only [levelLoopCost, levelLoopTapes, familyTapes, Nat.add_zero] using
        familySingleStep _ _ _ (levelGuard_boundary_zeroStep positive H growth
          (vertexCount (degree d) completed) (encodeWords (rotationWords (family H completed)))
          suffix state)
  | succ remaining ih =>
      let cycle := resizeInTime positive H growth (family H completed) remaining
        (clearRegister state) suffix
      let rest := ih (completed + 1) cycle.finalState
      let guard := familySingleStep _ _ _ (levelGuard_boundary_succStep positive H growth
        remaining (vertexCount (degree d) completed)
        (encodeWords (rotationWords (family H completed))) suffix state)
      have cycleRun : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
          ⟨some (.inr (.affine .copyCount .seed)), clearRegister state,
            levelLoopTapes H completed remaining suffix⟩
          (some ⟨some (.inr .levelGuard), cycle.finalState,
            levelLoopTapes H (completed + 1) remaining suffix⟩)
          (resizeCost (family H completed) H) := cycle.execution
      let first := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
        _ _ _ _ _ guard cycleRun
      let all := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
        _ _ _ _ _ first rest.execution
      have index : completed + 1 + remaining = completed + (remaining + 1) := by omega
      refine ⟨rest.finalState, ?_, ?_⟩
      · exact rest.caller_preserved.trans
          (cycle.caller_preserved.trans (caller_clearRegister state))
      · rw [index] at all
        refine { toEvalsTo := all.toEvalsTo, steps_le_m := ?_ }
        have bound := all.steps_le_m
        simp only [levelLoopCost]
        omega

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineExpanderFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineExpanderFamilyBounds

/-- Complete initialization, actual counted loop, and normalized halt. -/
noncomputable def familyInTime {d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (level : Nat) (state : State ρ d) (suffix : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .initialize_), state, initialTapes level suffix⟩
      (some ⟨none, initialState positive H (caller state), familyTapes H level suffix⟩)
      (familyBudget H level) := by
  let loop := levelLoopInTime positive H growth 0 level
    (initialState positive H (caller state)) suffix
  have initialRun : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .initialize_), state, initialTapes level suffix⟩
      (some ⟨some (.inr .levelGuard), initialState positive H (caller state),
        levelLoopTapes H 0 level suffix⟩) 1 :=
    singleFamilyStep _ _ _ (initialize_boundaryStep positive H growth level suffix state)
  have finalCaller : caller loop.finalState = caller state := loop.caller_preserved
  have done : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .done), loop.finalState, familyTapes H level suffix⟩
      (some ⟨none, initialState positive H (caller state), familyTapes H level suffix⟩) 1 := by
    simpa only [normalizeState, finalCaller] using
      singleFamilyStep _ _ _ (doneStep positive H growth (familyTapes H level suffix)
        loop.finalState)
  have loopRun : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .levelGuard), initialState positive H (caller state),
        levelLoopTapes H 0 level suffix⟩
      (some ⟨some (.inr .done), loop.finalState, familyTapes H level suffix⟩)
      (levelLoopCost H 0 level) := by simpa only [Nat.zero_add] using loop.execution
  let first := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
    _ _ _ _ _ initialRun loopRun
  let all := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
    _ _ _ _ _ first done
  refine { toEvalsTo := all.toEvalsTo, steps_le_m := ?_ }
  have bound := all.steps_le_m
  have costEquality := levelLoopCost_zero_start H level
  unfold familyBudget
  omega

/-- At the physically computable padding level, the actual family run has a
fixed polynomial bound in requested unary size. The separate ceiling-power
machine supplies this exact level and preserves the requested size. -/
noncomputable def paddedFamilyInTime {ρ : Type} [Fintype ρ]
    (H : Table (cloudSize PCP.Expanders.baseDegree) PCP.Expanders.baseDegree)
    (requested : Nat) (state : State ρ PCP.Expanders.baseDegree) (suffix : List Bool) :
    StateTransition.EvalsToInTime
      (TM2.step (program baseDegree_positive H baseDegree_cloud_gt_one))
      ⟨some (.inr .initialize_), state,
        initialTapes (PCP.PreprocessingLevels.boundedLevel requested) suffix⟩
      (some ⟨none, initialState baseDegree_positive H (caller state),
        familyTapes H (PCP.PreprocessingLevels.boundedLevel requested) suffix⟩)
      (inputCoefficient * (requested + 1)^5) where
  toEvalsTo := (familyInTime baseDegree_positive H baseDegree_cloud_gt_one
    (PCP.PreprocessingLevels.boundedLevel requested) state suffix).toEvalsTo
  steps_le_m := (familyInTime baseDegree_positive H baseDegree_cloud_gt_one
    (PCP.PreprocessingLevels.boundedLevel requested) state suffix).steps_le_m.trans
      (familyBudget_at_boundedLevel_le H requested)

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachinePaddedExpanderFamilyBoundsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamilyBounds

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

def timeCoefficient : Nat :=
  MachineExpanderFamilyBounds.inputCoefficient + PCP.ExpanderFamily.growth + 29

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C timeCoefficient * Polynomial.X^5

theorem timePolynomial_encoding (k : Nat) :
    timePolynomial.eval (encodeWord k).length = timeCoefficient * (k + 1)^5 := by
  simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, encodeWord_length]

theorem ceilingCost_le (g k : Nat) :
    (MachineCeilingPower.timePolynomial g).eval (encodeWord k).length ≤
      (g + 29) * (k + 1)^5 := by
  rw [MachineCeilingPower.timePolynomial_encoding]
  have squareBound : (k + 1)^2 ≤ (k + 1)^5 :=
    Nat.pow_le_pow_right (Nat.succ_pos k) (by decide)
  have linearBound : k + 1 ≤ (k + 1)^5 := by
    simpa only [pow_one] using Nat.pow_le_pow_right
      (Nat.succ_pos k) (show 1 ≤ 5 by decide)
  have constantBound : 1 ≤ (k + 1)^5 := by omega
  have squareCost := Nat.mul_le_mul_left (g + 8) squareBound
  have linearCost := Nat.mul_le_mul_left 18 linearBound
  have constantCost := Nat.mul_le_mul_left 3 constantBound
  unfold MachineCeilingPower.timeBound
  nlinarith only [squareCost, linearCost, constantCost]

theorem combinedCost_le (k : Nat) :
    (MachineCeilingPower.timePolynomial PCP.ExpanderFamily.growth).eval
        (encodeWord k).length +
      MachineExpanderFamilyBounds.inputCoefficient * (k + 1)^5 ≤
        timePolynomial.eval (encodeWord k).length := by
  rw [timePolynomial_encoding]
  have h := ceilingCost_le PCP.ExpanderFamily.growth k
  unfold timeCoefficient
  nlinarith only [h]

def outputWord
    (H : Table (cloudSize PCP.Expanders.baseDegree) PCP.Expanders.baseDegree) (k : Nat) :
    List Bool :=
  encodeWords (rotationWords (family H (PCP.PreprocessingLevels.boundedLevel k)))

end UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamilyBounds


namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily

open Turing

section TableCoordinates

open PCP.ExpanderTables PCP.ExpanderRowControl

theorem familyView_right (j : Tape) (tape : MachineExpanderFamily.Tape)
    (h : familyView j = some tape) : familyTape tape = j := by
  cases j with
  | inl j =>
    have hj : j = tape := Option.some.inj h
    subst tape
    rfl
  | inr j => simp [familyView] at h

theorem ceilingView_right (j : Tape) (tape : MachineCeilingPower.Tape)
    (h : ceilingView j = some tape) : ceilingTape tape = j := by
  cases j with
  | inl j =>
    cases j with
    | inl j => simp [ceilingView] at h
    | inr j =>
      cases j <;> simp_all [ceilingView, ceilingTape]
      cases h
      rfl
  | inr j => cases j <;> simp_all [ceilingView, ceilingTape] <;> cases h <;> rfl

def main : Label := .inr .init

open MachineCloudPadding PCP.ExpanderTableWords

end TableCoordinates


/-!
# Actual requested-size to expander-table computation

One finite program physically computes the padding level and then constructs
the complete corresponding rotation table. The level output of the first
phase is the input tape of the second phase. The actual execution preserves
the request, retains the padded size, and has a fixed polynomial time bound
in the unary request length.
-/

open MachineCloudPadding MachineComposition

end UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineCloudRankLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_archive _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_append _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_nil _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_append _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_nil _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_done _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_head _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_relation _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_reverseIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_words _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRows_acceptsAt _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRows_get _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRows_reverseAt _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_headIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_headValue _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_relation _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_reverseIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_row _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_head _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tableBits _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tableWords _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCloudPadding.countMemory _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.tableExecution_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.rowExecution_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRow.rowBlock_at _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Relations.oldPredicate_relationAt _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Relations.relationAt_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.build_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.build_vertices _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.rowList_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.rows_at _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableWords.decode_rotationWords _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringRowData.basePredicate_transposeBits _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringRowData.basePredicate_walkBits _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Preprocessing.graph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.equalityRelation_apply _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.accepts_materialize _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.accepts_pad _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.baseGraph_pad _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.rotation_pad _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_internal _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.vertexOrder_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.vertexOrder_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.actualRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Regularization.graph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_reverse_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_reverse_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.paddedG_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCloudRank

open Turing MachineComposition MachineCloudCount

variable {σ : Type}

open UniqueGamesTheorem.Foundations.PCP

theorem tableRows_length (t : GraphTables.Table) : (tableRows t).length = t.darts := by
  simp only [tableRows, List.length_map, GraphTables.rowList_length]

/-- The executable cloud rank is exactly the count of matching earlier rows. -/
theorem cloudRank_eq_prefix_count (t : GraphTables.Table) (v : Fin t.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics t) v) :
    (PreprocessingCloudIndex.cloudRank t v e).val =
      rowsHits v.val ((tableRows t).take e.val.val) := by
  have hindex := idxOf_filter_prefix (fun x : Fin t.darts => decide (t.rows[x].tail = v))
    e.val (by simpa using e.property) (List.finRange t.darts) (List.mem_finRange e.val)
  simp only [List.idxOf_finRange] at hindex
  change (PreprocessingCloudIndex.cloudDarts t v).idxOf e.val = _
  unfold PreprocessingCloudIndex.cloudDarts
  rw [hindex, rowsHits_eq_filter]
  simp only [tableRows, rowList_eq_finRange_map, ← List.map_take, List.filter_map,
    List.length_map, Function.comp_def, Fin.val_inj]

end UniqueGamesTheorem.Foundations.Complexity.MachineCloudRank

/-! Actual inverse cloud numbering. The input table and query are copied
preservingly. A unary working rank decreases only on equal stored tail
fields; a separate unary row position increases on every skipped row.
Only finite phase flags and symbol registers occur in the control state. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCloudSelect

open Turing MachineComposition
open MachineCloudCount (Row rowWords rowTime rowsHits tableRows)

variable {σ : Type}

def program : Label → TM2.Stmt Alphabet Label (State σ) :=
  MachineEmbedding.program (some (.inr .dispatch)) baseProgram extra

theorem liftTrace (phase : Phase) (position : List Bool) (n : Nat)
    (a b : TM2.Cfg BaseAlphabet BaseLabel (BaseState σ))
    (h : (advance (TM2.step baseProgram))^[n] (some a) = some b) :
    (advance (TM2.step (program (σ := σ))))^[n]
      (some (MachineEmbedding.configuration (some (.inr .dispatch)) phase
        (fun _ : Unit => position) a)) =
      some (MachineEmbedding.configuration (some (.inr .dispatch)) phase
        (fun _ : Unit => position) b) :=
  liftSuccessfulTrace (TM2.step baseProgram) (TM2.step program)
    (MachineEmbedding.configuration (some (.inr .dispatch)) phase (fun _ : Unit => position))
    (MachineEmbedding.step_simulation (some (.inr .dispatch)) phase
      (fun _ : Unit => position) baseProgram extra) n a b h

theorem compareTrace (original suffix targetSuffix rank position : List Bool)
    (x v : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[x + min x v + 3]
      (some (cfg (some (.inl .field)) .checking original (encodeWord x ++ suffix)
        (encodeWord v ++ targetSuffix) [] rank position ambient register)) =
      some (cfg (some (.inr .dispatch)) .checking original suffix
        (encodeWord v ++ targetSuffix) (List.replicate (if x = v then 1 else 0) true)
        rank position ambient none) := by
  have h := MachineCloudCount.preservingFieldTrace BaseLabel.field BaseLabel.restore BaseLabel.done
    baseProgram rfl rfl original suffix targetSuffix [] rank x v ambient register
  simp only [List.append_nil] at h
  have hhalt : (advance (TM2.step baseProgram))^[x + min x v + 3]
      (some ⟨some .field, ((ambient, false), register),
        MachineCloudCount.memory original (encodeWord x ++ suffix)
          (encodeWord v ++ targetSuffix) [] [] rank⟩) =
      some ⟨none, ((ambient, false), none),
        MachineCloudCount.memory original suffix (encodeWord v ++ targetSuffix) []
          (List.replicate (if x = v then 1 else 0) true) rank⟩ := by
    rw [show x + min x v + 3 = (x + min x v + 2) + 1 by omega,
      Function.iterate_succ_apply', h, advance_some]
    rfl
  convert liftTrace Phase.checking position _ _ _ hhalt using 1 <;> rfl

theorem dispatch_miss (original work target rank position : List Bool) (ambient : σ) :
    TM2.step program (cfg (some (.inr .dispatch)) .checking
      original work target [] rank position ambient none) =
      some (cfg (some (.inl (skipLabel 0))) .advancing
        original work target [] rank position ambient none) := by
  simp [program, MachineEmbedding.program, extra, dispatcher, go, TM2.stepAux, TM2.step, cfg]

theorem dispatch_hit_succ (original work target rankSuffix position : List Bool)
    (rank : Nat) (ambient : σ) :
    TM2.step program (cfg (some (.inr .dispatch)) .checking
      original work target [true] (encodeWord (rank + 1) ++ rankSuffix) position ambient none) =
      some (cfg (some (.inl (skipLabel 0))) .advancing original work target []
        (encodeWord rank ++ rankSuffix) position ambient none) := by
  simp [program, MachineEmbedding.program, extra, dispatcher, go, TM2.stepAux, TM2.step,
    cfg, encodeWord, List.replicate_succ]

theorem dispatch_hit_zero (original work target rankSuffix position : List Bool) (ambient : σ) :
    TM2.step program (cfg (some (.inr .dispatch)) .checking
      original work target [true] (encodeWord 0 ++ rankSuffix) position ambient none) =
      some (cfg (some (.inl .clearWork)) .finishing
        original work target [] rankSuffix position ambient none) := by
  simp [program, MachineEmbedding.program, extra, dispatcher, go, TM2.stepAux, TM2.step,
    cfg, encodeWord]

theorem advanceStep (original work target rank positionSuffix : List Bool)
    (position : Nat) (ambient : σ) :
    TM2.step program (cfg (some (.inr .dispatch)) .advancing original work target []
      rank (encodeWord position ++ positionSuffix) ambient none) =
      some (cfg (some (.inl .field)) .checking original work target []
        rank (encodeWord (position + 1) ++ positionSuffix) ambient none) := by
  simp [program, MachineEmbedding.program, extra, dispatcher, go, TM2.stepAux, TM2.step,
    cfg, encodeWord, List.replicate_succ]

theorem finishStep (original target position : List Bool) (ambient : σ) :
    TM2.step program (cfg (some (.inr .dispatch)) .finishing
      original [] target [] [] position ambient none) =
      some (cfg none .checking original [] target [] [] position ambient none) := by
  simp [program, MachineEmbedding.program, extra, dispatcher, go, TM2.stepAux, TM2.step, cfg]

theorem initializeStep (original target output : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program (cfg (some (.inr .initialize_)) .checking
      original [] target [] [] output ambient register) =
      some (cfg (some (.inl .queryFirst)) .checking
        original [] target [] [] (encodeWord 0 ++ output) ambient none) := by
  simp [program, MachineEmbedding.program, extra, go, TM2.stepAux, TM2.step, cfg, encodeWord]

/-- The rest of a row is skipped field by field by the actual fixed program. -/
theorem skipTrace (fields : List Nat) (hwidth : fields.length = 4097)
    (original suffix target rank position : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[(encodeWords fields).length + 1]
      (some (cfg (some (.inl (skipLabel 0))) .advancing original
        (encodeWords fields ++ suffix) target [] rank position ambient none)) =
      some (cfg (some (.inr .dispatch)) .advancing
        original suffix target [] rank position ambient none) := by
  have h := MachineCloudCount.discardFieldsTrace skipLabel (baseProgram (σ := σ)) fields 0
    (by intro i hi; simpa only [Nat.zero_add] using baseProgram_skip (hwidth ▸ hi))
    original suffix target [] [] rank ambient false none
  have hnonempty : fields ≠ [] := by intro h; simp [h] at hwidth
  simp only [Nat.zero_add, hwidth, skipLabel, lt_self_iff_false, ↓reduceDIte,
    hnonempty, ite_false, if_false] at h
  have raw : (advance (TM2.step baseProgram))^[(encodeWords fields).length + 1]
      (some ⟨some (skipLabel 0), ((ambient, false), none),
        MachineCloudCount.memory original (encodeWords fields ++ suffix) target [] [] rank⟩) =
      some ⟨none, ((ambient, false), none),
        MachineCloudCount.memory original suffix target [] [] rank⟩ := by
    rw [Function.iterate_succ_apply']
    simp only [skipLabel, dite_eq_left (by decide : 0 < 4097)] at h ⊢
    rw [h, advance_some]
    rfl
  convert liftTrace Phase.advancing position _ _ _ raw using 1 <;> rfl

/-- One nonselected row, with enough remaining rank to pass this row when
it matches. Its global position is incremented on the output tape. -/
theorem rowSkipTrace (r : Row) (hwidth : r.2.length = 4097) (v rank position : Nat)
    (original suffix targetSuffix rankSuffix outputSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[rowTime v r + 3]
      (some (cfg (some (.inl .field)) .checking original
        (encodeWords (rowWords r) ++ suffix) (encodeWord v ++ targetSuffix) []
        (encodeWord (rank + if r.1 = v then 1 else 0) ++ rankSuffix)
        (encodeWord position ++ outputSuffix) ambient register)) =
      some (cfg (some (.inl .field)) .checking original suffix
        (encodeWord v ++ targetSuffix) [] (encodeWord rank ++ rankSuffix)
        (encodeWord (position + 1) ++ outputSuffix) ambient none) := by
  have hcompare := compareTrace original (encodeWords r.2 ++ suffix) targetSuffix
    (encodeWord (rank + if r.1 = v then 1 else 0) ++ rankSuffix)
    (encodeWord position ++ outputSuffix) r.1 v ambient register
  have hdispatch : TM2.step program
      (cfg (some (.inr .dispatch)) .checking original (encodeWords r.2 ++ suffix)
        (encodeWord v ++ targetSuffix) (List.replicate (if r.1 = v then 1 else 0) true)
        (encodeWord (rank + if r.1 = v then 1 else 0) ++ rankSuffix)
        (encodeWord position ++ outputSuffix) ambient none) =
      some (cfg (some (.inl (skipLabel 0))) .advancing original (encodeWords r.2 ++ suffix)
        (encodeWord v ++ targetSuffix) [] (encodeWord rank ++ rankSuffix)
        (encodeWord position ++ outputSuffix) ambient none) := by
    by_cases hit : r.1 = v
    · simpa only [ite_eq_left hit, List.replicate_succ, List.replicate_zero] using
        dispatch_hit_succ original (encodeWords r.2 ++ suffix) (encodeWord v ++ targetSuffix)
          rankSuffix (encodeWord position ++ outputSuffix) rank ambient
    · simpa only [ite_eq_right hit, Nat.add_zero, List.replicate_zero] using
        dispatch_miss original (encodeWords r.2 ++ suffix) (encodeWord v ++ targetSuffix)
          (encodeWord rank ++ rankSuffix) (encodeWord position ++ outputSuffix) ambient
  have hskip := skipTrace r.2 hwidth original suffix (encodeWord v ++ targetSuffix)
    (encodeWord rank ++ rankSuffix) (encodeWord position ++ outputSuffix) ambient
  have ht : rowTime v r + 3 =
      1 + (((encodeWords r.2).length + 1) + (1 + (r.1 + min r.1 v + 3))) := by
    simp only [rowTime, rowWords, encodeWords, List.length_append, encodeWord_length]
    omega
  rw [ht, Function.iterate_add_apply _ 1,
    Function.iterate_add_apply _ ((encodeWords r.2).length + 1),
    Function.iterate_add_apply _ 1]
  simp only [rowWords, encodeWords, List.append_assoc]
  rw [hcompare, Function.iterate_one, advance_some, hdispatch, hskip,
    advance_some]
  exact advanceStep original suffix (encodeWord v ++ targetSuffix)
    (encodeWord rank ++ rankSuffix) outputSuffix position ambient

/-- A preceding consumes precisely its number of matching tails from unary
rank, while physically counting every original row on the position tape. -/
theorem prefixTrace (rs : List Row) (hwidth : ∀ r ∈ rs, r.2.length = 4097)
    (v rank position : Nat) (original suffix targetSuffix rankSuffix outputSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[prefixTime v rs]
      (some (cfg (some (.inl .field)) .checking original
        (encodeWords (rs.flatMap rowWords) ++ suffix) (encodeWord v ++ targetSuffix) []
        (encodeWord (rowsHits v rs + rank) ++ rankSuffix)
        (encodeWord position ++ outputSuffix) ambient register)) =
      some (cfg (some (.inl .field)) .checking original suffix
        (encodeWord v ++ targetSuffix) [] (encodeWord rank ++ rankSuffix)
        (encodeWord (position + rs.length) ++ outputSuffix) ambient
        (if rs = [] then register else none)) := by
  induction rs generalizing position register with
  | nil => simp [prefixTime, rowsHits, encodeWords]
  | cons r rs ih =>
    have hrow := rowSkipTrace r (hwidth r (by simp)) v (rowsHits v rs + rank) position
      original (encodeWords (rs.flatMap rowWords) ++ suffix) targetSuffix rankSuffix
      outputSuffix ambient register
    have hrest := ih (by intro x hx; exact hwidth x (by simp [hx])) (position + 1) none
    simp only [prefixTime, List.flatMap_cons, encodeWords_append, List.append_assoc]
    rw [Function.iterate_add_apply]
    have hi : (if r.1 = v then 1 else 0) + rowsHits v rs + rank =
        (rowsHits v rs + rank) + (if r.1 = v then 1 else 0) := by omega
    simp only [rowsHits, hi]
    rw [hrow]
    simpa only [ite_self, List.cons_ne_nil, ite_false, if_false, List.length_cons,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest

/-- Both copied workspaces are physically drained after finding the row;
the original table, complete query, and position output are retained. -/
theorem cleanupTrace (original work target rank position : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[work.length + rank.length + 4]
      (some (cfg (some (.inl .clearWork)) .finishing
        original work target [] rank position ambient none)) =
      some (cfg none .checking original [] target [] [] position ambient none) := by
  have hwork := MachineDrain.drainTrace MachineCloudCount.Tape.work BaseLabel.clearWork (some BaseLabel.clearRank)
    baseProgram rfl (MachineCloudCount.memory original work target [] [] rank) work
    (ambient, false) none
  simp only [MachineCloudCount.update_memory_work] at hwork
  have hrank := MachineDrain.drainTrace MachineCloudCount.Tape.spare BaseLabel.clearRank (some BaseLabel.done)
    baseProgram rfl (MachineCloudCount.memory original [] target [] [] rank) rank
    (ambient, false) none
  simp only [MachineCloudRank.update_memory_spare] at hrank
  have raw : (advance (TM2.step baseProgram))^[work.length + rank.length + 3]
      (some ⟨some .clearWork, ((ambient, false), none),
        MachineCloudCount.memory original work target [] [] rank⟩) =
      some ⟨none, ((ambient, false), none),
        MachineCloudCount.memory original [] target [] [] []⟩ := by
    rw [show work.length + rank.length + 3 =
        1 + ((rank.length + 1) + (work.length + 1)) by omega,
      Function.iterate_add_apply _ 1, Function.iterate_add_apply _ (rank.length + 1),
      hwork, hrank, Function.iterate_one, advance_some]
    rfl
  have lifted := liftTrace Phase.finishing position _ _ _ raw
  have h : (advance (TM2.step program))^[work.length + rank.length + 3]
      (some (cfg (some (.inl .clearWork)) .finishing
        original work target [] rank position ambient none)) =
      some (cfg (some (.inr .dispatch)) .finishing
        original [] target [] [] position ambient none) := by
    convert lifted using 1 <;> rfl
  rw [show work.length + rank.length + 4 = (work.length + rank.length + 3) + 1 by omega,
    Function.iterate_succ_apply', h, advance_some]
  exact finishStep original target position ambient

theorem selectedTrace (v : Nat) (original work targetSuffix rankSuffix position : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * v + work.length + rankSuffix.length + 8]
      (some (cfg (some (.inl .field)) .checking original (encodeWord v ++ work)
        (encodeWord v ++ targetSuffix) [] (encodeWord 0 ++ rankSuffix) position ambient register)) =
      some (cfg none .checking original [] (encodeWord v ++ targetSuffix) [] [] position ambient none) := by
  have hcompare := compareTrace original work targetSuffix (encodeWord 0 ++ rankSuffix)
    position v v ambient register
  simp only [ite_true, if_true, List.replicate_succ, List.replicate_zero] at hcompare
  rw [show 2 * v + work.length + rankSuffix.length + 8 =
      (work.length + rankSuffix.length + 4) + (1 + (v + min v v + 3)) by
        simp only [Nat.min_self]; omega,
    Function.iterate_add_apply _ (work.length + rankSuffix.length + 4),
    Function.iterate_add_apply _ 1, hcompare, Function.iterate_one, advance_some,
    dispatch_hit_zero]
  exact cleanupTrace original work (encodeWord v ++ targetSuffix) rankSuffix position ambient

/-- Preserve the complete query and table while making the two working
copies; extract the rank and skip the two actual table header fields. -/
theorem prepareTrace (n m v rank : Nat) (rs : List Row)
    (querySuffix position : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[prepareSteps n m v rank rs querySuffix]
      (some (cfg (some (.inl .queryFirst)) .checking (MachineCloudCount.inputWord n m rs)
        [] (queryWord v rank querySuffix) [] [] position ambient register)) =
      some (cfg (some (.inl .field)) .checking (MachineCloudCount.inputWord n m rs)
        (encodeWords (rs.flatMap rowWords)) (queryWord v rank querySuffix) []
        (encodeWord rank ++ querySuffix) position ambient none) := by
  have hquery := MachineCopy.copyTrace MachineCloudCount.Tape.target MachineCloudCount.Tape.spare MachineCloudCount.Tape.scratch
    (by decide) (by decide) (by decide) false BaseLabel.queryFirst BaseLabel.querySecond
    (some BaseLabel.querySkip) baseProgram rfl rfl
    (MachineCloudCount.memory (MachineCloudCount.inputWord n m rs) []
      (queryWord v rank querySuffix) [] [] []) rfl (ambient, false) register
  simp only [MachineCloudCount.memory_target, MachineCloudCount.memory_spare,
    List.append_nil, MachineCloudRank.update_memory_spare] at hquery
  have hquerySkip := MachineLookup.discardTrace MachineCloudCount.Tape.spare BaseLabel.querySkip BaseLabel.tableFirst
    baseProgram rfl (MachineCloudCount.memory (MachineCloudCount.inputWord n m rs) []
      (queryWord v rank querySuffix) [] [] (queryWord v rank querySuffix))
    v (encodeWord rank ++ querySuffix) rfl (ambient, false) none
  simp only [MachineCloudRank.update_memory_spare] at hquerySkip
  have hcopy := MachineCopy.copyTrace MachineCloudCount.Tape.original MachineCloudCount.Tape.work MachineCloudCount.Tape.scratch
    (by decide) (by decide) (by decide) false BaseLabel.tableFirst BaseLabel.tableSecond
    (some BaseLabel.headerFirst) baseProgram rfl rfl
    (MachineCloudCount.memory (MachineCloudCount.inputWord n m rs) []
      (queryWord v rank querySuffix) [] [] (encodeWord rank ++ querySuffix))
    rfl (ambient, false) none
  simp only [MachineCloudCount.memory_original, MachineCloudCount.memory_work,
    List.append_nil, MachineCloudCount.update_memory_work] at hcopy
  have hfirst := MachineLookup.discardTrace MachineCloudCount.Tape.work BaseLabel.headerFirst BaseLabel.headerSecond
    baseProgram rfl (MachineCloudCount.memory (MachineCloudCount.inputWord n m rs)
      (MachineCloudCount.inputWord n m rs) (queryWord v rank querySuffix) [] []
      (encodeWord rank ++ querySuffix))
    n (encodeWord m ++ encodeWords (rs.flatMap rowWords))
    (MachineCloudCount.inputWord_eq n m rs) (ambient, false) none
  simp only [MachineCloudCount.update_memory_work] at hfirst
  have hsecond := MachineLookup.discardTrace MachineCloudCount.Tape.work BaseLabel.headerSecond BaseLabel.field
    baseProgram rfl (MachineCloudCount.memory (MachineCloudCount.inputWord n m rs)
      (encodeWord m ++ encodeWords (rs.flatMap rowWords)) (queryWord v rank querySuffix)
      [] [] (encodeWord rank ++ querySuffix))
    m (encodeWords (rs.flatMap rowWords)) rfl (ambient, false) none
  simp only [MachineCloudCount.update_memory_work] at hsecond
  have raw : (advance (TM2.step baseProgram))^[prepareSteps n m v rank rs querySuffix]
      (some ⟨some .queryFirst, ((ambient, false), register),
        MachineCloudCount.memory (MachineCloudCount.inputWord n m rs) []
          (queryWord v rank querySuffix) [] [] []⟩) =
      some ⟨some .field, ((ambient, false), none),
        MachineCloudCount.memory (MachineCloudCount.inputWord n m rs)
          (encodeWords (rs.flatMap rowWords)) (queryWord v rank querySuffix) [] []
          (encodeWord rank ++ querySuffix)⟩ := by
    rw [show prepareSteps n m v rank rs querySuffix =
        (m + 1) + ((n + 1) + (2 * ((MachineCloudCount.inputWord n m rs).length + 1) +
          ((v + 1) + 2 * ((queryWord v rank querySuffix).length + 1)))) by
          unfold prepareSteps; omega,
      Function.iterate_add_apply _ (m + 1), Function.iterate_add_apply _ (n + 1),
      Function.iterate_add_apply _ (2 * ((MachineCloudCount.inputWord n m rs).length + 1)),
      Function.iterate_add_apply _ (v + 1), hquery, hquerySkip, hcopy, hfirst]
    exact hsecond
  convert liftTrace Phase.checking position _ _ _ raw using 1 <;> rfl

/-- A selected matching field is reached after precisely the matching count
of its actual preceding rows has been consumed from the copied query. -/
theorem prefixSelectedTrace (preceding : List Row)
    (hwidth : ∀ r ∈ preceding, r.2.length = 4097) (v position : Nat)
    (original work targetSuffix rankSuffix outputSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[prefixTime v preceding + 2 * v + work.length + rankSuffix.length + 8]
      (some (cfg (some (.inl .field)) .checking original
        (encodeWords (preceding.flatMap rowWords) ++ (encodeWord v ++ work))
        (encodeWord v ++ targetSuffix) [] (encodeWord (rowsHits v preceding) ++ rankSuffix)
        (encodeWord position ++ outputSuffix) ambient register)) =
      some (cfg none .checking original [] (encodeWord v ++ targetSuffix) [] []
        (encodeWord (position + preceding.length) ++ outputSuffix) ambient none) := by
  have hp := prefixTrace preceding hwidth v 0 position original (encodeWord v ++ work)
    targetSuffix rankSuffix outputSuffix ambient register
  simp only [Nat.add_zero] at hp
  have hs := selectedTrace v original work targetSuffix rankSuffix
    (encodeWord (position + preceding.length) ++ outputSuffix) ambient
    (if preceding = [] then register else none)
  rw [show prefixTime v preceding + 2 * v + work.length + rankSuffix.length + 8 =
      (2 * v + work.length + rankSuffix.length + 8) + prefixTime v preceding by omega,
    Function.iterate_add_apply, hp]
  exact hs

/-- Complete execution for the actual encoded preceding decomposition. The
decomposition is semantic data; every machine phase is proved above. -/
theorem fullTrace (n m v rank : Nat) (rs preceding : List Row) (work : List Bool)
    (hwidth : ∀ r ∈ preceding, r.2.length = 4097)
    (hword : encodeWords (rs.flatMap rowWords) =
      encodeWords (preceding.flatMap rowWords) ++ (encodeWord v ++ work))
    (hrank : rank = rowsHits v preceding) (querySuffix outputSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[totalSteps n m v rank rs preceding work querySuffix]
      (some (cfg (some (.inr .initialize_)) .checking (MachineCloudCount.inputWord n m rs)
        [] (queryWord v rank querySuffix) [] [] outputSuffix ambient register)) =
      some (cfg none .checking (MachineCloudCount.inputWord n m rs) []
        (queryWord v rank querySuffix) [] [] (encodeWord preceding.length ++ outputSuffix) ambient none) := by
  have hp := prepareTrace n m v rank rs querySuffix (encodeWord 0 ++ outputSuffix) ambient none
  have hs := prefixSelectedTrace preceding hwidth v 0 (MachineCloudCount.inputWord n m rs) work
    (encodeWord rank ++ querySuffix) querySuffix outputSuffix ambient none
  simp only [Nat.zero_add] at hs
  rw [← hrank, ← hword] at hs
  rw [show totalSteps n m v rank rs preceding work querySuffix =
      (prefixTime v preceding + 2 * v + work.length + querySuffix.length + 8) +
        (prepareSteps n m v rank rs querySuffix + 1) by unfold totalSteps; omega,
    Function.iterate_add_apply _ (prefixTime v preceding + 2 * v + work.length + querySuffix.length + 8),
    Function.iterate_succ_apply _ (prepareSteps n m v rank rs querySuffix),
    advance_some, initializeStep, hp]
  exact hs

open UniqueGamesTheorem.Foundations.PCP

/-- Bytes remaining after the selected row's actual tail field. -/
def remainder (t : GraphTables.Table) (e : Fin t.darts) : List Bool :=
  encodeWords (t.rows[e].reverseIndex.val :: GraphTables.relationWords t.rows[e].relation) ++
    encodeWords (((tableRows t).drop (e.val + 1)).flatMap rowWords)

theorem tableRows_getElem (t : GraphTables.Table) (e : Fin t.darts) :
    (tableRows t)[e.val]'(by rw [MachineCloudRank.tableRows_length]; exact e.isLt) =
      (t.rows[e].tail.val, t.rows[e].reverseIndex.val :: GraphTables.relationWords t.rows[e].relation) := by
  simp only [MachineCloudCount.tableRows, MachineCloudCount.rowList_eq_finRange_map,
    List.getElem_map, List.getElem_finRange]
  apply congrArg (fun j : Fin t.darts =>
    (t.rows[j].tail.val, t.rows[j].reverseIndex.val :: GraphTables.relationWords t.rows[j].relation))
  apply Fin.ext
  rfl

/-- Canonical dart indexing yields the literal byte decomposition consumed
by the actual preceding scan and final matching-field test. -/
theorem tableWord_split (t : GraphTables.Table) (v : Fin t.vertices) (e : Fin t.darts)
    (owner : t.rows[e].tail = v) :
    encodeWords ((tableRows t).flatMap rowWords) =
      encodeWords (((tableRows t).take e.val).flatMap rowWords) ++
        (encodeWord v.val ++ remainder t e) := by
  have he : e.val < (tableRows t).length := by
    rw [MachineCloudRank.tableRows_length]
    exact e.isLt
  rw [MachineCloudRank.encoded_rows_split (tableRows t) e.val, List.drop_eq_getElem_cons he]
  simp only [List.flatMap_cons, encodeWords_append]
  rw [tableRows_getElem]
  simp only [rowWords, encodeWords, owner, remainder, List.append_assoc]

def cloudSelectSteps (t : GraphTables.Table) (v : Fin t.vertices)
    (i : Fin (PreprocessingCloudIndex.cloudSize t v)) (querySuffix : List Bool) : Nat :=
  let e := (PreprocessingCloudIndex.cloudSelect t v i).val
  totalSteps t.vertices t.darts v.val i.val (tableRows t) ((tableRows t).take e.val)
    (remainder t e) querySuffix

theorem cloudSelectTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (i : Fin (PreprocessingCloudIndex.cloudSize t v)) (querySuffix outputSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[cloudSelectSteps t v i querySuffix]
      (some (cfg (some (.inr .initialize_)) .checking (GraphTables.tableBits t)
        [] (queryWord v.val i.val querySuffix) [] [] outputSuffix ambient register)) =
      some (cfg none .checking (GraphTables.tableBits t) [] (queryWord v.val i.val querySuffix)
        [] [] (encodeWord (PreprocessingCloudIndex.cloudSelect t v i).val.val ++ outputSuffix)
        ambient none) := by
  let e := PreprocessingCloudIndex.cloudSelect t v i
  have hword := tableWord_split t v e.val e.property
  have hrank : i.val = rowsHits v.val ((tableRows t).take e.val.val) := by
    simpa only [PreprocessingCloudIndex.cloudRank_cloudSelect] using
      MachineCloudRank.cloudRank_eq_prefix_count t v (PreprocessingCloudIndex.cloudSelect t v i)
  have h := fullTrace t.vertices t.darts v.val i.val (tableRows t)
    ((tableRows t).take e.val.val) (remainder t e.val)
    (by intro r hr; exact MachineCloudCount.tableRows_width t r (List.mem_of_mem_take hr))
    hword hrank querySuffix outputSuffix ambient register
  have htake : ((tableRows t).take e.val.val).length = e.val.val := by
    rw [List.length_take, MachineCloudRank.tableRows_length,
      Nat.min_eq_left e.val.isLt.le]
  rw [MachineCloudCount.tableRows_input, htake] at h
  exact h

end UniqueGamesTheorem.Foundations.Complexity.MachineCloudSelect

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularInternalRow
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_archive _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.boolView_outer _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.caller_initialState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.caller_normalizeState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.clearRegister_initialState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.program_outer _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.program_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.tableExecution_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamilyBounds.familyBudget_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamilyBounds.resizeSum_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionStates_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.program_firstEmit _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.program_outputEmit _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.program_secondEmit _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.accumulatedVertices_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.caller_boundaryState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.caller_prepareState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.caller_resetState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.caller_rowAfterState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.clearRegister_boundaryState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.prepareState_boundaryState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.program_outer _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.program_row _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.rowAfterState_position _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.rowExecution_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRow.rowBlock_at _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMasterState.clearBuffer_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMasterState.clearBuffer_withBuffer _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMasterState.compareEquiv_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMasterState.compareEquiv_symm_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMasterState.compareEquiv_withBuffer _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMasterState.equalityBit_clean _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMasterState.rowEquiv_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMasterState.rowEquiv_symm_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMasterState.rowEquiv_withBuffer _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.generatedWords_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.priorVertices_full _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.priorVertices_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.vertexWords_drop_full _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.vertexWords_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringRowData.basePredicate_transposeBits _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringRowData.leftMatches_transposeBits _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringRowData.rightMatches_transposeBits _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.overlay_accepts_expander _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.overlay_accepts_old _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.actualRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
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

/-- This literal is independent of the graph input. -/
def equalityBits : List Bool :=
  encodeWords (GraphTables.relationWords PreprocessingInternalRows.equalityRelation)

def emittedBits (q x z r : Nat) : List Bool :=
  encodeWord x ++ encodeWord ((q + 1) * z + r) ++ equalityBits

theorem emittedBits_length (q x z r : Nat) :
    (emittedBits q x z r).length = x + ((q + 1) * z + r) + equalityBits.length + 2 := by
  simp only [emittedBits, List.length_append, encodeWord_length]
  omega

/-- The address supplied to the physical lookup is the actual port-table row. -/
theorem selected_rotation {n q : Nat} (table : ExpanderTables.Table n q)
    (i : Fin n) (p : Fin q) :
    (ExpanderTableWords.rotationWords table)[q * i.val + p.val]? =
      some (q * (ExpanderTables.lookup table (i, p)).1.val +
        (ExpanderTables.lookup table (i, p)).2.val) := by
  simpa only [Nat.add_comm] using ExpanderTableWords.rotationWords_row_order table (i, p)

theorem selected_rotation_div {n q : Nat} (positive : 0 < q)
    (table : ExpanderTables.Table n q) (i : Fin n) (p : Fin q) :
    (q * (ExpanderTables.lookup table (i, p)).1.val +
      (ExpanderTables.lookup table (i, p)).2.val) / q =
        (ExpanderTables.lookup table (i, p)).1.val := by
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ positive,
    Nat.div_eq_of_lt (ExpanderTables.lookup table (i, p)).2.isLt, Nat.zero_add]

theorem selected_rotation_mod {n q : Nat} (_positive : 0 < q)
    (table : ExpanderTables.Table n q) (i : Fin n) (p : Fin q) :
    (q * (ExpanderTables.lookup table (i, p)).1.val +
      (ExpanderTables.lookup table (i, p)).2.val) % q =
        (ExpanderTables.lookup table (i, p)).2.val := by
  rw [Nat.mul_add_mod_self_left,
    Nat.mod_eq_of_lt (ExpanderTables.lookup table (i, p)).2.isLt]

/-- A direct instantiation of the real affine getter on the actual rotor words. -/
theorem rotationLookupTrace {n q : Nat} (table : ExpanderTables.Table n q)
    (i : Fin n) (p : Fin q) (source : K) (tape : Fin 5 → K)
    (distinct : Function.Injective tape) (outside : ∀ a, source ≠ tape a)
    (labels : MachineAffineLookup.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (code : ∀ l, program (labels l) =
      MachineAffineLookup.instruction source tape q p.val labels exit l)
    (base : K → List Bool)
    (tableWord : base (tape 0) = encodeWords (ExpanderTableWords.rotationWords table))
    (scratchEmpty : base (tape 4) = []) (suffix : List Bool)
    (sourceWord : base source = encodeWord i.val ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[MachineAffineLookup.steps
        (ExpanderTableWords.rotationWords table) i.val q p.val]
      (some ⟨some (labels .seed), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), MachineAffineLookup.finalTapes tape base
        (ExpanderTableWords.rotationWords table) (q * i.val + p.val)
        (q * (ExpanderTables.lookup table (i, p)).1.val +
          (ExpanderTables.lookup table (i, p)).2.val)⟩ :=
  MachineAffineLookup.affineLookupTrace source tape distinct outside q p.val labels exit
    program code base _ tableWord scratchEmpty i.val suffix sourceWord _
    (selected_rotation table i p) ambient register

/-- The return port is copied from its physical unary tape before fixed-slope
arithmetic adds the actual selected global target. -/
def finishInstruction (q : Nat) (tape : Fin 8 → K) (labels : FinishLabel → Λ)
    (exit : Option Λ) : FinishLabel → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .seedReturn => MachineUnaryAffineAt.seed (tape 4) 0 (labels .copyReturn)
  | .copyReturn => MachineUnaryAffineAt.scan (tape 2) (tape 3) (tape 4) 1
      (labels .copyReturn) (labels .restoreReturn)
  | .restoreReturn => Reduction.MachineTransfer.loopAt (tape 3) (tape 2) id false
      (labels .restoreReturn) (some (labels .affine))
  | .affine => MachineUnaryAffineAt.scan (tape 1) (tape 3) (tape 4) (q + 1)
      (labels .affine) (labels .restoreTarget)
  | .restoreTarget => Reduction.MachineTransfer.loopAt (tape 3) (tape 1) id false
      (labels .restoreTarget) (some (labels .equality))
  | .equality => pushWord (tape 5) equalityBits.reverse
      (.goto fun _ => labels (.row .relationRead))
  | .row stage => MachineTableRows.routine (finishFields tape) (tape 6) (tape 7) (tape 3)
      (fun l => labels (.row l)) (some (labels .clearReverse)) stage
  | .clearReverse => MachineDrain.drain (tape 4) (labels .clearReverse)
      (some (labels .clearEquality))
  | .clearEquality => MachineDrain.drain (tape 5) (labels .clearEquality) exit

def finishSteps (q x z r outputLength : Nat) : Nat :=
  (2 * (r + 1) + 1) + 2 * (z + 1) + 1 +
    (4 * (x + ((q + 1) * z + r) + equalityBits.length + 2) + 2 * outputLength + 9) +
    (((q + 1) * z + r) + 2) + (equalityBits.length + 1)

/-- Actual final arithmetic, full relation emission, row append and cleanup.
The only changed tape is the accumulated output; both physical target fields
and all metadata are preserved. No execution hypothesis is supplied. -/
theorem finishTrace (q : Nat) (tape : Fin 8 → K) (distinct : Function.Injective tape)
    (labels : FinishLabel → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (code : ∀ l, program (labels l) = finishInstruction q tape labels exit l)
    (base : K → List Bool) (x z r : Nat)
    (tailWord : base (tape 0) = encodeWord x)
    (targetWord : base (tape 1) = encodeWord z)
    (returnWord : base (tape 2) = encodeWord r)
    (scratchEmpty : base (tape 3) = []) (reverseEmpty : base (tape 4) = [])
    (equalityEmpty : base (tape 5) = []) (rowEmpty : base (tape 6) = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[finishSteps q x z r (base (tape 7)).length]
      (some ⟨some (labels .seedReturn), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        Function.update base (tape 7) (base (tape 7) ++ emittedBits q x z r)⟩ := by
  have hd (i j : Fin 8) (h : i ≠ j) : tape i ≠ tape j := fun e => h (distinct e)
  let w := (q + 1) * z + r
  let copied := Function.update base (tape 4) (encodeWord r)
  let computed := Function.update base (tape 4) (encodeWord w)
  let initialized := Function.update computed (tape 5) equalityBits
  let appended := Function.update initialized (tape 7)
    (base (tape 7) ++ emittedBits q x z r)
  let drained := Function.update appended (tape 4) []
  have copyRun : (advance (TM2.step program))^[2 * (r + 1) + 1]
      (some ⟨some (labels .seedReturn), (ambient, register), base⟩) =
      some ⟨some (labels .affine), (ambient, none), copied⟩ := by
    simpa only [copied, Nat.one_mul, Nat.add_zero, reverseEmpty, List.append_nil] using
      MachineUnaryAffineAt.seededAffineTrace (tape 2) (tape 3) (tape 4)
        (hd 2 3 (by decide)) (hd 2 4 (by decide)) (hd 3 4 (by decide)) 1 0
        (labels .seedReturn) (labels .copyReturn) (labels .restoreReturn)
        (some (labels .affine)) program (code .seedReturn) (code .copyReturn)
        (code .restoreReturn) base r [] (by simpa using returnWord) scratchEmpty ambient register
  have affineFrame (u : Nat) :
      MachineUnaryAffineAt.tapes (tape 1) (tape 3) (tape 4) base
        (encodeWord z ++ []) [] (encodeWord u ++ []) =
        Function.update base (tape 4) (encodeWord u) := by
    simp only [List.append_nil]
    rw [← targetWord, ← scratchEmpty]
    simp only [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes, Function.update_eq_self]
  have affineRun : (advance (TM2.step program))^[2 * (z + 1)]
      (some ⟨some (labels .affine), (ambient, none), copied⟩) =
      some ⟨some (labels .equality), (ambient, none), computed⟩ := by
    simpa only [affineFrame, copied, computed, w] using
      MachineUnaryAffineAt.affineTrace (tape 1) (tape 3) (tape 4)
        (hd 1 3 (by decide)) (hd 1 4 (by decide)) (hd 3 4 (by decide)) (q + 1)
        (labels .affine) (labels .restoreTarget) (some (labels .equality)) program
        (code .affine) (code .restoreTarget) base z r [] [] ambient none
  have initRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .equality), (ambient, none), computed⟩) =
      some ⟨some (labels (.row .relationRead)), (ambient, none), initialized⟩ := by
    change some (TM2.stepAux (program (labels .equality)) _ _) = _
    rw [code]
    simp [finishInstruction, stepAux_pushWord, TM2.stepAux, computed, initialized,
      hd 5 4 (by decide), equalityEmpty]
  have hfields : ∀ i, finishFields tape i ≠ tape 6 ∧ finishFields tape i ≠ tape 3 := by
    intro i
    fin_cases i
    all_goals exact ⟨hd _ _ (by decide), hd _ _ (by decide)⟩
  have hbits : MachineTableRows.fieldBits (finishFields tape) initialized =
      emittedBits q x z r := by
    simp [MachineTableRows.fieldBits, initialized, computed, finishFields, tailWord,
      hd 0 4 (by decide), hd 0 5 (by decide), hd 4 5 (by decide), emittedBits, w]
  have hsize : MachineTableRows.fieldSize (finishFields tape) initialized =
      x + w + equalityBits.length + 2 := by
    rw [← MachineTableRows.fieldBits_length, hbits, emittedBits_length]
  have hout : initialized (tape 7) = base (tape 7) := by
    simp [initialized, computed, hd 7 4 (by decide), hd 7 5 (by decide)]
  have rowRun : (advance (TM2.step program))^[
      4 * (x + w + equalityBits.length + 2) + 2 * (base (tape 7)).length + 9]
      (some ⟨some (labels (.row .relationRead)), (ambient, none), initialized⟩) =
      some ⟨some (labels .clearReverse), (ambient, none), appended⟩ := by
    simpa only [hbits, hsize, hout, appended] using
      MachineTableRows.appendTrace (finishFields tape) (tape 6) (tape 7) (tape 3)
        hfields (hd 6 7 (by decide)) (hd 6 3 (by decide)) (hd 7 3 (by decide))
        (fun l => labels (.row l)) (some (labels .clearReverse)) program
        (fun l => code (.row l)) initialized
        (by simp [initialized, computed, hd 6 4 (by decide), hd 6 5 (by decide), rowEmpty])
        (by simp [initialized, computed, hd 3 4 (by decide), hd 3 5 (by decide), scratchEmpty])
        ambient none
  have hreverse : appended (tape 4) = encodeWord w := by
    simp [appended, initialized, computed, hd 4 7 (by decide), hd 4 5 (by decide)]
  have reverseRun : (advance (TM2.step program))^[w + 2]
      (some ⟨some (labels .clearReverse), (ambient, none), appended⟩) =
      some ⟨some (labels .clearEquality), (ambient, none), drained⟩ := by
    have h := MachineDrain.drainTrace (tape 4) (labels .clearReverse)
      (some (labels .clearEquality)) program (code .clearReverse)
      appended (appended (tape 4)) ambient none
    rw [Function.update_eq_self, hreverse, encodeWord_length] at h
    exact h
  have hequality : drained (tape 5) = equalityBits := by
    simp [drained, appended, initialized, hd 5 4 (by decide), hd 5 7 (by decide)]
  have finalFrame : Function.update drained (tape 5) [] =
      Function.update base (tape 7) (base (tape 7) ++ emittedBits q x z r) := by
    funext k
    by_cases h4 : k = tape 4
    · subst k
      simp [drained, hd 4 5 (by decide), hd 4 7 (by decide), reverseEmpty]
    · by_cases h5 : k = tape 5
      · subst k
        simp [hd 5 7 (by decide), equalityEmpty]
      · by_cases h7 : k = tape 7
        · subst k
          simp [drained, appended, h4, h5]
        · simp [drained, appended, initialized, computed, h4, h5, h7]
  have equalityRun : (advance (TM2.step program))^[equalityBits.length + 1]
      (some ⟨some (labels .clearEquality), (ambient, none), drained⟩) =
      some ⟨exit, (ambient, none),
        Function.update base (tape 7) (base (tape 7) ++ emittedBits q x z r)⟩ := by
    have h := MachineDrain.drainTrace (tape 5) (labels .clearEquality) exit program
      (code .clearEquality) drained (drained (tape 5)) ambient none
    rw [Function.update_eq_self, hequality, finalFrame] at h
    exact h
  exact joinTrace (joinTrace (joinTrace (joinTrace (joinTrace
    copyRun affineRun) initRun) rowRun) reverseRun) equalityRun

inductive RotorLabel (q : Nat)
  | lookup (stage : MachineAffineLookup.Label)
  | initialize_ | divide | emit (r : Fin q)
  deriving DecidableEq, Fintype

def rotorInstruction (q : Nat) (positive : 0 < q) (p : Fin q)
    (tape : Fin 8 → K) (labels : RotorLabel q → Λ) (exit : Option Λ) :
    RotorLabel q → TM2.Stmt (Alphabet (K := K)) Λ (MachineFixedDivMod.State σ q)
  | .lookup stage => MachineAffineLookup.instruction (tape 0) (rotorLookupTapes tape)
      q p.val (fun l => labels (.lookup l)) (some (labels .initialize_)) stage
  | .initialize_ => .push (tape 6) (fun _ => false)
      (.push (tape 7) (fun _ => false) (.goto fun _ => labels .divide))
  | .divide => MachineFixedDivMod.scanLoop q positive (tape 4) (tape 6)
      (labels .divide) (fun r => labels (.emit r))
  | .emit r => MachineFixedDivMod.emitter q positive (tape 7) exit r

def rotorFinalTapes {n q : Nat} (table : ExpanderTables.Table n q) (i : Fin n) (p : Fin q)
    (tape : Fin 8 → K) (base : K → List Bool) : K → List Bool :=
  MachineFixedDivMod.unaryTapes (tape 4) (tape 6) (tape 7)
    (MachineAffineLookup.finalTapes (rotorLookupTapes tape) base
      (ExpanderTableWords.rotationWords table) (q * i.val + p.val)
      (q * (ExpanderTables.lookup table (i, p)).1.val +
        (ExpanderTables.lookup table (i, p)).2.val))
    0 (ExpanderTables.lookup table (i, p)).1.val
      (ExpanderTables.lookup table (i, p)).2.val [] [] []

def rotorSteps {n q : Nat} (table : ExpanderTables.Table n q) (i : Fin n) (p : Fin q) : Nat :=
  MachineAffineLookup.steps (ExpanderTableWords.rotationWords table) i.val q p.val +
    1 + (q * (ExpanderTables.lookup table (i, p)).1.val +
      (ExpanderTables.lookup table (i, p)).2.val + 2)

/-- The actual stored reverse row is read and physically divided by the fixed
degree. Both output fields equal the coordinates of the actual table lookup. -/
theorem rotorTrace {n q : Nat} (positive : 0 < q) (table : ExpanderTables.Table n q)
    (i : Fin n) (p : Fin q) (tape : Fin 8 → K) (distinct : Function.Injective tape)
    (labels : RotorLabel q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (MachineFixedDivMod.State σ q))
    (code : ∀ l, program (labels l) = rotorInstruction q positive p tape labels exit l)
    (base : K → List Bool)
    (sourceWord : base (tape 0) = encodeWord i.val)
    (tableWord : base (tape 1) = encodeWords (ExpanderTableWords.rotationWords table))
    (flatEmpty : base (tape 4) = []) (scratchEmpty : base (tape 5) = [])
    (localEmpty : base (tape 6) = []) (returnEmpty : base (tape 7) = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[rotorSteps table i p]
      (some ⟨some (labels (.lookup .seed)),
        ((ambient, MachineFixedDivMod.residue q positive 0), register), base⟩) =
      some ⟨exit, ((ambient, MachineFixedDivMod.residue q positive 0), none),
        rotorFinalTapes table i p tape base⟩ := by
  have hd (a b : Fin 8) (h : a ≠ b) : tape a ≠ tape b := fun e => h (distinct e)
  let a := q * (ExpanderTables.lookup table (i, p)).1.val +
    (ExpanderTables.lookup table (i, p)).2.val
  let looked := MachineAffineLookup.finalTapes (rotorLookupTapes tape) base
    (ExpanderTableWords.rotationWords table) (q * i.val + p.val) a
  let initialized := Function.update (Function.update looked (tape 6) (encodeWord 0))
    (tape 7) (encodeWord 0)
  have lookupRun : (advance (TM2.step program))^[MachineAffineLookup.steps
      (ExpanderTableWords.rotationWords table) i.val q p.val]
      (some ⟨some (labels (.lookup .seed)),
        ((ambient, MachineFixedDivMod.residue q positive 0), register), base⟩) =
      some ⟨some (labels .initialize_),
        ((ambient, MachineFixedDivMod.residue q positive 0), none), looked⟩ := by
    exact rotationLookupTrace table i p (tape 0) (rotorLookupTapes tape)
      (rotorLookupTapes_injective tape distinct) (rotorLookupTapes_outside tape distinct)
      (fun l => labels (.lookup l)) (some (labels .initialize_)) program
      (fun l => code (.lookup l)) base tableWord scratchEmpty []
      (by simpa using sourceWord) (ambient, MachineFixedDivMod.residue q positive 0) register
  have lookedOther (k : Fin 8) (h2 : k ≠ 2) (h3 : k ≠ 3) (h4 : k ≠ 4) :
      looked (tape k) = base (tape k) := by
    exact MachineAffineLookup.finalTapes_other (rotorLookupTapes tape) base
      (ExpanderTableWords.rotationWords table) (q * i.val + p.val) a (tape k)
      (hd k 2 h2) (hd k 3 h3) (hd k 4 h4)
  have lookedFlat : looked (tape 4) = encodeWord a := by
    change MachineAffineLookup.finalTapes (rotorLookupTapes tape) base
      (ExpanderTableWords.rotationWords table) (q * i.val + p.val) a
      (rotorLookupTapes tape 3) = _
    rw [MachineAffineLookup.finalTapes_output]
    change encodeWord a ++ base (tape 4) = _
    rw [flatEmpty, List.append_nil]
  have initRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .initialize_),
        ((ambient, MachineFixedDivMod.residue q positive 0), none), looked⟩) =
      some ⟨some (labels .divide),
        ((ambient, MachineFixedDivMod.residue q positive 0), none), initialized⟩ := by
    change some (TM2.stepAux (program (labels .initialize_)) _ _) = _
    rw [code]
    simp [rotorInstruction, TM2.stepAux, initialized, encodeWord,
      lookedOther 6 (by decide) (by decide) (by decide),
      lookedOther 7 (by decide) (by decide) (by decide),
      hd 7 6 (by decide), localEmpty, returnEmpty]
  have initialFrame : MachineFixedDivMod.unaryTapes (tape 4) (tape 6) (tape 7)
      looked a 0 0 [] [] [] = initialized := by
    simp only [MachineFixedDivMod.unaryTapes, MachineFixedDivMod.tapes,
      MachineCopy.forkTapes, List.append_nil, ← lookedFlat, Function.update_eq_self,
      initialized]
  have finalFrame : MachineFixedDivMod.unaryTapes (tape 4) (tape 6) (tape 7)
      looked 0 (a / q) (a % q) [] [] [] = rotorFinalTapes table i p tape base := by
    dsimp only [a]
    rw [selected_rotation_div positive, selected_rotation_mod positive]
    rfl
  have divideRun : (advance (TM2.step program))^[a + 2]
      (some ⟨some (labels .divide),
        ((ambient, MachineFixedDivMod.residue q positive 0), none), initialized⟩) =
      some ⟨exit, ((ambient, MachineFixedDivMod.residue q positive 0), none),
        rotorFinalTapes table i p tape base⟩ := by
    simpa only [initialFrame, finalFrame] using
      MachineFixedDivMod.divModTrace q positive (tape 4) (tape 6) (tape 7)
        (hd 4 6 (by decide)) (hd 4 7 (by decide)) (hd 6 7 (by decide))
        (labels .divide) (fun r => labels (.emit r)) exit program (code .divide)
        (fun r => code (.emit r)) looked a [] [] [] ambient none
  exact joinTrace (joinTrace lookupRun initRun) divideRun

def selectControl : SelectControl → TM2.Stmt SelectAlphabet SelectLabel (SelectState σ)
  | .compare stage => MachineUnaryLessAt.statement compareSlots
      (fun s => .inr (.compare s)) (some (.inr .choose)) stage
  | .choose => .branch (fun s => s.1.2)
      (.load (fun s => ((s.1.1, false), none))
        (.goto fun _ => .inr (.copy .oldLocal .seed)))
      (.load (fun s => ((s.1.1, false), none))
        (.goto fun _ => .inr (.copy .dummyLocal .seed)))
  | .copy kind .seed => MachineUnaryAffineAt.seed (copyDestination kind) 0
      (.inr (.copy kind .scan))
  | .copy kind .scan => MachineUnaryAffineAt.scan (copySource kind) selectScratch
      (copyDestination kind) 1 (.inr (.copy kind .scan)) (.inr (.copy kind .restore))
  | .copy kind .restore => Reduction.MachineTransfer.loopAt selectScratch (copySource kind)
      id false (.inr (.copy kind .restore)) (some (afterCopy kind))
  | .subtract => MachineUnaryLessAt.scan subtractSlots (.inr .subtract)
      (.inr (.copy .dummyDifference .seed))
  | .add kind .scan => MachineUnaryAffineAt.scan (addSource kind) selectScratch selectOutput 1
      (.inr (.add kind .scan)) (.inr (.add kind .restore))
  | .add kind .restore => Reduction.MachineTransfer.loopAt selectScratch (addSource kind)
      id false (.inr (.add kind .restore)) (some (afterAdd kind))
  | .cleanup i => MachineDrain.drain (cleanupTape i) (.inr (.cleanup i)) (afterCleanup i)

/-- All arithmetic is on extra tapes. The old-dart branch literally contains
the shared selector program, with only static tape, label and state transport. -/
def rawSelectProgram : SelectLabel → TM2.Stmt RawSelectAlphabet SelectLabel (SelectState σ) :=
  MachineStateEquiv.program (selectStateEquiv σ)
    (MachineEmbedding.program (some (.inr (.cleanup 0))) MachineCloudSelect.program
      (fun control => MachineStateEquiv.statement (selectStateEquiv σ).symm
        (MachineAlphabetTransport.statement selectAlphabet_eq.symm (selectControl control))))

def selectProgram : SelectLabel → TM2.Stmt SelectAlphabet SelectLabel (SelectState σ) :=
  MachineAlphabetTransport.program selectAlphabet_eq rawSelectProgram

@[simp] theorem selectProgram_control (l : SelectControl) :
    selectProgram (σ := σ) (.inr l) = selectControl l := by
  change MachineAlphabetTransport.statement selectAlphabet_eq
    (MachineStateEquiv.statement (selectStateEquiv σ)
      (MachineStateEquiv.statement (selectStateEquiv σ).symm
        (MachineAlphabetTransport.statement selectAlphabet_eq.symm (selectControl l)))) = _
  have h := MachineStateEquiv.statement_symm_statement (selectStateEquiv σ).symm
    (MachineAlphabetTransport.statement selectAlphabet_eq.symm (selectControl (σ := σ) l))
  simp only [Equiv.symm_symm] at h
  rw [h]
  exact MachineAlphabetTransport.statement_roundtrip selectAlphabet_eq _

def selectCleanState (ambient : σ) (register : Option Bool) : SelectState σ :=
  (((ambient, .checking), false), register)

/-- One physical strict comparison decides the branch and preserves both
input indices. In particular equality belongs to the dummy branch. -/
theorem selectComparisonTrace (base : SelectTape → List Bool) (j k : Nat)
    (hj : base (.inr .localIndex) = encodeWord j)
    (hk : base (.inr .cloudSize) = encodeWord k)
    (hl : base (.inr .savedLeft) = []) (hr : base (.inr .savedRight) = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step selectProgram))^[MachineUnaryLessAt.steps j k + 1]
      (some ⟨some (.inr (.compare .scan)), selectCleanState ambient register, base⟩) =
      some ⟨some (.inr (.copy (if j < k then .oldLocal else .dummyLocal) .seed)),
        selectCleanState ambient none, base⟩ := by
  have h := MachineUnaryLessAt.lessThanTrace compareSlots
    (fun l => .inr (.compare l)) (some (.inr .choose)) selectProgram
    (fun l => by rw [selectProgram_control]; rfl)
    base j k [] [] (by change base (.inr .localIndex) = _; simpa only [List.append_nil] using hj)
    (by change base (.inr .cloudSize) = _; simpa only [List.append_nil] using hk) hl hr
    (ambient, MachineCloudSelect.Phase.checking) false register
  simp only [selectCleanState]
  rw [Function.iterate_succ_apply', h, advance_some]
  change some (TM2.stepAux (selectProgram (.inr .choose)) _ _) = _
  rw [selectProgram_control]
  by_cases hlt : j < k <;> simp [selectControl, TM2.stepAux, hlt]

/-- Actual preserving unary copy used to construct both the selector query
and the dummy-index operands. -/
theorem selectCopyTrace (kind : SelectCopy) (base : SelectTape → List Bool)
    (a : Nat) (hword : base (copySource kind) = encodeWord a)
    (hscratch : base selectScratch = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step selectProgram))^[2 * (a + 1) + 1]
      (some ⟨some (.inr (.copy kind .seed)), selectCleanState ambient register, base⟩) =
      some ⟨some (afterCopy kind), selectCleanState ambient none,
        Function.update base (copyDestination kind)
          (encodeWord a ++ base (copyDestination kind))⟩ := by
  have h₁ : copySource kind ≠ selectScratch := by cases kind <;> decide
  have h₂ : copySource kind ≠ copyDestination kind := by cases kind <;> decide
  have h₃ : selectScratch ≠ copyDestination kind := by cases kind <;> decide
  simpa only [Nat.one_mul, Nat.add_zero, selectCleanState] using
    MachineUnaryAffineAt.seededAffineTrace (copySource kind) selectScratch (copyDestination kind)
      h₁ h₂ h₃ 1 0 (.inr (.copy kind .seed)) (.inr (.copy kind .scan))
      (.inr (.copy kind .restore)) (some (afterCopy kind)) selectProgram
      (by rw [selectProgram_control]; rfl) (by rw [selectProgram_control]; rfl)
      (by rw [selectProgram_control]; rfl) base a [] (by simpa using hword) hscratch
      ((ambient, MachineCloudSelect.Phase.checking), false) register

/-- The two runtime addends are read physically; no input-dependent offset
is captured by a single finite instruction. -/
theorem selectAddTrace (kind : SelectAdd) (base : SelectTape → List Bool)
    (a b : Nat) (hword : base (addSource kind) = encodeWord a)
    (houtput : base selectOutput = encodeWord b) (hscratch : base selectScratch = [])
    (ambient : σ) :
    (advance (TM2.step selectProgram))^[2 * (a + 1)]
      (some ⟨some (.inr (.add kind .scan)), selectCleanState ambient none, base⟩) =
      some ⟨some (afterAdd kind), selectCleanState ambient none,
        Function.update base selectOutput (encodeWord (a + b))⟩ := by
  have h₁ : addSource kind ≠ selectScratch := by cases kind <;> decide
  have h₂ : addSource kind ≠ selectOutput := by cases kind <;> decide
  have h₃ : selectScratch ≠ selectOutput := by decide
  have frame (n : Nat) : MachineUnaryAffineAt.tapes (addSource kind) selectScratch selectOutput
      base (encodeWord a ++ []) [] (encodeWord n ++ []) =
        Function.update base selectOutput (encodeWord n) := by
    simp only [List.append_nil]
    rw [← hword, ← hscratch]
    simp only [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes, Function.update_eq_self]
  have h := MachineUnaryAffineAt.affineTrace (addSource kind) selectScratch selectOutput
    h₁ h₂ h₃ 1 (.inr (.add kind .scan)) (.inr (.add kind .restore))
    (some (afterAdd kind)) selectProgram
    (by rw [selectProgram_control]; rfl) (by rw [selectProgram_control]; rfl)
    base a b [] [] ((ambient, MachineCloudSelect.Phase.checking), false) none
  rw [frame, frame] at h
  rw [← houtput, Function.update_eq_self] at h
  simpa only [Nat.one_mul, selectCleanState] using h

abbrev CoreState (σ : Type) (q : Nat) :=
  (σ × (MachineFixedBlockMap.Buffer 4096 ×
    (Fin q × (Bool × MachineCloudSelect.Phase)))) × Option Bool

inductive CoreLabel (q : Nat)
  | rotor (stage : RotorLabel q)
  | select (stage : SelectLabel)
  | finish (stage : FinishLabel)
  | cleanup (i : Fin 10)
  deriving DecidableEq, Fintype

def coreEntry (q : Nat) : CoreLabel q := .rotor (.lookup .seed)

/-- The shared cloud-selector trace is preserved exactly by static tape,
register and alphabet transport. These transports add no transition. -/
theorem selectCloudTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (i : Fin (PreprocessingCloudIndex.cloudSize t v))
    (extra : SelectExtraTape → List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step selectProgram))^[MachineCloudSelect.cloudSelectSteps t v i []]
      (some ⟨some (.inl (.inr .initialize_)), selectCleanState ambient register,
        selectToBoolTapes (MachineEmbedding.tapes
          (MachineCloudSelect.memory (GraphTables.tableBits t) []
            (MachineCloudSelect.queryWord v.val i.val []) [] [] [] []) extra)⟩) =
      some ⟨some (.inr (.cleanup 0)), selectCleanState ambient none,
        selectToBoolTapes (MachineEmbedding.tapes
          (MachineCloudSelect.memory (GraphTables.tableBits t) []
            (MachineCloudSelect.queryWord v.val i.val []) [] [] []
            (encodeWord (PreprocessingCloudIndex.cloudSelect t v i).val.val)) extra)⟩ := by
  let source := MachineCloudSelect.program (σ := σ)
  let more := fun c => MachineStateEquiv.statement (selectStateEquiv σ).symm
    (MachineAlphabetTransport.statement selectAlphabet_eq.symm (selectControl (σ := σ) c))
  let caller := MachineEmbedding.program (some (.inr (.cleanup 0))) source more
  let embed := MachineEmbedding.configuration (K := MachineCloudSelect.Tape)
    (Γ := MachineCloudSelect.Alphabet) (σ := MachineCloudSelect.State σ)
    (some (Sum.inr (SelectControl.cleanup 0)) : Option SelectLabel) () extra
  have sourceRun := MachineCloudSelect.cloudSelectTrace t v i [] [] ambient register
  have lifted := liftSuccessfulTrace (TM2.step source) (TM2.step caller) embed
    (MachineEmbedding.step_simulation (some (.inr (.cleanup 0))) () extra source more)
    _ _ _ sourceRun
  have transported := MachineStateEquiv.trace (selectStateEquiv σ) caller _ _ _ lifted
  have boolean := MachineAlphabetTransport.successfulTrace selectAlphabet_eq
    (MachineStateEquiv.program (selectStateEquiv σ) caller) _ _ _ transported
  simp only [embed, MachineCloudSelect.cfg, MachineStateEquiv.configuration, MachineEmbedding.configuration,
    MachineEmbedding.label, selectStateEquiv, List.append_nil,
    MachineAlphabetTransport.configuration_mk, ← selectToBoolTapes_eq] at boolean
  convert boolean using 1 <;> rfl

def selectExtraMemory (j v k offset m : Nat)
    (savedLeft savedRight localWork sizeWork : List Bool) :
    SelectExtraTape → List Bool
  | .localIndex => encodeWord j
  | .owner => encodeWord v
  | .cloudSize => encodeWord k
  | .prefixOffset => encodeWord offset
  | .darts => encodeWord m
  | .savedLeft => savedLeft
  | .savedRight => savedRight
  | .localWork => localWork
  | .sizeWork => sizeWork

def selectMemory (graph : List Bool) (j v k offset m : Nat)
    (query output savedLeft savedRight localWork sizeWork : List Bool) :
    SelectTape → List Bool :=
  selectToBoolTapes (MachineEmbedding.tapes
    (MachineCloudSelect.memory graph [] query [] [] [] output)
    (selectExtraMemory j v k offset m savedLeft savedRight localWork sizeWork))

@[simp] theorem selectMemory_query (graph : List Bool) (j v k o m : Nat)
    (query output a b c d : List Bool) :
    selectMemory graph j v k o m query output a b c d selectQuery = query := rfl

@[simp] theorem selectMemory_output (graph : List Bool) (j v k o m : Nat)
    (query output a b c d : List Bool) :
    selectMemory graph j v k o m query output a b c d selectOutput = output := rfl

@[simp] theorem selectMemory_scratch (graph : List Bool) (j v k o m : Nat)
    (query output a b c d : List Bool) :
    selectMemory graph j v k o m query output a b c d selectScratch = [] := rfl

@[simp] theorem selectMemory_extra (graph : List Bool) (j v k o m : Nat)
    (query output a b c d : List Bool) (z : SelectExtraTape) :
    selectMemory graph j v k o m query output a b c d (.inr z) =
      selectExtraMemory j v k o m a b c d z := rfl

@[simp] theorem update_selectMemory_query (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) selectQuery word =
      selectMemory graph j v k o m word output a b c d := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

@[simp] theorem update_selectMemory_output (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) selectOutput word =
      selectMemory graph j v k o m query word a b c d := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

@[simp] theorem update_selectMemory_local (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) (.inr .localWork) word =
      selectMemory graph j v k o m query output a b word d := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

@[simp] theorem update_selectMemory_size (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) (.inr .sizeWork) word =
      selectMemory graph j v k o m query output a b c word := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

@[simp] theorem update_selectMemory_left (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) (.inr .savedLeft) word =
      selectMemory graph j v k o m query output word b c d := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

@[simp] theorem update_selectMemory_right (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) (.inr .savedRight) word =
      selectMemory graph j v k o m query output a word c d := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

theorem selectCleanupTrace (graph : List Bool) (j v k o m : Nat)
    (query output a b c d : List Bool) (ambient : σ) :
    (advance (TM2.step selectProgram))^[query.length + c.length + d.length + a.length + b.length + 5]
      (some ⟨some (.inr (.cleanup 0)), selectCleanState ambient none,
        selectMemory graph j v k o m query output a b c d⟩) =
      some ⟨none, selectCleanState ambient none,
        selectMemory graph j v k o m [] output [] [] [] []⟩ := by
  have h0 := MachineDrain.drainTrace selectQuery (.inr (.cleanup 0))
    (some (.inr (.cleanup 1))) selectProgram
    (by rw [selectProgram_control]; rfl)
    (selectMemory graph j v k o m query output a b c d) query
    ((ambient, MachineCloudSelect.Phase.checking), false) none
  simp only [update_selectMemory_query] at h0
  have h1 := MachineDrain.drainTrace (.inr .localWork) (.inr (.cleanup 1))
    (some (.inr (.cleanup 2))) selectProgram
    (by rw [selectProgram_control]; rfl)
    (selectMemory graph j v k o m [] output a b c d) c
    ((ambient, MachineCloudSelect.Phase.checking), false) none
  simp only [update_selectMemory_local] at h1
  have h2 := MachineDrain.drainTrace (.inr .sizeWork) (.inr (.cleanup 2))
    (some (.inr (.cleanup 3))) selectProgram
    (by rw [selectProgram_control]; rfl)
    (selectMemory graph j v k o m [] output a b [] d) d
    ((ambient, MachineCloudSelect.Phase.checking), false) none
  simp only [update_selectMemory_size] at h2
  have h3 := MachineDrain.drainTrace (.inr .savedLeft) (.inr (.cleanup 3))
    (some (.inr (.cleanup 4))) selectProgram
    (by rw [selectProgram_control]; rfl)
    (selectMemory graph j v k o m [] output a b [] []) a
    ((ambient, MachineCloudSelect.Phase.checking), false) none
  simp only [update_selectMemory_left] at h3
  have h4 := MachineDrain.drainTrace (.inr .savedRight) (.inr (.cleanup 4))
    none selectProgram (by rw [selectProgram_control]; rfl)
    (selectMemory graph j v k o m [] output [] b [] []) b
    ((ambient, MachineCloudSelect.Phase.checking), false) none
  simp only [update_selectMemory_right] at h4
  have total := joinTrace (joinTrace (joinTrace (joinTrace h0 h1) h2) h3) h4
  have hn : query.length + c.length + d.length + a.length + b.length + 5 =
      ((((query.length + 1) + (c.length + 1)) + (d.length + 1)) + (a.length + 1)) +
        (b.length + 1) := by omega
  rw [hn]
  exact total

def oldSelectSteps (t : GraphTables.Table) (v : Fin t.vertices)
    (i : Fin (PreprocessingCloudIndex.cloudSize t v)) : Nat :=
  (2 * (i.val + 1) + 1) + (2 * (v.val + 1) + 1) +
    MachineCloudSelect.cloudSelectSteps t v i [] + (v.val + i.val + 7)

/-- The dummy branch uses the actual truncating-subtraction scan on copied
operands. The original local index, cloud size, prefix and dart count survive. -/
theorem selectDummyTrace (graph : List Bool) (j v k o m : Nat) (hk : k ≤ j)
    (ambient : σ) :
    (advance (TM2.step selectProgram))^[dummySelectSteps j k o m]
      (some ⟨some (.inr (.copy .dummyLocal .seed)), selectCleanState ambient none,
        selectMemory graph j v k o m [] [] [] [] [] []⟩) =
      some ⟨none, selectCleanState ambient none,
        selectMemory graph j v k o m [] (encodeWord (m + o + (j - k))) [] [] [] []⟩ := by
  have hjcopy := selectCopyTrace .dummyLocal
    (selectMemory graph j v k o m [] [] [] [] [] []) j rfl rfl ambient none
  simp only [copyDestination, afterCopy, selectMemory_extra, selectExtraMemory,
    update_selectMemory_local, List.append_nil] at hjcopy
  have hkcopy := selectCopyTrace .dummySize
    (selectMemory graph j v k o m [] [] [] [] (encodeWord j) []) k rfl rfl ambient none
  simp only [copyDestination, afterCopy, selectMemory_extra, selectExtraMemory,
    update_selectMemory_size, List.append_nil] at hkcopy
  have scanFrame (left right savedLeft savedRight : List Bool) :
      MachineUnaryLessAt.tapes subtractSlots
        (selectMemory graph j v k o m [] [] [] [] [] [])
        left right savedLeft savedRight =
      selectMemory graph j v k o m [] [] savedLeft savedRight left right := by
    simp only [MachineUnaryLessAt.tapes,
      show subtractSlots 0 = .inr .localWork from rfl,
      show subtractSlots 1 = .inr .sizeWork from rfl,
      show subtractSlots 2 = .inr .savedLeft from rfl,
      show subtractSlots 3 = .inr .savedRight from rfl,
      update_selectMemory_local, update_selectMemory_size,
      update_selectMemory_left, update_selectMemory_right]
  have hscan := MachineUnaryLessAt.scanTrace subtractSlots (.inr .subtract)
    (.inr (.copy .dummyDifference .seed)) selectProgram
    (by rw [selectProgram_control]; rfl)
    (selectMemory graph j v k o m [] [] [] [] [] [])
    j k [] [] [] [] (ambient, MachineCloudSelect.Phase.checking) false none
  simp only [List.append_nil, scanFrame, Nat.min_eq_right hk, Nat.sub_eq_zero_of_le hk,
    show ¬ j < k from Nat.not_lt_of_ge hk, decide_false] at hscan
  have hdiffcopy := selectCopyTrace .dummyDifference
    (selectMemory graph j v k o m [] [] (List.replicate k true) (List.replicate k true)
      (encodeWord (j - k)) (encodeWord 0)) (j - k) rfl rfl ambient none
  simp only [copyDestination, afterCopy, selectMemory_output, update_selectMemory_output, List.append_nil] at hdiffcopy
  have hprefix := selectAddTrace .prefixOffset
    (selectMemory graph j v k o m [] (encodeWord (j - k))
      (List.replicate k true) (List.replicate k true) (encodeWord (j - k)) (encodeWord 0))
    o (j - k) rfl rfl rfl ambient
  simp only [afterAdd, update_selectMemory_output] at hprefix
  have hm := selectAddTrace .darts
    (selectMemory graph j v k o m [] (encodeWord (o + (j - k)))
      (List.replicate k true) (List.replicate k true) (encodeWord (j - k)) (encodeWord 0))
    m (o + (j - k)) rfl rfl rfl ambient
  simp only [afterAdd, update_selectMemory_output, ← Nat.add_assoc] at hm
  have hcleanup := selectCleanupTrace graph j v k o m []
    (encodeWord (m + o + (j - k))) (List.replicate k true) (List.replicate k true)
    (encodeWord (j - k)) (encodeWord 0) ambient
  have hcleanSteps : ([] : List Bool).length + (encodeWord (j - k)).length + (encodeWord 0).length +
      (List.replicate k true).length + (List.replicate k true).length + 5 = j + k + 7 := by
    simp only [List.length_nil, encodeWord_length, List.length_replicate]
    omega
  rw [hcleanSteps] at hcleanup
  exact joinTrace (joinTrace (joinTrace (joinTrace (joinTrace (joinTrace
    hjcopy hkcopy) hscan) hdiffcopy) hprefix) hm) hcleanup

def selectionSteps (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (PreprocessingCloudIndex.cloudSize t v + padding v)) : Nat :=
  MachineUnaryLessAt.steps i.val (PreprocessingCloudIndex.cloudSize t v) + 1 +
    if hi : i.val < PreprocessingCloudIndex.cloudSize t v then
      oldSelectSteps t v ⟨i.val, hi⟩
    else dummySelectSteps i.val (PreprocessingCloudIndex.cloudSize t v)
      (PreprocessingPaddingOffsets.offset padding v.val) t.darts

def coreSelectTape : SelectTape → CoreTape
  | .inl (.inl .original) => 0
  | .inl (.inl .work) => 17
  | .inl (.inl .target) => 16
  | .inl (.inl .scratch) => 9
  | .inl (.inl .count) => 18
  | .inl (.inl .spare) => 19
  | .inl (.inr ()) => 15
  | .inr .localIndex => 13
  | .inr .owner => 2
  | .inr .cloudSize => 4
  | .inr .prefixOffset => 5
  | .inr .darts => 6
  | .inr .savedLeft => 20
  | .inr .savedRight => 21
  | .inr .localWork => 22
  | .inr .sizeWork => 23

def coreSelectView : CoreTape → Option SelectTape :=
  ![some (.inl (.inl .original)), none, some (.inr .owner), none,
    some (.inr .cloudSize), some (.inr .prefixOffset), some (.inr .darts), none, none,
    some (.inl (.inl .scratch)), none, none, none, some (.inr .localIndex), none,
    some (.inl (.inr ())), some (.inl (.inl .target)), some (.inl (.inl .work)),
    some (.inl (.inl .count)), some (.inl (.inl .spare)),
    some (.inr .savedLeft), some (.inr .savedRight),
    some (.inr .localWork), some (.inr .sizeWork), none, none, none]

theorem coreSelectView_left (k : SelectTape) : coreSelectView (coreSelectTape k) = some k := by
  cases k with
  | inl k =>
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k; rfl
  | inr k => cases k <;> rfl

theorem coreSelectView_right (j : CoreTape) (k : SelectTape)
    (h : coreSelectView j = some k) : coreSelectTape k = j := by
  fin_cases j <;> simp [coreSelectView] at h
  all_goals subst k; rfl

def coreRotorStateEquiv (σ : Type) (q : Nat) :
    MachineFixedDivMod.State
      ((σ × MachineFixedBlockMap.Buffer 4096) × (Bool × MachineCloudSelect.Phase)) q ≃
        CoreState σ q where
  toFun s := ((s.1.1.1.1, (s.1.1.1.2, (s.1.2, s.1.1.2))), s.2)
  invFun s := ((((s.1.1, s.1.2.1), s.1.2.2.2), s.1.2.2.1), s.2)
  left_inv s := by rcases s with ⟨⟨⟨⟨a,b⟩,⟨c,d⟩⟩,e⟩,f⟩; rfl
  right_inv s := by rcases s with ⟨⟨a,⟨b,⟨c,⟨d,e⟩⟩⟩⟩,f⟩; rfl

def coreSelectStateEquiv (σ : Type) (q : Nat) :
    SelectState (σ × (MachineFixedBlockMap.Buffer 4096 × Fin q)) ≃ CoreState σ q where
  toFun s := ((s.1.1.1.1, (s.1.1.1.2.1, (s.1.1.1.2.2, (s.1.2, s.1.1.2)))), s.2)
  invFun s := ((((s.1.1, (s.1.2.1, s.1.2.2.1)), s.1.2.2.2.2), s.1.2.2.2.1), s.2)
  left_inv s := by rcases s with ⟨⟨⟨⟨a,⟨b,c⟩⟩,d⟩,e⟩,f⟩; rfl
  right_inv s := by rcases s with ⟨⟨a,⟨b,⟨c,⟨d,e⟩⟩⟩⟩,f⟩; rfl

def coreAfterCleanup {q : Nat} (labels : CoreLabel q → Λ) (exit : Option Λ) (i : Fin 10) :
    Option Λ :=
  if h : i.val + 1 < 10 then some (labels (.cleanup ⟨i.val + 1,h⟩)) else exit

/-- The whole internal-row program has only fixed q and p in its code. -/
def coreInstruction (q : Nat) (positive : 0 < q) (p : Fin q)
    (labels : CoreLabel q → Λ) (exit : Option Λ) :
    CoreLabel q → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q)
  | .rotor stage => MachineStateEquiv.statement (coreRotorStateEquiv σ q)
      (rotorInstruction q positive p coreRotorTapes
        (fun l => labels (.rotor l)) (some (labels (.select (.inr (.compare .scan))))) stage)
  | .select stage => MachineCloudPadding.Placement.statement coreSelectTape
      (fun l => labels (.select l)) (some (labels (.finish .seedReturn)))
      (MachineStateEquiv.statement (coreSelectStateEquiv σ q) (selectProgram stage))
  | .finish stage => finishInstruction q coreFinishTapes
      (fun l => labels (.finish l)) (some (labels (.cleanup 0))) stage
  | .cleanup i => MachineDrain.drain (coreCleanupTape i) (labels (.cleanup i))
      (coreAfterCleanup labels exit i)

def coreInitialState (q : Nat) (positive : 0 < q) (ambient : σ) : CoreState σ q :=
  ((ambient, (MachineFixedBlockMap.emptyBuffer 4096,
    (MachineFixedDivMod.residue q positive 0, (false, MachineCloudSelect.Phase.checking)))), none)

def coreMemory (graph : List Bool) (x v i k o m : Nat) (rotor output : List Bool)
    (query scan flat localIndex returnPort selected : List Bool) : CoreTape → List Bool :=
  ![graph, encodeWord x, encodeWord v, encodeWord i, encodeWord k, encodeWord o,
    encodeWord m, rotor, output, [], query, scan, flat, localIndex, returnPort, selected,
    [], [], [], [], [], [], [], [], [], [], []]

@[simp] theorem coreMemory_update_output (graph : List Bool) (x v i k o m : Nat)
    (rotor output query scan flat localIndex returnPort selected newOutput : List Bool) :
    Function.update (coreMemory graph x v i k o m rotor output query scan flat
      localIndex returnPort selected) (8 : CoreTape) newOutput =
      coreMemory graph x v i k o m rotor newOutput query scan flat localIndex returnPort selected := by
  funext z
  fin_cases z <;> rfl

theorem coreRotorTapes_injective : Function.Injective coreRotorTapes := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [coreRotorTapes]

theorem coreFinishTapes_injective : Function.Injective coreFinishTapes := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [coreFinishTapes]

def coreCleaned (base : CoreTape → List Bool) : CoreTape → List Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
      (Function.update base 10 []) 11 []) 12 []) 13 []) 14 []) 15 []) 9 []) 16 []) 17 []) 18 []

def coreCleanupSteps (base : CoreTape → List Bool) : Nat :=
  (base 10).length + (base 11).length + (base 12).length + (base 13).length +
  (base 14).length + (base 15).length + (base 9).length + (base 16).length +
  (base 17).length + (base 18).length + 10

theorem coreCleanupTrace (q : Nat) (positive : 0 < q) (p : Fin q)
    (labels : CoreLabel q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = coreInstruction q positive p labels exit l)
    (base : CoreTape → List Bool)
    (ambient : σ × (MachineFixedBlockMap.Buffer 4096 ×
      (Fin q × (Bool × MachineCloudSelect.Phase)))) :
    (advance (TM2.step program))^[coreCleanupSteps base]
      (some ⟨some (labels (.cleanup 0)), (ambient, none), base⟩) =
      some ⟨exit, (ambient, none), coreCleaned base⟩ := by
  let b1 := Function.update base (10 : CoreTape) []
  have h0 := MachineDrain.drainTrace (10 : CoreTape) (labels (.cleanup 0))
    (some (labels (.cleanup 1))) program (code (.cleanup 0)) base (base 10) ambient none
  rw [Function.update_eq_self] at h0
  let b2 := Function.update b1 (11 : CoreTape) []
  have h1 := MachineDrain.drainTrace (11 : CoreTape) (labels (.cleanup 1))
    (some (labels (.cleanup 2))) program (code (.cleanup 1)) b1 (b1 11) ambient none
  rw [Function.update_eq_self] at h1
  have hw1 : b1 11 = base 11 := by simp [b1]
  rw [hw1] at h1
  let b3 := Function.update b2 (12 : CoreTape) []
  have h2 := MachineDrain.drainTrace (12 : CoreTape) (labels (.cleanup 2))
    (some (labels (.cleanup 3))) program (code (.cleanup 2)) b2 (b2 12) ambient none
  rw [Function.update_eq_self] at h2
  have hw2 : b2 12 = base 12 := by simp [b1, b2]
  rw [hw2] at h2
  let b4 := Function.update b3 (13 : CoreTape) []
  have h3 := MachineDrain.drainTrace (13 : CoreTape) (labels (.cleanup 3))
    (some (labels (.cleanup 4))) program (code (.cleanup 3)) b3 (b3 13) ambient none
  rw [Function.update_eq_self] at h3
  have hw3 : b3 13 = base 13 := by simp [b1, b2, b3]
  rw [hw3] at h3
  let b5 := Function.update b4 (14 : CoreTape) []
  have h4 := MachineDrain.drainTrace (14 : CoreTape) (labels (.cleanup 4))
    (some (labels (.cleanup 5))) program (code (.cleanup 4)) b4 (b4 14) ambient none
  rw [Function.update_eq_self] at h4
  have hw4 : b4 14 = base 14 := by simp [b1, b2, b3, b4]
  rw [hw4] at h4
  let b6 := Function.update b5 (15 : CoreTape) []
  have h5 := MachineDrain.drainTrace (15 : CoreTape) (labels (.cleanup 5))
    (some (labels (.cleanup 6))) program (code (.cleanup 5)) b5 (b5 15) ambient none
  rw [Function.update_eq_self] at h5
  have hw5 : b5 15 = base 15 := by simp [b1, b2, b3, b4, b5]
  rw [hw5] at h5
  let b7 := Function.update b6 (9 : CoreTape) []
  have h6 := MachineDrain.drainTrace (9 : CoreTape) (labels (.cleanup 6))
    (some (labels (.cleanup 7))) program (code (.cleanup 6)) b6 (b6 9) ambient none
  rw [Function.update_eq_self] at h6
  have hw6 : b6 9 = base 9 := by simp [b1, b2, b3, b4, b5, b6]
  rw [hw6] at h6
  let b8 := Function.update b7 (16 : CoreTape) []
  have h7 := MachineDrain.drainTrace (16 : CoreTape) (labels (.cleanup 7))
    (some (labels (.cleanup 8))) program (code (.cleanup 7)) b7 (b7 16) ambient none
  rw [Function.update_eq_self] at h7
  have hw7 : b7 16 = base 16 := by simp [b1, b2, b3, b4, b5, b6, b7]
  rw [hw7] at h7
  let b9 := Function.update b8 (17 : CoreTape) []
  have h8 := MachineDrain.drainTrace (17 : CoreTape) (labels (.cleanup 8))
    (some (labels (.cleanup 9))) program (code (.cleanup 8)) b8 (b8 17) ambient none
  rw [Function.update_eq_self] at h8
  have hw8 : b8 17 = base 17 := by simp [b1, b2, b3, b4, b5, b6, b7, b8]
  rw [hw8] at h8
  let b10 := Function.update b9 (18 : CoreTape) []
  have h9 := MachineDrain.drainTrace (18 : CoreTape) (labels (.cleanup 9))
    exit program (code (.cleanup 9)) b9 (b9 18) ambient none
  rw [Function.update_eq_self] at h9
  have hw9 : b9 18 = base 18 := by simp [b1, b2, b3, b4, b5, b6, b7, b8, b9]
  rw [hw9] at h9
  have total := (joinTrace (joinTrace (joinTrace (joinTrace (joinTrace (joinTrace (joinTrace (joinTrace (joinTrace h0 h1) h2) h3) h4) h5) h6) h7) h8) h9)
  have hn : coreCleanupSteps base =
      (base 10).length + 1 + ((base 11).length + 1) + ((base 12).length + 1) +
      ((base 13).length + 1) + ((base 14).length + 1) + ((base 15).length + 1) +
      ((base 9).length + 1) + ((base 16).length + 1) + ((base 17).length + 1) +
      ((base 18).length + 1) := by unfold coreCleanupSteps; omega
  rw [hn]
  exact total

theorem coreCleaned_memory (graph : List Bool) (x v i k o m : Nat)
    (rotor output query scan flat localIndex returnPort selected : List Bool) :
    coreCleaned (coreMemory graph x v i k o m rotor output query scan flat
      localIndex returnPort selected) =
      coreMemory graph x v i k o m rotor output [] [] [] [] [] [] := by
  funext z
  fin_cases z <;> rfl

theorem coreCleanupSteps_memory (graph : List Bool) (x v i k o m : Nat)
    (rotor output scan : List Bool) (j r z : Nat) :
    coreCleanupSteps (coreMemory graph x v i k o m rotor output
      (encodeWord 0) scan (encodeWord 0) (encodeWord j) (encodeWord r) (encodeWord z)) =
      scan.length + j + r + z + 15 := by
  change (encodeWord 0).length + scan.length + (encodeWord 0).length +
    (encodeWord j).length + (encodeWord r).length + (encodeWord z).length +
    ([] : List Bool).length + ([] : List Bool).length + ([] : List Bool).length +
    ([] : List Bool).length + 10 = _
  simp only [encodeWord_length, List.length_nil]
  omega

theorem coreRotorFinalFrame {n q : Nat} (table : ExpanderTables.Table n q) (i : Fin n) (p : Fin q)
    (graph : List Bool) (x v k o m : Nat) (output : List Bool) :
    rotorFinalTapes table i p coreRotorTapes
      (coreMemory graph x v i.val k o m
        (encodeWords (ExpanderTableWords.rotationWords table)) output [] [] [] [] [] []) =
    coreMemory graph x v i.val k o m
      (encodeWords (ExpanderTableWords.rotationWords table)) output (encodeWord 0)
      (encodeWords ((ExpanderTableWords.rotationWords table).drop (q * i.val + p.val + 1)))
      (encodeWord 0) (encodeWord (ExpanderTables.lookup table (i, p)).1.val)
      (encodeWord (ExpanderTables.lookup table (i, p)).2.val) [] := by
  funext z
  fin_cases z <;>
    simp [rotorFinalTapes, coreRotorTapes, rotorLookupTapes, coreMemory,
      MachineFixedDivMod.unaryTapes, MachineFixedDivMod.tapes, MachineCopy.forkTapes,
      MachineAffineLookup.finalTapes, MachinePreservingLookup.finalTapes, MachineLookup.tapes]

theorem coreRotorTrace {n q : Nat} (positive : 0 < q) (table : ExpanderTables.Table n q)
    (i : Fin n) (p : Fin q) (labels : CoreLabel q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = coreInstruction q positive p labels exit l)
    (graph : List Bool) (x v k o m : Nat) (output : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[rotorSteps table i p]
      (some ⟨some (labels (coreEntry q)), coreInitialState q positive ambient,
        coreMemory graph x v i.val k o m
          (encodeWords (ExpanderTableWords.rotationWords table)) output [] [] [] [] [] []⟩) =
      some ⟨some (labels (.select (.inr (.compare .scan)))), coreInitialState q positive ambient,
        coreMemory graph x v i.val k o m
          (encodeWords (ExpanderTableWords.rotationWords table)) output (encodeWord 0)
          (encodeWords ((ExpanderTableWords.rotationWords table).drop (q * i.val + p.val + 1)))
          (encodeWord 0) (encodeWord (ExpanderTables.lookup table (i, p)).1.val)
          (encodeWord (ExpanderTables.lookup table (i, p)).2.val) []⟩ := by
  let e := coreRotorStateEquiv σ q
  let backwards := MachineStateEquiv.program e.symm program
  have atRotor (l : RotorLabel q) :
      backwards (labels (.rotor l)) = rotorInstruction q positive p coreRotorTapes
        (fun l => labels (.rotor l)) (some (labels (.select (.inr (.compare .scan))))) l := by
    change MachineStateEquiv.statement e.symm (program (labels (.rotor l))) = _
    rw [code]
    exact MachineStateEquiv.statement_symm_statement e _
  have run := rotorTrace positive table i p coreRotorTapes coreRotorTapes_injective
    (fun l => labels (.rotor l)) (some (labels (.select (.inr (.compare .scan)))))
    backwards atRotor
    (coreMemory graph x v i.val k o m
      (encodeWords (ExpanderTableWords.rotationWords table)) output [] [] [] [] [] [])
    rfl rfl rfl rfl rfl rfl
    ((ambient, MachineFixedBlockMap.emptyBuffer 4096), (false, MachineCloudSelect.Phase.checking)) none
  have h := MachineStateEquiv.trace e backwards _ _ _ run
  have backForward : MachineStateEquiv.program e backwards = program := by
    have hp := MachineStateEquiv.program_symm_program e.symm program
    simpa only [Equiv.symm_symm, backwards] using hp
  rw [backForward] at h
  change (advance (TM2.step program))^[rotorSteps table i p]
    (some ⟨some (labels (coreEntry q)), coreInitialState q positive ambient,
      coreMemory graph x v i.val k o m
        (encodeWords (ExpanderTableWords.rotationWords table)) output [] [] [] [] [] []⟩) =
    some ⟨some (labels (.select (.inr (.compare .scan)))), coreInitialState q positive ambient,
      rotorFinalTapes table i p coreRotorTapes
        (coreMemory graph x v i.val k o m
          (encodeWords (ExpanderTableWords.rotationWords table)) output [] [] [] [] [] [])⟩ at h
  rw [coreRotorFinalFrame] at h
  exact h

theorem coreSelectFrame (graph : List Bool) (x v i k o m j : Nat)
    (rotor output query scan flat returnPort selected : List Bool) :
    MachineCloudPadding.Placement.tapes coreSelectView
      (selectMemory graph j v k o m [] selected [] [] [] [])
      (coreMemory graph x v i k o m rotor output query scan flat (encodeWord j) returnPort []) =
      coreMemory graph x v i k o m rotor output query scan flat (encodeWord j) returnPort selected := by
  funext z
  fin_cases z <;> rfl

theorem coreFinishTrace (q : Nat) (positive : 0 < q) (p : Fin q)
    (labels : CoreLabel q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = coreInstruction q positive p labels exit l)
    (graph : List Bool) (x v i k o m j r z : Nat)
    (rotor output query scan flat : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[finishSteps q x z r output.length]
      (some ⟨some (labels (.finish .seedReturn)), coreInitialState q positive ambient,
        coreMemory graph x v i k o m rotor output query scan flat
          (encodeWord j) (encodeWord r) (encodeWord z)⟩) =
      some ⟨some (labels (.cleanup 0)), coreInitialState q positive ambient,
        coreMemory graph x v i k o m rotor (output ++ emittedBits q x z r) query scan flat
          (encodeWord j) (encodeWord r) (encodeWord z)⟩ := by
  have h := finishTrace q coreFinishTapes coreFinishTapes_injective
    (fun l => labels (.finish l)) (some (labels (.cleanup 0))) program
    (fun l => code (.finish l))
    (coreMemory graph x v i k o m rotor output query scan flat
      (encodeWord j) (encodeWord r) (encodeWord z))
    x z r rfl rfl rfl rfl rfl rfl rfl
    (ambient, (MachineFixedBlockMap.emptyBuffer 4096,
      (MachineFixedDivMod.residue q positive 0, (false, MachineCloudSelect.Phase.checking)))) none
  change (advance (TM2.step program))^[finishSteps q x z r output.length]
    (some ⟨some (labels (.finish .seedReturn)), coreInitialState q positive ambient,
      coreMemory graph x v i k o m rotor output query scan flat
        (encodeWord j) (encodeWord r) (encodeWord z)⟩) =
    some ⟨some (labels (.cleanup 0)), coreInitialState q positive ambient,
      Function.update (coreMemory graph x v i k o m rotor output query scan flat
        (encodeWord j) (encodeWord r) (encodeWord z)) (8 : CoreTape)
        (output ++ emittedBits q x z r)⟩ at h
  rw [coreMemory_update_output] at h
  exact h

def coreInputTapes (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PreprocessingCloudIndex.PaddedCloud t padding v)
    (output : List Bool) : CoreTape → List Bool :=
  coreMemory (GraphTables.tableBits t)
    (PreprocessingRegularTables.vertexOrder t padding x.val).val v.val
    (PreprocessingCloudIndex.paddedCloudRank t padding v x).val
    (PreprocessingCloudIndex.cloudSize t v) (PreprocessingPaddingOffsets.offset padding v.val) t.darts
    (encodeWords (ExpanderTableWords.rotationWords (tables v))) output [] [] [] [] [] []

def coreSteps (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PreprocessingCloudIndex.PaddedCloud t padding v)
    (p : Fin q) (outputLength : Nat) : Nat :=
  let rank := PreprocessingCloudIndex.paddedCloudRank t padding v x
  let step := ExpanderTables.lookup (tables v) (rank, p)
  let selected := PreprocessingInternalRows.selectedIndex t padding v step.1
  let suffixBits := encodeWords ((ExpanderTableWords.rotationWords (tables v)).drop
    (q * rank.val + p.val + 1))
  rotorSteps (tables v) rank p + selectionSteps t padding v step.1 +
    finishSteps q (PreprocessingRegularTables.vertexOrder t padding x.val).val
      selected step.2.val outputLength +
    (suffixBits.length + step.1.val + step.2.val + selected + 15)

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

@[simp] theorem update_frame_remaining (a b c d e f g h x : List Bool) :
    Function.update (frame a b c d e f g h) .remaining x =
      frame a b c d e f x h := by
  funext k; cases k <;> rfl
@[simp] theorem update_frame_total (a b c d e f g h x : List Bool) :
    Function.update (frame a b c d e f g h) .total x =
      frame a b c d e f g x := by
  funext k; cases k <;> rfl

variable {σ : Type}

def bodyTime (t : GraphTables.Table) (v : Fin t.vertices) : Nat :=
  MachineCloudPadding.totalTime t v + (MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t v) + 1) +
    (PreprocessingCloudIndex.cloudSize t v + 1) +
      (PreprocessingLevels.boundedLevel (PreprocessingCloudIndex.cloudSize t v) + 1) + 1

def amount (t : GraphTables.Table) (v : Nat) : Nat :=
  if h : v < t.vertices then MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t ⟨v, h⟩) else 0

def cycleTime (t : GraphTables.Table) (v : Nat) : Nat :=
  if h : v < t.vertices then 1 + bodyTime t ⟨v, h⟩ else 0

def sumFrom (t : GraphTables.Table) (v : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => amount t v + sumFrom t (v + 1) n

def loopTime (t : GraphTables.Table) (v : Nat) : Nat → Nat
  | 0 => 2
  | n + 1 => cycleTime t v + loopTime t (v + 1) n

def totalTime (t : GraphTables.Table) (b : Nat) (suffix : List Bool) : Nat :=
  (1 + 2 * ((encodeWord b ++ suffix).length + 1)) + loopTime t 0 b

end UniqueGamesTheorem.Foundations.Complexity.MachineCloudPrefix

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularMetadata
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable
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

inductive Label
  | owner (l : MachineAffineLookup.Label)
  | ownerClearQuery | ownerClearWork
  | copyXFirst | copyXSecond | copyOwnerFirst | copyOwnerSecond | rankInit
  | rank (l : MachineCloudRank.RankLabel)
  | rankClearQuery | rankClearWork | rankClearFuel
  | prefixCode (l : MachineCloudPrefix.Label)
  | prefixClearQuery | prefixClearFuel
  | cloud (l : MachineCloudPadding.Label)
  deriving DecidableEq, Fintype

def prefixTape : MachineCloudPrefix.Tape → Tape
  | .inner .table => .inl 0
  | .inner .query => .inl 9
  | .inner .count => .inl 10
  | .inner .work => .inl 11
  | .inner .scratch => .inl 12
  | .inner .spare => .inl 13
  | .inner .power => .inl 14
  | .inner .level => .inl 15
  | .inner .fuel => .inl 16
  | .inner .product => .inl 17
  | .bound => .inl 2
  | .remaining => .inl 18
  | .total => .inl 5

def cloudTape : MachineCloudPadding.Tape → Tape
  | .table => .inl 0
  | .query => .inl 2
  | .count => .inl 4
  | .work => .inl 9
  | .scratch => .inl 10
  | .spare => .inl 11
  | .power => .inr .padding
  | .level => .inr .level
  | .fuel => .inl 12
  | .product => .inl 13

variable {σ : Type}

def cloudData (t : GraphTables.Table) (v : Fin t.vertices) (data : Data) : Data :=
  { data with
    count := encodeWord (PreprocessingCloudIndex.cloudSize t v)
    padding := encodeWord (MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t v))
    level := encodeWord (PreprocessingLevels.boundedLevel (PreprocessingCloudIndex.cloudSize t v)) }

def prefixData (t : GraphTables.Table) (v : Fin t.vertices) (data : Data) : Data :=
  { data with offset := encodeWord (PreprocessingPaddingOffsets.offset
      (PreprocessingRegularTables.padding t) v.val) }

def prefixSteps (t : GraphTables.Table) (v : Fin t.vertices) : Nat :=
  MachineCloudPrefix.totalTime t v.val [] + (v.val + 2) + 2

def ownerData (t : GraphTables.Table) (e : Fin t.darts) (data : Data) : Data :=
  { data with owner := encodeWord t.rows[e].tail.val }

def ownerRemainder (t : GraphTables.Table) (e : Fin t.darts) : List Bool :=
  encodeWords ((GraphTables.tableWords t).drop (4098 * e.val + 2 + 1))

def ownerSteps (t : GraphTables.Table) (e : Fin t.darts) : Nat :=
  MachineAffineLookup.steps (GraphTables.tableWords t) e.val 4098 2 + 2 +
    ((ownerRemainder t e).length + 1)

def rankData (t : GraphTables.Table) (v : Fin t.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics t) v) (data : Data) : Data :=
  { data with localRank := encodeWord (PreprocessingCloudIndex.cloudRank t v e).val }

def rankRemainder (t : GraphTables.Table)
    (v : Fin t.vertices) (e : DegreeReplacement.Cloud (GraphTables.semantics t) v) : List Bool :=
  encodeWords (((MachineCloudCount.tableRows t).drop e.val.val).flatMap MachineCloudCount.rowWords)

def rankSteps (t : GraphTables.Table) (v : Fin t.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics t) v) : Nat :=
  querySteps v.val e.val.val +
    MachineCloudRank.rankSteps t.vertices t.darts v.val e.val.val (MachineCloudCount.tableRows t) [] +
    ((rankQuery v.val e.val.val).length + 1) + ((rankRemainder t v e).length + 1) + 2

/-- Membership is a statement about the actual stored tail, used only to
identify the numeric answer of the physical rank routine. -/
def originalMember (t : GraphTables.Table) (e : Fin t.darts) :
    DegreeReplacement.Cloud (GraphTables.semantics t) t.rows[e].tail := ⟨e, rfl⟩

def originalData (t : GraphTables.Table) (e : Fin t.darts) (data : Data) : Data :=
  cloudData t t.rows[e].tail (prefixData t t.rows[e].tail
    (rankData t t.rows[e].tail (originalMember t e) (ownerData t e data)))

def totalTime (t : GraphTables.Table) (e : Fin t.darts) : Nat :=
  ownerSteps t e + rankSteps t t.rows[e].tail (originalMember t e) +
    prefixSteps t t.rows[e].tail + MachineCloudPadding.totalTime t t.rows[e].tail

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularMetadata

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachinePaddedOverlayRuntimeLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial bounds for the actual regularization subcalls. These lemmas
bound the established step counts; they do not assume any machine execution. -/
namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularExecutionBounds

open Turing MachineComposition PCP PCP.PreprocessingRegularTables PCP.PreprocessingCloudIndex
open PCP.PreprocessingMachineBounds MachineRegularInternalRow

noncomputable def familyPolynomial : Polynomial Nat :=
  MachinePaddedExpanderFamilyBounds.timePolynomial.comp (Polynomial.X + 1) +
    Polynomial.C (2 * ExpanderFamily.growth) * (Polynomial.X + 1) + 7

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularExecutionBounds

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Materializing a cloud rotor inside the regularization machine

Core tape 4 contains the unary cloud size and core tape 7 receives the complete
forward rotor table. The actual family computation runs on private tapes;
three retained unary words are then physically drained. All other core tapes
are preserved and all private tapes are empty on return.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily

open Turing MachineComposition
open MachineCloudPadding

noncomputable def timePolynomial : Polynomial Nat :=
  MachinePaddedExpanderFamilyBounds.timePolynomial +
    Polynomial.C (2 * PCP.ExpanderFamily.growth) * Polynomial.X + 7

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable

open Turing MachineComposition

/-! The outer construction uses independent finite registers for its existing
subprograms. This transport combines tape placement, an untouched register
frame, and a static register equivalence, without adding any machine steps. -/
namespace Lift

open MachineCloudPadding

variable {K K' Λ Λ' σ τ υ : Type}

variable [DecidableEq K] [DecidableEq K']

theorem stepAux (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Λ → Λ') (exit : Option Λ') (registers : (σ × τ) ≃ υ)
    (ambient : τ) (extra : K' → List Bool)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (state : σ) (source : K → List Bool) :
    TM2.stepAux (statement tape labels exit registers q) (registers (state, ambient))
        (Placement.tapes view source extra) =
      configuration view labels exit registers ambient extra (TM2.stepAux q state source) := by
  rw [statement, MachineStateEquiv.stepAux_transport, MachineStateFrame.frame_stepAux,
    Placement.stepAux_simulation tape view left right]
  rfl

theorem step (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Λ → Λ') (exit : Option Λ') (registers : (σ × τ) ≃ υ)
    (ambient : τ) (extra : K' → List Bool)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (target : Λ' → TM2.Stmt (fun _ : K' => Bool) Λ' υ)
    (code : ∀ l, target (labels l) = statement tape labels exit registers (source l))
    (a b : TM2.Cfg (fun _ : K => Bool) Λ σ) (h : TM2.step source a = some b) :
    TM2.step target (configuration view labels exit registers ambient extra a) =
      some (configuration view labels exit registers ambient extra b) := by
  cases a with
  | mk label state sourceTapes =>
    cases label with
    | none => simp [TM2.step] at h
    | some label =>
      have hb : TM2.stepAux (source label) state sourceTapes = b := Option.some.inj h
      rw [← hb]
      change some (TM2.stepAux (target (labels label)) (registers (state, ambient))
        (Placement.tapes view sourceTapes extra)) = _
      rw [code, stepAux tape view left right]

theorem trace (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Λ → Λ') (exit : Option Λ') (registers : (σ × τ) ≃ υ)
    (ambient : τ) (extra : K' → List Bool)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (target : Λ' → TM2.Stmt (fun _ : K' => Bool) Λ' υ)
    (code : ∀ l, target (labels l) = statement tape labels exit registers (source l))
    (steps : Nat) (a b : TM2.Cfg (fun _ : K => Bool) Λ σ)
    (run : (advance (TM2.step source))^[steps] (some a) = some b) :
    (advance (TM2.step target))^[steps]
      (some (configuration view labels exit registers ambient extra a)) =
      some (configuration view labels exit registers ambient extra b) :=
  liftSuccessfulTrace _ _ _
    (step tape view left right labels exit registers ambient extra source target code) steps a b run

end Lift

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable

end

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

/-- The row subprogram is a static label placement of the checked emitter. -/
def instruction {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt Alphabet Λ (State σ)
  | .affine .seed => MachineUnaryAffineAt.seed 1 q (labels (.affine .scan))
  | .affine .scan => MachineUnaryAffineAt.scan 0 3 1 (q + 1)
      (labels (.affine .scan)) (labels (.affine .restore))
  | .affine .restore => Reduction.MachineTransfer.loopAt 3 0 id false
      (labels (.affine .restore)) (some (labels (.row (MachineDummyRows.start 1))))
  | .row stage => MachineCloudPadding.Placement.statement (id : Tape → Tape)
      (fun l => labels (.row l)) (some (labels .reverse))
      (MachineDummyRows.program 1 stage)
  | .reverse => MachineDrain.drain 1 (labels .reverse) (some (labels .relation))
  | .relation => MachineDrain.drain 2 (labels .relation) exit

/-- The existing one-port emitter executes under the caller's actual labels. -/
theorem rowTraceAt {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (x e : Nat) (output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[MachineDummyRows.steps x e output 1 + 1]
      (some ⟨some (labels (.row (MachineDummyRows.start 1))), (ambient, register),
        MachineDummyRows.initialTapes x e output⟩) =
      some ⟨some (labels .reverse), (ambient, none),
        MachineDummyRows.fieldTapes x (e + 1) (output ++ MachineDummyRows.rowBits x e)⟩ := by
  have run := MachineDummyRows.allTrace 1 x e output ambient register
  have placed := MachineCloudPadding.Placement.trace (id : Tape → Tape) (fun k => some k)
    (fun _ => rfl) (fun _ _ h => (Option.some.inj h).symm)
    (fun l => labels (.row l)) (some (labels .reverse)) (fun _ => [])
    (MachineDummyRows.program 1) program
    (fun l => code (.row l)) _ _ _ run
  have identityTapes (source : Tape → List Bool) :
      MachineCloudPadding.Placement.tapes (fun k : Tape => some k) source
        (fun _ : Tape => []) = source := rfl
  simpa only [MachineCloudPadding.Placement.configuration,
    MachineCloudPadding.Placement.label, identityTapes,
    MachineDummyRows.rowsBits, List.append_nil] using placed

/-- Both cleanup loops pop their entire physical fields. -/
theorem cleanupTraceAt {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (x e : Nat) (output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[
        ((encodeWord e).length + 1) + (MachineDummyRows.trueBits.length + 1)]
      (some ⟨some (labels .reverse), (ambient, register),
        MachineDummyRows.fieldTapes x e output⟩) =
      some ⟨exit, (ambient, none),
        Function.update (Function.update (MachineDummyRows.fieldTapes x e output) 1 []) 2 []⟩ := by
  let base := MachineDummyRows.fieldTapes x e output
  let mid := Function.update base (1 : Tape) []
  have first := MachineDrain.drainTrace (1 : Tape) (labels .reverse)
    (some (labels .relation)) program (code .reverse) base (base 1) ambient register
  have second := MachineDrain.drainTrace (2 : Tape) (labels .relation)
    exit program (code .relation) mid (mid 2) ambient none
  simp only [Function.update_eq_self] at first second
  have hreverse : base 1 = encodeWord e := rfl
  have hrelation : mid 2 = MachineDummyRows.trueBits := by
    simp only [mid, Function.update_of_ne (by decide : (2 : Tape) ≠ 1)]
    rfl
  rw [hreverse] at first
  rw [hrelation] at second
  exact join_trace first second

/-- Exact physical execution; only the accumulated output changes at the boundary. -/
theorem traceAt {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (x : Nat) (base : Tape → List Bool) (input : Input x base)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps q x (base 4)]
      (some ⟨some (labels (.affine .seed)), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), Function.update base 4 (base 4 ++ emittedBits q x)⟩ := by
  have affine := MachineUnaryAffineAt.seededAffineTrace (0 : Tape) 3 1
    (by decide) (by decide) (by decide) (q + 1) q
    (labels (.affine .seed)) (labels (.affine .scan)) (labels (.affine .restore))
    (some (labels (.row (MachineDummyRows.start 1)))) program
    (code (.affine .seed)) (code (.affine .scan)) (code (.affine .restore))
    base x [] (by simpa only [List.append_nil] using input.source)
    input.scratchEmpty ambient register
  simp only [input.reverseEmpty, List.append_nil] at affine
  change (advance (TM2.step program))^[2 * (x + 1) + 1]
    (some ⟨some (labels (.affine .seed)), (ambient, register), base⟩) =
      some ⟨some (labels (.row (MachineDummyRows.start 1))), (ambient, none),
        Function.update base 1 (encodeWord (reverseIndex q x))⟩ at affine
  rw [affine_frame x (reverseIndex q x) base input] at affine
  have row := rowTraceAt q labels exit program code x (reverseIndex q x) (base 4) ambient none
  have clean := cleanupTraceAt q labels exit program code x (reverseIndex q x + 1)
    (base 4 ++ MachineDummyRows.rowBits x (reverseIndex q x)) ambient none
  rw [cleanup_frame x (reverseIndex q x + 1) _ base input] at clean
  exact join_trace (join_trace affine row) clean

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularDummyRow

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOriginalClean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Reusable inherited-row execution with actual cleanup

Five concrete drain loops remove the query delimiter, unread scan suffix,
raw reverse field, computed reverse field, and copied relation. With initially
empty work tapes, the only final tape change is the appended output row. The
index on tape zero and input table on tape one are both preserved.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalClean

open Turing MachineComposition PCP PCP.GraphTables PCP.PreprocessingRegularTables

abbrev State := MachineRegularOriginalRow.State

inductive Label
  | row (label : MachineRegularOriginalRow.Label)
  | query | scan | rawReverse | computedReverse | relation
  deriving DecidableEq, Fintype

def instruction {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt Alphabet Λ (State σ)
  | .row l => MachineRegularOriginalRow.instruction q (fun l => labels (.row l))
      (some (labels .query)) l
  | .query => MachineDrain.drain 2 (labels .query) (some (labels .scan))
  | .scan => MachineDrain.drain 3 (labels .scan) (some (labels .rawReverse))
  | .rawReverse => MachineDrain.drain 4 (labels .rawReverse) (some (labels .computedReverse))
  | .computedReverse => MachineDrain.drain 6 (labels .computedReverse) (some (labels .relation))
  | .relation => MachineDrain.drain 7 (labels .relation) exit

def steps (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) : Nat :=
  MachineRegularOriginalRow.steps q t e base +
    cleanupSteps (MachineRegularOriginalRow.finalTapes q t e base)

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalClean

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularVertexBlock
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable
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

abbrev PortLabel (q : Nat) := Fin q × CoreLabel q

def portEntry (q : Nat) (labels : PortLabel q → Λ) (exit : Option Λ) (k : Nat) :
    Option Λ :=
  if h : k < q then some (labels (⟨k, h⟩, coreEntry q)) else exit

def portInstruction (q : Nat) (positive : 0 < q) (labels : PortLabel q → Λ)
    (exit : Option Λ) (l : PortLabel q) :
    TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q) :=
  coreInstruction q positive l.1 (fun s => labels (l.1, s))
    (portEntry q labels exit (l.1.val + 1)) l.2

def rowBits (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) : List Bool :=
  encodeWords (GraphTables.rowWords (PreprocessingInternalRows.row t padding tables v x p))

def portSteps (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PaddedCloud t padding v) (outputLength : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => portSteps t padding tables v x outputLength k +
      if h : k < q then coreSteps t padding tables v x ⟨k, h⟩
        (outputLength + (portBits (rowBits t padding tables v x) k).length) else 0

def originalTapes : MachineRegularOriginalClean.Tape → CoreTape :=
  ![1, 0, 10, 11, 12, 9, 24, 25, 26, 8]

def originalStateEquiv (σ : Type) (q : Nat) :
    MachineRegularOriginalClean.State (σ × (Fin q × (Bool × MachineCloudSelect.Phase))) ≃
      CoreState σ q where
  toFun s := ((s.1.1.1, (s.1.2, s.1.1.2)), s.2)
  invFun s := (((s.1.1, s.1.2.2), s.1.2.1), s.2)
  left_inv s := by rcases s with ⟨⟨⟨a,b⟩,c⟩,d⟩; rfl
  right_inv s := by rcases s with ⟨⟨a,⟨b,c⟩⟩,d⟩; rfl

def originalCoreInstruction (q : Nat) (labels : MachineRegularOriginalClean.Label → Λ)
    (exit : Option Λ) (l : MachineRegularOriginalClean.Label) :
    TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q) :=
  MachineCloudPadding.Placement.statement originalTapes labels exit
    (MachineStateEquiv.statement (originalStateEquiv σ q)
      (MachineRegularOriginalClean.instruction q id none l))

def originalMemory (graph : List Bool) (x : Nat) (output : List Bool) :
    MachineRegularOriginalClean.Tape → List Bool :=
  ![encodeWord x, graph, [], [], [], [], [], [], [], output]

def dummyTapes : MachineRegularDummyRow.Tape → CoreTape := ![1, 24, 25, 9, 8, 26]

def dummyView : CoreTape → Option MachineRegularDummyRow.Tape :=
  ![none, some 0, none, none, none, none, none, none, some 4, some 3,
    none, none, none, none, none, none, none, none, none, none,
    none, none, none, none, some 1, some 2, some 5]

theorem dummyView_left (k : MachineRegularDummyRow.Tape) :
    dummyView (dummyTapes k) = some k := by fin_cases k <;> rfl

theorem dummyView_right (j : CoreTape) (k : MachineRegularDummyRow.Tape)
    (h : dummyView j = some k) : dummyTapes k = j := by
  fin_cases j <;> simp [dummyView] at h
  all_goals subst k; rfl

def dummyCoreInstruction (q : Nat) (labels : MachineRegularDummyRow.Label → Λ)
    (exit : Option Λ) (l : MachineRegularDummyRow.Label) :
    TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q) :=
  MachineCloudPadding.Placement.statement dummyTapes labels exit
    (MachineRegularDummyRow.instruction q id none l)

theorem dummyFrame (graph : List Bool) (x v i k o m : Nat) (rotor output output' : List Bool) :
    MachineCloudPadding.Placement.tapes dummyView (MachineRegularDummyRow.memory x output')
      (coreMemory graph x v i k o m rotor output [] [] [] [] [] []) =
      coreMemory graph x v i k o m rotor output' [] [] [] [] [] [] := by
  funext j; fin_cases j <;> rfl

theorem dummyCoreTrace (q : Nat) (positive : 0 < q)
    (labels : MachineRegularDummyRow.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = dummyCoreInstruction q labels exit l)
    (graph : List Bool) (x v i k o m : Nat) (rotor output : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[MachineRegularDummyRow.timeBound q x output.length]
      (some ⟨some (labels (.affine .seed)), coreInitialState q positive ambient,
        coreMemory graph x v i k o m rotor output [] [] [] [] [] []⟩) =
      some ⟨exit, coreInitialState q positive ambient,
        coreMemory graph x v i k o m rotor
          (output ++ MachineRegularDummyRow.emittedBits q x) [] [] [] [] [] []⟩ := by
  let state := (ambient, (MachineFixedBlockMap.emptyBuffer 4096,
    (MachineFixedDivMod.residue q positive 0, (false, MachineCloudSelect.Phase.checking))))
  have run := MachineRegularDummyRow.traceAt q id none
    (MachineRegularDummyRow.instruction q id none) (fun _ => rfl) x
    (MachineRegularDummyRow.memory x output) (MachineRegularDummyRow.memory_input x output) state none
  rw [dummyMemory_update] at run
  have placed := MachineCloudPadding.Placement.trace dummyTapes dummyView
    dummyView_left dummyView_right labels exit
    (coreMemory graph x v i k o m rotor output [] [] [] [] [] [])
    (MachineRegularDummyRow.instruction q id none) program code _ _ _ run
  simp only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
    dummyFrame] at placed
  have hs : MachineRegularDummyRow.steps q x output =
      MachineRegularDummyRow.timeBound q x output.length := MachineRegularDummyRow.steps_eq q x output
  change (advance (TM2.step program))^[MachineRegularDummyRow.steps q x output] _ = _ at placed
  rw [hs] at placed
  exact placed

inductive Label (q : Nat)
  | originalPort (l : PortLabel q)
  | dummyPort (l : PortLabel q)
  | original (l : MachineRegularOriginalClean.Label)
  | dummy (l : MachineRegularDummyRow.Label)
  deriving DecidableEq, Fintype

def originalEntry (q : Nat) (positive : 0 < q) : Label q :=
  .originalPort (⟨0, positive⟩, coreEntry q)

def dummyEntry (q : Nat) (positive : 0 < q) : Label q :=
  .dummyPort (⟨0, positive⟩, coreEntry q)

def instruction (q : Nat) (positive : 0 < q) (labels : Label q → Λ) (exit : Option Λ) :
    Label q → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q)
  | .originalPort l => portInstruction q positive (fun p => labels (.originalPort p))
      (some (labels (.original (.row (.lookup .seed))))) l
  | .dummyPort l => portInstruction q positive (fun p => labels (.dummyPort p))
      (some (labels (.dummy (.affine .seed)))) l
  | .original l => originalCoreInstruction q (fun s => labels (.original s)) exit l
  | .dummy l => dummyCoreInstruction q (fun s => labels (.dummy s)) exit l

def oldCloud (t : GraphTables.Table) (padding : Fin t.vertices → Nat) (e : Fin t.darts) :
    PaddedCloud t padding t.rows[e].tail := paddedOld t padding t.rows[e].tail ⟨e, rfl⟩

def originalRowSteps (q : Nat) (t : GraphTables.Table) (e : Fin t.darts) (outputLength : Nat) : Nat :=
  MachineRegularOriginalClean.steps q t e
    (originalMemory (GraphTables.tableBits t) e.val (List.replicate outputLength false))

def originalSteps (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (e : Fin t.darts) (outputLength : Nat) : Nat :=
  portSteps t padding tables t.rows[e].tail (oldCloud t padding e) outputLength q +
    originalRowSteps q t e (outputLength +
      (List.ofFn (rowBits t padding tables t.rows[e].tail (oldCloud t padding e))).flatten.length)

def dummySteps (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (j : Fin (padding v)) (outputLength : Nat) : Nat :=
  portSteps t padding tables v (paddedNew t padding v j) outputLength q +
    MachineRegularDummyRow.timeBound q (vertexOrder t padding (.inr ⟨v, j⟩)).val
      (outputLength + (List.ofFn (rowBits t padding tables v (paddedNew t padding v j))).flatten.length)

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularVertexBlock

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOriginalBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# One actual original-vertex body of regularization

The finite code composes physical metadata preparation, expander-family
materialization, all vertex rows, and seven metadata drain loops. The outer
loop owns the global vertex counter and keeps it unchanged during this body.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable

abbrev CoreState := MachineRegularInternalRow.CoreState Unit internalDegree
abbrev Data := MachineRegularMetadata.Data
abbrev BaseTable := PreprocessingRegularTables.BaseTable

theorem degree_positive : 0 < internalDegree :=
  Nat.mul_pos MachineExpanderFamily.baseDegree_positive MachineExpanderFamily.baseDegree_positive

def vertexSource : MachineRegularVertexBlock.Label internalDegree →
    TM2.Stmt (fun _ : Fin 27 => Bool) (MachineRegularVertexBlock.Label internalDegree) CoreState :=
  MachineRegularVertexBlock.instruction internalDegree degree_positive id none

def coreFrame (data : Data) (i : Fin 27) : List Bool :=
  MachineRegularMetadata.frame data (.inl i)

def emittedBits (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts) : List Bool :=
  PreprocessingRegularWords.originalVertexBits t (padding t) (familyCloudTable H t) e

def vertexSteps (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) : Nat :=
  MachineRegularVertexBlock.originalSteps t (padding t) (familyCloudTable H t) e output.length

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBody

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

noncomputable def timePolynomial : Polynomial Nat :=
  MachineRegularMetadata.timePolynomial + MachineRegularExecutionBounds.familyPolynomial +
    blockPolynomial internalDegree + cleanupPolynomial internalDegree

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBodyBounds

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOwnerProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual dummy-owner body of regularization

The owner is a physically stored unary index. The code computes its cloud
metadata, initializes local index and fuel, skips the family computation when
padding is zero, and otherwise generates one rotor for all dummy vertices of
this owner. Each vertex iteration consumes one fuel bit and increments both
physical vertex indices. The final checked addition and cleanup leave only the
updated global index, prefix, and accumulated output.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable
open PreprocessingRegularLoopWords

abbrev Data := MachineRegularMetadata.Data
abbrev CoreState := MachineRegularOriginalBody.CoreState
abbrev BaseTable := PreprocessingRegularTables.BaseTable

def ownerBits (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices) : List Bool :=
  (List.ofFn (PreprocessingRegularWords.dummyVertexBits t (padding t) (familyCloudTable H t) v)).flatten

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody

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

def dummyBits (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices) :
    Fin (padding t v) → List Bool :=
  PreprocessingRegularWords.dummyVertexBits t (padding t) (familyCloudTable H t) v

def loopSteps (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) : (n : Nat) → n ≤ padding t v → Nat
  | 0, _ => 0
  | n + 1, hn => loopSteps H t v output n (by omega) +
      (1 + MachineRegularVertexBlock.dummySteps t (padding t) (familyCloudTable H t)
        v ⟨n, by omega⟩ (output ++ blocksPrefix (dummyBits H t v) n).length + 1)

theorem ownerBits_zero (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (hp : padding t v = 0) : ownerBits H t v = [] := by
  have hnil : List.ofFn (dummyBits H t v) = [] := by
    apply List.length_eq_zero_iff.mp
    simpa only [List.length_ofFn] using hp
  exact congrArg List.flatten hnil

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

noncomputable def timePolynomial : Polynomial Nat :=
  prePolynomial + MachineRegularExecutionBounds.familyPolynomial + loopPolynomial +
    cleanupPolynomial + 2

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

abbrev Tape := MachineCloudPrefix.Tape ⊕ Extra
abbrev Alphabet (_ : Tape) := Bool

def tableTape : Tape := .inl (.inner .table)
def nTape : Tape := .inl .bound
def queryTape : Tape := .inl (.inner .query)
def fuelTape : Tape := .inl .remaining
def sumTape : Tape := .inl .total
def mTape : Tape := .inr .m
def indexTape : Tape := .inr .index
def workTape : Tape := .inr .work
def scratchTape : Tape := .inr .scratch
def verticesTape : Tape := .inr .vertices
def dartsTape : Tape := .inr .darts
def emitTape : Tape := .inr .emit
def outputTape : Tape := .inr .output

def memory (inner : MachineCloudPrefix.Tape → List Bool)
    (m index work scratch vertices darts emit output : List Bool) : Tape → List Bool
  | .inl k => inner k
  | .inr .m => m
  | .inr .index => index
  | .inr .work => work
  | .inr .scratch => scratch
  | .inr .vertices => vertices
  | .inr .darts => darts
  | .inr .emit => emit
  | .inr .output => output

def frame (t n v f s m i w a N R e o : List Bool) : Tape → List Bool :=
  memory (MachineCloudPrefix.frame t v [] [] [] n f s) m i w a N R e o

@[simp] theorem frame_table (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o tableTape = t := rfl
@[simp] theorem frame_n (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o nTape = n := rfl
@[simp] theorem frame_query (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o queryTape = v := rfl
@[simp] theorem frame_fuel (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o fuelTape = f := rfl
@[simp] theorem frame_sum (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o sumTape = s := rfl
@[simp] theorem frame_m (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o mTape = m := rfl
@[simp] theorem frame_index (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o indexTape = i := rfl
@[simp] theorem frame_work (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o workTape = w := rfl
@[simp] theorem frame_scratch (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o scratchTape = a := rfl
@[simp] theorem frame_vertices (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o verticesTape = N := rfl
@[simp] theorem frame_darts (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o dartsTape = R := rfl
@[simp] theorem frame_emit (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o emitTape = e := rfl
@[simp] theorem frame_output (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o outputTape = o := rfl

@[simp] theorem update_frame_table (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) tableTape x =
      frame x n v f s m i w a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_n (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) nTape x =
      frame t x v f s m i w a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_query (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) queryTape x =
      frame t n x f s m i w a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_fuel (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) fuelTape x =
      frame t n v x s m i w a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_sum (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) sumTape x =
      frame t n v f x m i w a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_m (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) mTape x =
      frame t n v f s x i w a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_index (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) indexTape x =
      frame t n v f s m x w a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_work (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) workTape x =
      frame t n v f s m i x a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_scratch (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) scratchTape x =
      frame t n v f s m i w x N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_vertices (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) verticesTape x =
      frame t n v f s m i w a x R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_darts (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) dartsTape x =
      frame t n v f s m i w a N x e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_emit (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) emitTape x =
      frame t n v f s m i w a N R x o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_output (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) outputTape x =
      frame t n v f s m i w a N R e x := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

def fieldTape : Field → Tape
  | .vertices => nTape
  | .darts => mTape

def lookupSlots (field : Field) : Fin 5 → Tape :=
  ![tableTape, indexTape, workTape, fieldTape field, scratchTape]

def copySource : CopyPhase → Tape
  | .count => mTape
  | .rEmit => dartsTape
  | .nEmit => verticesTape

def copyDestination : CopyPhase → Tape
  | .count => verticesTape
  | .rEmit | .nEmit => emitTape

variable {σ : Type}

def paddingTotal (t : GraphTables.Table) : Nat :=
  PreprocessingPaddingOffsets.offset (PreprocessingRegularTables.padding t) t.vertices

def vertexTotal (t : GraphTables.Table) : Nat :=
  PreprocessingRegularTables.vertexCount t (PreprocessingRegularTables.padding t)

def dartTotal (q : Nat) (t : GraphTables.Table) : Nat := vertexTotal t * (q + 1)

def readTime (t : GraphTables.Table) : Nat :=
  1 + MachinePreservingLookupClean.steps (GraphTables.tableWords t) 0 + 1 +
    MachinePreservingLookupClean.steps (GraphTables.tableWords t) 1 + 1

def computeTime (t : GraphTables.Table) : Nat :=
  (2 * (t.darts + 2) + (paddingTotal t + 1)) + (2 * (vertexTotal t + 1) + 1)

def headerBits (q : Nat) (t : GraphTables.Table) : List Bool :=
  encodeWords [vertexTotal t, dartTotal q t]

def emitTime (q : Nat) (t : GraphTables.Table) (output : List Bool) : Nat :=
  (((2 * (dartTotal q t + 2) + 2 * (vertexTotal t + 2)) +
    (2 * ((headerBits q t).length + output.length) + 3)) + 1) + (t.vertices + 1) + 1

def totalTime (q : Nat) (t : GraphTables.Table) (output : List Bool) : Nat :=
  ((readTime t + MachineCloudPrefix.totalTime t t.vertices []) + computeTime t) + emitTime q t output

end Header

namespace Top

abbrev Data := MachineRegularMetadata.Data
abbrev BaseTable := PreprocessingRegularTables.BaseTable

def oldPrefix (H : BaseTable) (t : GraphTables.Table) (k : Nat) : List Bool :=
  PreprocessingRegularLoopWords.blocksPrefix (MachineRegularOriginalBody.emittedBits H t) k

def ownerPrefix (H : BaseTable) (t : GraphTables.Table) (k : Nat) : List Bool :=
  PreprocessingRegularLoopWords.blocksPrefix (MachineRegularOwnerBody.ownerBits H t) k

def headerOutput (t : GraphTables.Table) : List Bool :=
  Header.headerBits PreprocessingRegularTables.internalDegree t

def oldOutput (H : BaseTable) (t : GraphTables.Table) : List Bool :=
  headerOutput t ++ oldPrefix H t t.darts

def finalOutput (H : BaseTable) (t : GraphTables.Table) : List Bool :=
  oldOutput H t ++ ownerPrefix H t t.vertices

end Top

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularTableBoundsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! A polynomial cap for the actual two regularization loops, their header,
and all seven final drain loops. Per-call sizes include the complete stored
output prefix. -/
namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top

open Turing MachineComposition PCP PreprocessingRegularTables
open PreprocessingRegularBounds PreprocessingMachineBounds


noncomputable def oldLoopPolynomial : Polynomial Nat :=
  Polynomial.X *
    (MachineRegularOriginalBodyBounds.timePolynomial.comp
      (Polynomial.X + regularPolynomial) + 2)

noncomputable def ownerLoopPolynomial : Polynomial Nat :=
  Polynomial.X *
    (MachineRegularOwnerBodyBounds.timePolynomial.comp
      (Polynomial.X + regularPolynomial) + 2)

noncomputable def timePolynomial : Polynomial Nat :=
  Header.timePolynomial internalDegree + oldLoopPolynomial + ownerLoopPolynomial +
    4 * Polynomial.X + 12 +
    Polynomial.C (7 * (ExpanderFamily.growth * (internalDegree + 4) + 4)) *
      (Polynomial.X + 1)

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_PCPSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.PCPSource

open UniqueGamesTheorem.Foundations Target PCP SourceClause
open scoped BigOperators

noncomputable section

def baseDenominator : Nat := 40960 * FinalConstants.walkLength

def sourceDenominator : Nat := 13 * baseDenominator

def sourceGap : ℚ := 1 / (sourceDenominator : ℚ)

theorem baseDenominator_pos : 0 < baseDenominator :=
  Nat.mul_pos (by decide) FinalConstants.walkLength_positive

theorem sourceDenominator_pos : 0 < sourceDenominator :=
  Nat.mul_pos (by decide) baseDenominator_pos

theorem sourceGap_pos : 0 < sourceGap := by
  apply one_div_pos.mpr
  exact_mod_cast sourceDenominator_pos

theorem sourceGap_le_one : sourceGap ≤ 1 := by
  have hden : (0 : ℚ) < sourceDenominator := by exact_mod_cast sourceDenominator_pos
  have hone : (1 : ℚ) ≤ sourceDenominator := by exact_mod_cast sourceDenominator_pos
  exact (div_le_one hden).mpr hone

end
end PerfectCompleteness.PCPSource

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_FiniteListSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FiniteListSampling

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def pairAcceptance (μ : FiniteDistribution A) (ν : FiniteDistribution B)
    (accepts : A → B → Bool) : ℝ :=
  μ.expectation (fun a => ν.probability (accepts a))

end
end PerfectCompleteness.FiniteListSampling

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceOddListsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceOddLists

open SourceClause OddLists
open UniqueGamesTheorem.Foundations.Games

noncomputable section

def alphabetLog (s t : Nat) : ℝ :=
  UniqueGamesTheorem.Foundations.Repetition.logTwo
    ((Fintype.card (OddList s (LeftLabels t)) : ℝ) *
      (Fintype.card (OddList s (RightLabels t)) : ℝ))

end
end PerfectCompleteness.SourceOddLists



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_NormalizationReadMachine
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryFormula.compactLiteral_positive _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_archive _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec.decodeWords_encodeWord _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter.counterTapes_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_current _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_remaining _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.baseAccepts_eq_true_iff _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.card_ClauseContext _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.localConsistent_eq_true_iff _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableWords.decode_rotationWords _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_dart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_vertex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
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

section Placement

variable {K Λ A : Type} [DecidableEq K]

variable (tape : Fin 4 → K) (distinct : Function.Injective tape)
variable (labels : Label → Λ) (exit rejected : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ label, program (labels label) = instruction tape labels exit rejected label)
variable (base : K → List Bool) (ambient : A)

include distinct atLabels

theorem signStep (slot : Fin 3) (sign : Bool) (suffix : List Bool)
    (counter : Counters) (signs : Signs) (register : Option Bool) :
    TM2.step program
      ⟨some (labels (.sign slot)), ((ambient, signs), register),
        tapes tape base (encodeWord (if sign then 1 else 0) ++ suffix) counter⟩ =
      some ⟨afterSign labels exit slot, clean ambient (Function.update signs slot sign),
        tapes tape base suffix counter⟩ := by
  change some (TM2.stepAux (program (labels (.sign slot))) _ _) = _
  rw [atLabels (.sign slot)]
  cases sign <;> cases h : afterSign labels exit slot <;>
    simp [instruction, signInstruction, saveSign, rejectSign, encodeWord,
      TM2.stepAux, exitAt, h, clean, tapes_input tape distinct, update_input tape distinct]

theorem literalTrace {n : Nat} (slot : Fin 3) (literal : Target.Literal n)
    (suffix : List Bool) (counter : Counters) (signs : Signs) (register : Option Bool) :
    (advance (TM2.step program))^[literal.variableIndex.val + 2]
      (some ⟨some (labels (.field slot)), ((ambient, signs), register),
        tapes tape base (encodeWords (literalWords literal) ++ suffix) counter⟩) =
      some ⟨afterSign labels exit slot, clean ambient (Function.update signs slot literal.positive),
        tapes tape base suffix (Function.update counter slot
          (List.replicate literal.variableIndex.val true ++ counter slot))⟩ := by
  have first := fieldTrace tape distinct labels exit rejected program atLabels base ambient
    slot literal.variableIndex.val (encodeWord (if literal.positive then 1 else 0) ++ suffix)
    counter signs register
  have second := signStep tape distinct labels exit rejected program atLabels base ambient
    slot literal.positive suffix
    (Function.update counter slot (List.replicate literal.variableIndex.val true ++ counter slot))
    signs none
  change (advance (TM2.step program))^[1]
    (some ⟨some (labels (.sign slot)), clean ambient signs,
      tapes tape base (encodeWord (if literal.positive then 1 else 0) ++ suffix)
        (Function.update counter slot (List.replicate literal.variableIndex.val true ++ counter slot))⟩) = _
    at second
  have full := joinTrace first second
  simpa only [literalWords, encodeWords, List.append_nil, List.append_assoc,
    Nat.add_assoc] using full

theorem clauseTrace {n : Nat} (clause : Target.Clause n) (suffix : List Bool)
    (signs : Signs) (register : Option Bool) :
    (advance (TM2.step program))^[clause[0].variableIndex.val +
        clause[1].variableIndex.val + clause[2].variableIndex.val + 6]
      (some ⟨some (labels (.field 0)), ((ambient, signs), register),
        tapes tape base (encodeWords (clauseWords clause) ++ suffix) (fun _ => [])⟩) =
      some ⟨exit, clean ambient (clauseSigns clause),
        tapes tape base suffix (clauseCounters clause)⟩ := by
  let counter₀ : Counters := Function.update (fun _ => []) 0
    (List.replicate clause[0].variableIndex.val true)
  let counter₁ : Counters := Function.update counter₀ 1
    (List.replicate clause[1].variableIndex.val true)
  let counter₂ : Counters := Function.update counter₁ 2
    (List.replicate clause[2].variableIndex.val true)
  let signs₀ := Function.update signs 0 clause[0].positive
  let signs₁ := Function.update signs₀ 1 clause[1].positive
  let signs₂ := Function.update signs₁ 2 clause[2].positive
  have counter₀_one : counter₀ 1 = [] := rfl
  have counter₁_two : counter₁ 2 = [] := rfl
  have first := literalTrace tape distinct labels exit rejected program atLabels base ambient
    0 clause[0] (encodeWords (literalWords clause[1]) ++
      (encodeWords (literalWords clause[2]) ++ suffix)) (fun _ => []) signs register
  have second := literalTrace tape distinct labels exit rejected program atLabels base ambient
    1 clause[1] (encodeWords (literalWords clause[2]) ++ suffix) counter₀ signs₀ none
  have third := literalTrace tape distinct labels exit rejected program atLabels base ambient
    2 clause[2] suffix counter₁ signs₁ none
  simp only [counter₀_one, counter₁_two, List.append_nil,
    afterSign_zero, afterSign_one, afterSign_two] at first second third
  have full := joinTrace (joinTrace first second) third
  have counters_eq : counter₂ = clauseCounters clause := by
    funext i
    fin_cases i <;> simp [counter₂, counter₁, counter₀, clauseCounters]
  have signs_eq : signs₂ = clauseSigns clause := by
    funext i
    fin_cases i <;> simp [signs₂, signs₁, signs₀, clauseSigns]
  have htime : (clause[0].variableIndex.val + 2 + (clause[1].variableIndex.val + 2)) +
      (clause[2].variableIndex.val + 2) =
      clause[0].variableIndex.val + clause[1].variableIndex.val + clause[2].variableIndex.val + 6 := by omega
  rw [htime] at full
  change (advance (TM2.step program))^[_]
    (some ⟨some (labels (.field 0)), ((ambient, signs), register),
      tapes tape base (encodeWords (literalWords clause[0]) ++
        (encodeWords (literalWords clause[1]) ++ (encodeWords (literalWords clause[2]) ++ suffix)))
        (fun _ => [])⟩) =
    some ⟨exit, clean ambient signs₂, tapes tape base suffix counter₂⟩ at full
  rw [signs_eq, counters_eq] at full
  simpa only [clauseWords, encodeWords_append, List.append_assoc] using full

end Placement

end PerfectCompleteness.NormalizationReadMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceTupleData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceTupleData


open UniqueGamesTheorem.Foundations Target

variable {width : Nat}

theorem localTape_injective (position : Fin width) : Function.Injective (localTape position) := by
  intro i j same
  fin_cases i <;> fin_cases j <;> simp [localTape] at same ⊢

end PerfectCompleteness.SourceTupleData

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_TerminalCalls
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.TerminalCalls

open RecursiveSpaces DescendantSpaces RecursiveSampler
open scoped BigOperators

universe u w

variable {branch : Nat → Nat} {n m : Nat}

theorem card_step (repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m) :
    Fintype.card (TerminalIndex repeats (.step i p)) =
      (2 * repeats (n + 1)) * Fintype.card (TerminalIndex repeats p) := by
  change Fintype.card ((Fin (repeats (n + 1)) × Bool) × TerminalIndex repeats p) = _
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  exact congrArg (fun a => a * Fintype.card (TerminalIndex repeats p)) (Nat.mul_comm _ _)

theorem card_eq_prod (repeats : Nat → Nat) (p : Path branch n m) :
    Fintype.card (TerminalIndex repeats p) = ∏ h ∈ Finset.Ioc m n, 2 * repeats h := by
  induction p with
  | refl n => simp only [card_refl, Finset.Ioc_self, Finset.prod_empty]
  | step i p ih =>
      rw [card_step, ih, Finset.prod_Ioc_succ_top p.height_le]
      exact Nat.mul_comm _ _

end PerfectCompleteness.TerminalCalls

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_ExactTargetOnlineEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ExactTargetOnlineEncoding

open UniqueGamesTheorem.Foundations.Complexity
open scoped Classical

noncomputable section

theorem encodeWords_flatMap {α : Type*} (xs : List α) (words : α → List Nat) :
    encodeWords (xs.flatMap words) = xs.flatMap (fun x => encodeWords (words x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

end
end PerfectCompleteness.ExactTargetOnlineEncoding

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SignedRuntimeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SignedRuntimeBounds


open CanonicalKeys
open UniqueGamesTheorem.Foundations.Complexity
open scoped BigOperators Classical

noncomputable section

def KeyBound {width : Nat} (T : Nat) (key : Key width) : Prop :=
  key.retained.length ≤ width ∧
    ∀ entry ∈ key.retained, KeyMetadataEncoding.entryID entry.2 ≤ T

def KeysBound {width : Nat} (T : Nat) (keys : List (Key width)) : Prop :=
  ∀ key ∈ keys, KeyBound T key

theorem keysBound_append {width T : Nat} {keys : List (Key width)} {key : Key width}
    (earlier : KeysBound T keys) (last : KeyBound T key) :
    KeysBound T (keys ++ [key]) := by
  intro candidate present
  rcases List.mem_append.mp present with present | present
  · exact earlier candidate present
  · have same : candidate = key := by simpa using present
    simpa only [same] using last

theorem endpoint_budget_le {width T count : Nat} {K : Type} [DecidableEq K]
    (source : Fin width → Fin 6 → K) (base : K → List Bool)
    (earlier : List (Key width)) (key : Key width)
    (sourceBound : CanonicalKeyMachine.sourceLength source base ≤ 4 * width * (T + 1))
    (earlierBound : KeysBound T earlier) (keyBound : KeyBound T key)
    (countBound : earlier.length + 1 ≤ count) :
    CanonicalEndpointMachine.budget source base earlier key ≤
      SignedCostEnvelope.endpointBound width T count := by
  have allBound := keysBound_append earlierBound keyBound
  have payloadBound := CanonicalVertexNames.payload_length_le key T keyBound.1 keyBound.2
  have streamBound :
      (BinaryNameSearch.stream (CanonicalVertexNames.tokens (earlier ++ [key]))).length ≤
        CanonicalDictionaryNames.streamBound width T count := by
    have h := CanonicalVertexNames.stream_length_le (earlier ++ [key]) T
      (fun candidate present => (allBound candidate present).1)
      (fun candidate present => (allBound candidate present).2)
    apply h.trans
    apply Nat.mul_le_mul_left
    simpa only [List.length_append, List.length_singleton] using countBound
  have squareBound := Nat.pow_le_pow_left streamBound 2
  unfold CanonicalEndpointMachine.budget SignedCostEnvelope.endpointBound
  nlinarith

end

end PerfectCompleteness.SignedRuntimeBounds

end OAI
end


