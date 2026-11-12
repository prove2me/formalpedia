-- Prove2me | Definitions.Def_OAIQ252P007
-- name    : OAIQ252P007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T07:38:11.100668+00:00
-- url     : https://prove2.me/theorems/551857da-98b4-4409-8cce-5214420304b2
-- title:
--   Definitions bundle OAIQ252P007 of the split of OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 621 declarations of OpenAI's Lean: 450 definitions, 5 inductive types or structures, 32 instances and 134 theorems. The definitions and types are `OAI.PerfectCompleteness.ChildAssemblyProjection.assembledPullback`, `OAI.PerfectCompleteness.ChildAssemblyProjection.childPullback`, `OAI.PerfectCompleteness.ChildAssemblyProjection.rawPullback`, `OAI.PerfectCompleteness.ChildBilinearCollisionTransfer.ParentForm`, `OAI.PerfectCompleteness.ChildBilinearCollisionTransfer.Raw`, `OAI.PerfectCompleteness.ChildBlockCardinality.allZero`, `OAI.PerfectCompleteness.ChildBlockCardinality.bound`, `OAI.PerfectCompleteness.ChildBlockCardinality.cleanLowerBound`, `OAI.PerfectCompleteness.ChildBlockCardinality.zeroRaw`, `OAI.PerfectCompleteness.ChildBlockContinuation.continuedSpecial`, `OAI.PerfectCompleteness.ChildBlockMixture.mixture`, `OAI.PerfectCompleteness.ChildBlockMixture.reference`, `OAI.PerfectCompleteness.ChildBlockMixture.special`, `OAI.PerfectCompleteness.ChildBlockProjection.liftedLaw`, `OAI.PerfectCompleteness.ChildBlockProjection.mixtureLaw`, `OAI.PerfectCompleteness.ChildBlockProjection.rawPullback`, `OAI.PerfectCompleteness.ChildBlockProjection.replacementLaws`, `OAI.PerfectCompleteness.ChildCallNumbering.Raw`, `OAI.PerfectCompleteness.ChildCallNumbering.equiv`, `OAI.PerfectCompleteness.ChildCallNumbering.pullback`, `OAI.PerfectCompleteness.ChildCallNumberingLaws.liftedLaw`, `OAI.PerfectCompleteness.ChildCallNumberingLaws.mixtureLaw`, `OAI.PerfectCompleteness.ChildCallNumberingLaws.number`, `OAI.PerfectCompleteness.ChildCallNumberingLaws.replacementLaws`, `OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber`, `OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap`, `OAI.PerfectCompleteness.ChildUnmarkedSpace.space`, `OAI.PerfectCompleteness.CleanDecoderContext.CleanChildren`, `OAI.PerfectCompleteness.CleanDecoderContext.Exposed`, `OAI.PerfectCompleteness.CleanDecoderContext.LeftOwn`, `OAI.PerfectCompleteness.CleanDecoderContext.LeftSeed`, `OAI.PerfectCompleteness.CleanDecoderContext.RightOwn`, `OAI.PerfectCompleteness.CleanDecoderContext.RightSeed`, `OAI.PerfectCompleteness.CleanDecoderContext.leftExposed`, `OAI.PerfectCompleteness.CleanDecoderContext.leftForm`, `OAI.PerfectCompleteness.CleanDecoderContext.leftOutput`, `OAI.PerfectCompleteness.CleanDecoderContext.leftSlots`, `OAI.PerfectCompleteness.CleanDecoderContext.lower`, `OAI.PerfectCompleteness.CleanDecoderContext.path`, `OAI.PerfectCompleteness.CleanDecoderContext.rightForm` and 415 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `PerfectCompleteness_Algebra_ChildBilinearCollisionTransfer`, `PerfectCompleteness_Algebra_DecoderRankSplit`, `PerfectCompleteness_Algebra_HierarchicalMatrixTable`, `PerfectCompleteness_Algebra_MatrixTriangularFoldingLemmas`, `PerfectCompleteness_Algebra_TensorBucketEvaluationLemmas`, `PerfectCompleteness_Construction_ChildCallNumbering`, `PerfectCompleteness_Construction_ChildUnmarkedSpace`, `PerfectCompleteness_Construction_CutChildGrouping`, `PerfectCompleteness_Construction_DescendantSpacesLemmas`, `PerfectCompleteness_Construction_HiddenBucketBias`, `PerfectCompleteness_Construction_NativeLeafAlphabet`, `PerfectCompleteness_Construction_OriginalChildScalarAssemblyLemmas`, `PerfectCompleteness_Construction_SourceChildKernelLemmas`, `PerfectCompleteness_Construction_SourceLocalOddLists`, `PerfectCompleteness_Construction_SourceQuestionCutSplit`, `PerfectCompleteness_Construction_SourceQuestionOrderLemmas`, `PerfectCompleteness_Construction_SourceQuestionReconstruction`, `PerfectCompleteness_Decoding_ChildAssemblyProjection`, `PerfectCompleteness_Decoding_ChildBlockProjection`, `PerfectCompleteness_Decoding_CleanDecoderOddLists`, `PerfectCompleteness_Decoding_CleanDecoderRateLemmas`, `PerfectCompleteness_Decoding_CleanDecoderSeedLawLemmas`, `PerfectCompleteness_Decoding_CleanEndpointProjection`, `PerfectCompleteness_Decoding_CleanLeftDecoderLemmas`, `PerfectCompleteness_Decoding_CleanPhysicalDecoderLaw`, `PerfectCompleteness_Decoding_CutProjectionAssembly`, `PerfectCompleteness_Decoding_DecoderContraction`, `PerfectCompleteness_Decoding_DecoderSourcePullback`, `PerfectCompleteness_Decoding_HierarchicalAllDecoderTables`, `PerfectCompleteness_Decoding_HierarchicalDecoderTables`, `PerfectCompleteness_Decoding_HierarchicalLeftDecoder`, `PerfectCompleteness_Decoding_LeftDecoder`, `PerfectCompleteness_Decoding_LowerCutRowsLemmas`, `PerfectCompleteness_Decoding_LowerCutScalar`, `PerfectCompleteness_Decoding_RepresentativeBucketCollisionLemmas`, `PerfectCompleteness_Decoding_RightDecoderLemmas`, `PerfectCompleteness_Foundations_CutCallExtension`, `PerfectCompleteness_Foundations_CutSlotAssembly`, `PerfectCompleteness_Foundations_CutSlotOutside`, `PerfectCompleteness_Foundations_GeometricPathLemmas`, `PerfectCompleteness_Foundations_HierarchicalFrozenTablesLemmas`, `PerfectCompleteness_Foundations_NormalizationLemmas`, `PerfectCompleteness_Foundations_OddListExtraction`, `PerfectCompleteness_Foundations_OriginalTerminalSplitLemmas`, `PerfectCompleteness_Foundations_ProjectedCardinality`, `PerfectCompleteness_Foundations_SourceOddListsLemmas`, `PerfectCompleteness_Foundations_WholeArrayInteriorExteriorLemmas`, `PerfectCompleteness_Foundations_WholeArrayPositiveSplit`, `PerfectCompleteness_Foundations_WholeArraySubtreeSplit`, `PerfectCompleteness_Foundations_WholeCutCallsLemmas`, `PerfectCompleteness_Foundations_WholeCutExteriorTransportLemmas`, `PerfectCompleteness_Foundations_WholeCutGrouping`, `PerfectCompleteness_Foundations_WholeCutReplayKeys`, `PerfectCompleteness_Foundations_WholeCutReplayLemmas`, `PerfectCompleteness_Foundations_WholeReplaySubtreeLemmas`, `PerfectCompleteness_Machines_CleanRecordDecoderInput`, `PerfectCompleteness_Machines_HierarchicalLowerMatrixInput`, `PerfectCompleteness_Machines_OwnInputReferenceLemmas`, `PerfectCompleteness_Repetition_CleanConditioning`, `PerfectCompleteness_Repetition_CleanEndpointSlots`, `PerfectCompleteness_Repetition_CleanNativeReplay`, `PerfectCompleteness_Repetition_CleanPhysicalCanonicalQuery`, `PerfectCompleteness_Repetition_CleanPhysicalReplay`, `PerfectCompleteness_Repetition_CleanRecordChildBlocks`, `PerfectCompleteness_Repetition_CleanRecordObservation`, `PerfectCompleteness_Repetition_CleanTreeFactors`, `PerfectCompleteness_Repetition_CutChildCleanLawLemmas`, `PerfectCompleteness_Sampling_ChildCallNumberingLaws`, `PerfectCompleteness_Sampling_CutSamplerKeyLocalityLemmas`, `PerfectCompleteness_Sampling_CutSamplerRefinement`, `PerfectCompleteness_Sampling_CutSamplerReplayTransportLemmas`, `PerfectCompleteness_Sampling_FilledUniformSampler`, `PerfectCompleteness_Sampling_RecordSeedSamplingLemmas`, `PerfectCompleteness_Sampling_SamplerComposition`, `PerfectCompleteness_Sampling_UniformLatent`, `PerfectCompleteness_Sampling_UniformLatentSupportLemmas`, `PerfectCompleteness_Sampling_WholeArrayHiddenLaw`, `PerfectCompleteness_Sampling_WholeArrayInteriorHiddenLaw`, `PerfectCompleteness_Sampling_WholeCutSampler`.
--
--   **Imports.** It imports the bundles `OAIQ252P003` and `OAIQ252P004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ252P012`, `OAIQ252P013`, `OAIQ252P014` and `OAIQ252P015`; the statements `OAI.PerfectCompleteness.ChildBilinearCollisionTransfer.marked_restricted_le_uniform_full`, `OAI.PerfectCompleteness.ChildFiniteCallCollisionTransfer.marked_restricted_le_uniform_full`, `OAI.PerfectCompleteness.CleanNativeReplay.rightArrays_heq`, `OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.rightKernel_heq`, `OAI.PerfectCompleteness.OwnInputHeavyBounds.heavyList_card_le_of_balanced` and `OAI.PerfectCompleteness.UniformCleanSoundness.source_soundness`; the proofs of `OAI.PerfectCompleteness.ChildBilinearCollisionTransfer.marked_restricted_le_uniform_full`, `OAI.PerfectCompleteness.ChildFiniteCallCollisionTransfer.marked_restricted_le_uniform_full` and `OAI.PerfectCompleteness.UniformCleanSoundness.source_soundness`.
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
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.LinearIndependent.Defs
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
import Definitions.Def_OAIQ252P003
import Definitions.Def_OAIQ252P004

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanConditioning
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CleanConditioning

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open FiniteProduct

noncomputable section

section Product

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

theorem probability_law_all (P : (i : I) → FiniteDistribution (Ω i))
    (event : (i : I) → Ω i → Bool) :
    (law P).probability (allEvent event) = ∏ i, (P i).probability (event i) := by
  classical
  unfold FiniteDistribution.probability law allEvent
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [decide_eq_true_eq]
  exact product_filter (fun i => (P i).weight (x i)) (fun i => event i (x i))

theorem coordinate_probability_positive (P : (i : I) → FiniteDistribution (Ω i))
    (event : (i : I) → Ω i → Bool)
    (positive : 0 < (law P).probability (allEvent event)) (i : I) :
    0 < (P i).probability (event i) := by
  have hne : (P i).probability (event i) ≠ 0 := by
    intro hz
    have hzprod : (∏ j, (P j).probability (event j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hz
    rw [probability_law_all, hzprod] at positive
    exact (lt_irrefl 0) positive
  exact lt_of_le_of_ne ((P i).probability_nonnegative _) hne.symm

end Product


end
end PerfectCompleteness.CleanConditioning

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_DescendantSpacesLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawIndexDecidableEq _root_.OAI.PerfectCompleteness.RecursiveSampler.drawIndexFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.DescendantSpaces

open PointwiseSpaces RecursiveSpaces

universe u w

namespace Path

variable {branch : Nat → Nat} {n m : Nat}

theorem slotEmbedding_injective (p : Path branch n m) :
    Function.Injective p.slotEmbedding := by
  induction p with
  | refl n => exact fun _ _ h => h
  | step i p ih =>
      intro s t h
      exact ih (congrArg Prod.snd h)

end Path

end PerfectCompleteness.DescendantSpaces



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_UniformLatent
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.UniformLatent

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open FiniteProduct CleanConditioning

noncomputable section


variable {S J : Type*} [Fintype S] [Fintype J] [DecidableEq J]
  (Ω : S → J → Type*) [∀ s j, Fintype (Ω s j)] [∀ s j, Nonempty (Ω s j)]

def latentKernel (s : S) : FiniteDistribution (Raw Ω) :=
  (law (fun j => FiniteDistribution.uniform (Ω s j))).pushforward
    (fun x => (⟨s, x⟩ : Raw Ω))

variable [∀ s j, DecidableEq (Ω s j)]


variable {D : Type*} [Fintype D]

def projectedKernel (flag : FiniteDistribution Bool)
    (nonprojected : S → FiniteDistribution D) (s : S) :
    FiniteDistribution (Sum D (Raw Ω)) :=
  flag.mixture (fun b => if b then
    (latentKernel Ω s).pushforward Sum.inr else (nonprojected s).pushforward Sum.inl)


end
end PerfectCompleteness.UniformLatent

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_ProjectedCardinality
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyDomainFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalKeyShape.assignmentEquiv_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.restriction_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.restriction_refl _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_refl _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_step _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_castSucc _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_last _root_.OAI.PerfectCompleteness.HierarchicalArrays.joint_component _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.NodeEmbedding.embed_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.embeddedRows_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.equiv_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.matrix_evaluate _root_.OAI.PerfectCompleteness.NodeEmbedding.rowsEquiv_apply _root_.OAI.PerfectCompleteness.OddListExtraction.form_atom_self _root_.OAI.PerfectCompleteness.OddListExtraction.multiplicationForm_apply _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSampler.combine_zero _root_.OAI.PerfectCompleteness.RecursiveSampler.evaluate_refl _root_.OAI.PerfectCompleteness.RecursiveSampler.evaluate_zeroTape _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.squareProduct_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.actualProjection_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset _root_.OAI.PerfectCompleteness.TreeCanonical.assignmentEquiv_apply _root_.OAI.PerfectCompleteness.UniformChildSum.childSum_apply _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_selected _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ProjectedCardinality

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open TreeSourceSpaces PointwiseSpaces UniformLatent

variable {branch : Nat → Nat} {n t : Nat}

def projectedSlots (ids : RecursiveSpaces.Slots branch n → Fin t → Nat) :
    RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot :=
  fun s k => MixedSupport.Slot.bit (ids s k)

def Factor (square : Bool) (ids : RecursiveSpaces.Slots branch n → Fin t → Nat) : Type :=
  if square then squareSpace (H (projectedSlots ids)) else H (projectedSlots ids)

instance factorFinite (square : Bool)
    (ids : RecursiveSpaces.Slots branch n → Fin t → Nat) : Finite (Factor square ids) := by
  cases square <;> dsimp [Factor] <;> infer_instance

noncomputable instance factorFintype (square : Bool)
    (ids : RecursiveSpaces.Slots branch n → Fin t → Nat) : Fintype (Factor square ids) :=
  Fintype.ofFinite _

noncomputable instance factorDecidableEq (square : Bool)
    (ids : RecursiveSpaces.Slots branch n → Fin t → Nat) : DecidableEq (Factor square ids) :=
  Classical.decEq _

def factorZero (square : Bool) (ids : RecursiveSpaces.Slots branch n → Fin t → Nat) :
    Factor square ids := by
  cases square
  · change H (projectedSlots ids)
    exact 0
  · change squareSpace (H (projectedSlots ids))
    exact 0

instance factorNonempty (square : Bool)
    (ids : RecursiveSpaces.Slots branch n → Fin t → Nat) : Nonempty (Factor square ids) :=
  ⟨factorZero square ids⟩

end PerfectCompleteness.ProjectedCardinality

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanTreeFactors
attribute [-instance] _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanTreeFactors

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces TreeSourceSpaces PointwiseSpaces HierarchicalArrays
open ProjectedCardinality FiniteProduct CleanConditioning

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

abbrev Index (branch : Nat → Nat) (n calls : Nat) (rows : Nat → Nat) :=
  Fin calls ⊕ (Σ node : Nodes branch n, Fin (rows (Nodes.height node)))

def height (calls : Nat) (rows : Nat → Nat) : Index branch n calls rows → Nat
  | .inl _ => n
  | .inr p => Nodes.height p.1

def square (calls : Nat) (rows : Nat → Nat) : Index branch n calls rows → Bool
  | .inl _ => true
  | .inr _ => false

def factorIds (calls : Nat) (rows : Nat → Nat)
    (ids : Slots branch n → Fin t → Nat) :
    (j : Index branch n calls rows) → Slots branch (height calls rows j) → Fin t → Nat
  | .inl _, s, k => ids s k
  | .inr p, s, k => ids ((Nodes.path p.1).slotEmbedding s) k

abbrev Factors (calls : Nat) (rows : Nat → Nat)
    (ids : Slots branch n → Fin t → Nat) (j : Index branch n calls rows) :=
  Factor (square calls rows j) (factorIds calls rows ids j)

abbrev Raw (calls : Nat) (rows : Nat → Nat)
    (ids : Slots branch n → Fin t → Nat) :=
  (Fin calls → squareSpace (H (projectedSlots ids))) × Arrays (projectedSlots ids) rows

def rawEquiv (calls : Nat) (rows : Nat → Nat)
    (ids : Slots branch n → Fin t → Nat) :
    ((j : Index branch n calls rows) → Factors calls rows ids j) ≃ Raw calls rows ids where
  toFun x := (fun q => x (.inl q), fun node row => x (.inr ⟨node, row⟩))
  invFun x j := match j with
    | .inl q => x.1 q
    | .inr p => x.2 p.1 p.2
  left_inv x := by
    funext j
    cases j <;> rfl
  right_inv x := by
    cases x
    rfl

end
end PerfectCompleteness.CleanTreeFactors

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_CutChildGrouping
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutChildGrouping

open scoped BigOperators Classical
open TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {n t : Nat} {C : Type*} [Fintype C]
  (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat)

instance childFintype (i : Fin (branch n)) : Fintype (Child (C := C) slots rows i) :=
  Fintype.ofFinite _

end
end PerfectCompleteness.CutChildGrouping

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_HierarchicalMatrixTable
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalMatrixTable

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (node : Nodes branch n)

def backgroundOf (arrays : Arrays slots rows) : Background (rows := rows) slots node :=
  fun j => arrays j.val

end
end PerfectCompleteness.HierarchicalMatrixTable

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_MatrixTriangularFoldingLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.RepresentativeMatrixTable

noncomputable section

open scoped Classical
open ClauseSupport MixedSupport CanonicalKeys
open DirectionQuotient (F2)

variable {n : Nat} {K Z : Type*} [AddCommGroup K] [Module F2 K]
  (slots : Fin n → Slot) (H : Submodule F2 (Assignment slots → F2))
  (other : Assignment slots → Z) (σ : KeyStrategy.Strategy n)
  (W : Submodule F2 H) (s : (H ⧸ W) →ₗ[F2] H)
  (hs : W.mkQ.comp s = LinearMap.id)

def sideEvaluation (z : Z) : Module.Dual F2 W :=
  if hz : z ∈ Set.range other then
    (EvaluationMatrix.evaluation H (Classical.choose hz)).comp W.subtype
  else 0

def correctionFunctional (z : Z) : Module.Dual F2 H :=
  (sideEvaluation slots H other W z).comp (MatrixRowQuotient.residualVector W s hs)

def partialTable (useful : (Module.Dual F2 (H ⧸ W) →ₗ[F2] K) → Prop)
    (X : Module.Dual F2 (H ⧸ W) →ₗ[F2] K) : Option (K × Z) :=
  if useful X then
    some (CanonicalMatrixTable.response slots H other σ (MatrixRowQuotient.liftMatrix W s X))
  else none

end
end PerfectCompleteness.RepresentativeMatrixTable

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_GeometricPathLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.HierarchicalKnownRows

noncomputable section

open TreeSourceSpaces HierarchicalArrays

variable {branch rows : Nat → Nat} {n t : Nat} {D : Type*}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n)
  (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)
  (descendant : D → {j : Nodes branch n // j ≠ upper})

def knownSpace : Submodule F2 (NodeEmbedding.NumberedDomain slots → F2) :=
  FactoredFunctionsDependent.dependentQuadraticSpan (lower slots upper background descendant)

end
end PerfectCompleteness.HierarchicalKnownRows

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_RecordSeedSamplingLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.RecordSeedSampling

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {X R : Type*} [Fintype X] [Fintype R] [DecidableEq R]
  {Seed : R → Type*} [∀ r, Fintype (Seed r)]

def freshLaw (P : FiniteDistribution X) (record : X → R)
    (kernel : (r : R) → FiniteDistribution (Seed r)) :
    FiniteDistribution (Σ x : X, Seed (record x)) :=
  CompletionSoundness.sigmaLaw P (fun x => kernel (record x))

end
end PerfectCompleteness.RecordSeedSampling



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceQuestionOrderLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.TreeCardinality

open TreeSourceSpaces HierarchicalArrays
open scoped BigOperators

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

def domainBound (branch : Nat → Nat) (n t : Nat) : Nat :=
  (7 ^ t) ^ Fintype.card (RecursiveSpaces.Slots branch n)

def functionBound (branch : Nat → Nat) (n t : Nat) : Nat :=
  2 ^ domainBound branch n t

def arraysBound (branch : Nat → Nat) (n t : Nat) (rows : Nat → Nat) : Nat :=
  ∏ node : Nodes branch n,
    functionBound branch (Nodes.height node) t ^ rows (Nodes.height node)

end
end PerfectCompleteness.TreeCardinality


namespace PerfectCompleteness.ChildBlockCardinality

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

instance rawFintype (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (Raw calls rows slots) := Fintype.ofFinite _

instance rawNonempty (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Nonempty (Raw calls rows slots) := ⟨(fun _ => 0, fun _ _ => 0)⟩

def bound (branch : Nat → Nat) (n t calls : Nat) (rows : Nat → Nat) : Nat :=
  TreeCardinality.functionBound branch n t ^ calls *
    TreeCardinality.arraysBound branch n t rows

end
end PerfectCompleteness.ChildBlockCardinality


namespace PerfectCompleteness.ChildBlockMixture

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

noncomputable section

section General

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]

def reference : FiniteDistribution ((i : I) → Ω i) :=
  FiniteProduct.law (fun i => FiniteDistribution.uniform (Ω i))

def special (Q : (i : I) → FiniteDistribution (Ω i)) (chosen : I) :
    FiniteDistribution ((i : I) → Ω i) :=
  FiniteProduct.law (component Q chosen)

def mixture (Q : (i : I) → FiniteDistribution (Ω i)) :
    FiniteDistribution ((i : I) → Ω i) :=
  HiddenChildMixture.mixture (special Q)

end General

end
end PerfectCompleteness.ChildBlockMixture


namespace PerfectCompleteness.ChildBlockContinuation

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    {T : I → Type*} [∀ i, Fintype (T i)]

def continuedSpecial (Q : (i : I) → T i → FiniteDistribution (Ω i))
    (chosen : I) (t : T chosen) : FiniteDistribution ((i : I) → Ω i) :=
  ChildBlockMixture.special
    (Function.update (fun i => FiniteDistribution.uniform (Ω i)) chosen (Q chosen t))
    chosen

end
end PerfectCompleteness.ChildBlockContinuation

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OddListExtraction
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.OddListExtraction

open scoped BigOperators Classical
open PointwiseSpaces

variable {X Y A B : Type*}

theorem leaf_indicator_mem (branch : Nat → Nat) :
    ∀ (n : Nat) (D : RecursiveSpaces.Slots branch n → Type*)
      (s : RecursiveSpaces.Slots branch n) (a : D s),
      indicator (fun x : RecursiveSpaces.Assignment D => x s) a ∈
        RecursiveSpaces.space F2 branch n D := by
  intro n
  induction n with
  | zero =>
      intro D s a
      exact Submodule.mem_top
  | succ n ih =>
      intro D s a
      rcases s with ⟨i, s⟩
      have h := ih (RecursiveSpaces.childFamily D i) s a
      have hsquare : indicator
          (fun x : RecursiveSpaces.Assignment (RecursiveSpaces.childFamily D i) => x s) a ∈
          squareSpace (RecursiveSpaces.space F2 branch n (RecursiveSpaces.childFamily D i)) := by
        simpa only [indicator_mul_self] using mul_mem_squareSpace _ h h
      exact RecursiveSpaces.child_square_le_space D i (Submodule.mem_map_of_mem hsquare)

theorem source_leaf_indicator_mem {branch : Nat → Nat} {n t : Nat}
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (s : RecursiveSpaces.Slots branch n) (a : TreeSourceSpaces.LeafDomain slots s) :
    indicator (fun x : TreeSourceSpaces.Domain slots => x s) a ∈ TreeSourceSpaces.H slots :=
  leaf_indicator_mem branch n (TreeSourceSpaces.LeafDomain slots) s a

section Form

variable (H : Submodule F2 (X → F2))

noncomputable def formRank (F : H →ₗ[F2] H →ₗ[F2] F2) : Nat :=
  Module.finrank F2 (LinearMap.range F)

end Form

end PerfectCompleteness.OddListExtraction

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_ChildBlockProjection
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.ChildBlockProjection

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  {slots projected : Slots branch n → Fin t → MixedSupport.Slot}

def rawPullback (calls : Nat) (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) :
    ChildBlockCardinality.Raw calls rows projected →ₗ[F2]
      ChildBlockCardinality.Raw calls rows slots where
  toFun block := (fun call => squarePullback p (block.1 call), arraysPullback rows p block.2)
  map_add' a b := by
    apply Prod.ext
    · funext call
      exact map_add (squarePullback p) (a.1 call) (b.1 call)
    · exact map_add (arraysPullback rows p) a.2 b.2
  map_smul' c a := by
    apply Prod.ext
    · funext call
      exact map_smul (squarePullback p) c (a.1 call)
    · exact map_smul (arraysPullback rows p) c a.2

def liftedLaw (calls : Nat) (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) :
    FiniteDistribution (ChildBlockCardinality.Raw calls rows slots) :=
  (FiniteDistribution.uniform (ChildBlockCardinality.Raw calls rows projected)).pushforward
    (rawPullback calls rows p)

instance liftedRangeFintype (calls : Nat) (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) :
    Fintype (LinearMap.range (rawPullback calls rows p)) := Fintype.ofFinite _

def mixtureLaw {Z : Type*} [Fintype Z] (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (projected : Z → Slots branch n → Fin t → MixedSupport.Slot)
    (p : ∀ z s k, MixedSupport.Projection (slots s k) (projected z s k))
    (choiceLaw : FiniteDistribution Z) :
    FiniteDistribution (ChildBlockCardinality.Raw calls rows slots) :=
  choiceLaw.mixture (fun z => liftedLaw calls rows (p z))


variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
  {Z : I → Type*} [∀ i, Fintype (Z i)]

def replacementLaws (calls : Nat) (rows : Nat → Nat)
    (slots : I → Slots branch n → Fin t → MixedSupport.Slot)
    (projected : (i : I) → Z i → Slots branch n → Fin t → MixedSupport.Slot)
    (p : ∀ i z s k, MixedSupport.Projection (slots i s k) (projected i z s k))
    (choiceLaw : (i : I) → FiniteDistribution (Z i)) :
    (i : I) → FiniteDistribution (ChildBlockCardinality.Raw calls rows (slots i)) :=
  fun i => mixtureLaw calls rows (slots i) (projected i) (p i) (choiceLaw i)

end
end PerfectCompleteness.ChildBlockProjection

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_ChildAssemblyProjection
attribute [-instance] _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ChildAssemblyProjection

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  {slots projected : Slots branch (n + 1) → Fin t → MixedSupport.Slot}

variable {C : Type*} [Fintype C]

def childPullback (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (i : Fin (branch n)) :
    CutChildGrouping.Child (C := C) projected rows i →ₗ[F2]
      CutChildGrouping.Child (C := C) slots rows i where
  toFun block :=
    (fun call => ChildBlockProjection.squarePullback (childProjection p i) (block.1 call),
      ChildBlockProjection.arraysPullback rows (childProjection p i) block.2)
  map_add' a b := by
    apply Prod.ext
    · funext call
      exact map_add (ChildBlockProjection.squarePullback (childProjection p i))
        (a.1 call) (b.1 call)
    · exact map_add (ChildBlockProjection.arraysPullback rows (childProjection p i)) a.2 b.2
  map_smul' c a := by
    apply Prod.ext
    · funext call
      exact map_smul (ChildBlockProjection.squarePullback (childProjection p i)) c (a.1 call)
    · exact map_smul (ChildBlockProjection.arraysPullback rows (childProjection p i)) c a.2

def rawPullback (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) :
    CutChildGrouping.Raw (C := C) projected rows →ₗ[F2]
      CutChildGrouping.Raw (C := C) slots rows where
  toFun block i := childPullback rows p i (block i)
  map_add' a b := by
    funext i
    exact map_add (childPullback rows p i) (a i) (b i)
  map_smul' c a := by
    funext i
    exact map_smul (childPullback rows p i) c (a i)

def assembledPullback (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) :
    CutChildGrouping.Assembled (C := C) projected rows →ₗ[F2]
      CutChildGrouping.Assembled (C := C) slots rows where
  toFun z := (fun call => HPullback p (z.1 call),
    fun i => ChildBlockProjection.arraysPullback rows (childProjection p i) (z.2 i))
  map_add' a b := by
    apply Prod.ext
    · funext call
      exact map_add (HPullback p) (a.1 call) (b.1 call)
    · funext i
      exact map_add (ChildBlockProjection.arraysPullback rows (childProjection p i)) (a.2 i) (b.2 i)
  map_smul' c a := by
    apply Prod.ext
    · funext call
      exact map_smul (HPullback p) c (a.1 call)
    · funext i
      exact map_smul (ChildBlockProjection.arraysPullback rows (childProjection p i)) c (a.2 i)

end
end PerfectCompleteness.ChildAssemblyProjection

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_ChildUnmarkedSpace
attribute [-instance] _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.squareProduct_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ChildUnmarkedSpace

open RecursiveSpaces TreeSourceSpaces PointwiseSpaces
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

def childMap (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (i : Fin (branch n)) : squareSpace (H (childSlots slots i)) →ₗ[F2] H slots where
  toFun v := ⟨PointwiseSpaces.pullback F2 (restrictChild slots i) v.val,
    child_square_le_H slots i (Submodule.mem_map_of_mem v.property)⟩
  map_add' v w := by apply Subtype.ext; rfl
  map_smul' c v := by apply Subtype.ext; rfl

@[simp] theorem childMap_apply
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (i : Fin (branch n)) (v : squareSpace (H (childSlots slots i))) (x : Domain slots) :
    (childMap slots i v).val x = v.val (restrictChild slots i x) := rfl

def space (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (mask : Fin (branch n) → Bool) : Submodule F2 (H slots) :=
  ⨆ i, ⨆ (_ : mask i = false), LinearMap.range (childMap slots i)

end
end PerfectCompleteness.ChildUnmarkedSpace

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_ChildBilinearCollisionTransfer
attribute [-instance] _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ChildBilinearCollisionTransfer

noncomputable section

open scoped Classical
open RecursiveSpaces TreeSourceSpaces PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n t : Nat}

abbrev ParentForm (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :=
  H slots →ₗ[F2] H slots →ₗ[F2] F2

abbrev Raw (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :=
  (i : Fin (branch n)) → ChildBlockCardinality.Raw calls rows (childSlots slots i)

end
end PerfectCompleteness.ChildBilinearCollisionTransfer

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceOddListsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceOddLists

open SourceClause OddLists
open UniqueGamesTheorem.Foundations.Games

noncomputable section

def tupleLaw (m t : Nat) [NeZero m] : FiniteDistribution (Occurrences m t) :=
  (FiniteDistribution.uniform (Occurrence m)).iid t

end
end PerfectCompleteness.SourceOddLists



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_NormalizationLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryFormula.compactLiteral_positive _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_variable_count _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftKeys_length _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_accepts _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightKeys_length _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.actualProjection_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightEquiv_apply _root_.OAI.PerfectCompleteness.SourceGame.questionGame_success _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_variables _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_current _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_remaining _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.Normalization

open UniqueGamesTheorem.Foundations
open Target
open SourceClause

def normalizedTriple {n : Nat} (a b c : Fin n) (sa sb sc : Bool)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : NormalizedClause n where
  clause := tripleClause a b c sa sb sc
  distinct := by
    intro i j h
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hi with rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl <;>
      simp_all [tripleClause]

def mainClause (F : Formula) (c : Fin F.clauses.length) :
    NormalizedClause (outputVariables F) :=
  normalizedTriple (copyVariable F c 0) (copyVariable F c 1) (copyVariable F c 2)
    (PCP.clauseAt F c)[0].positive (PCP.clauseAt F c)[1].positive
    (PCP.clauseAt F c)[2].positive
    (copy_ne_copy F c (by decide)) (copy_ne_copy F c (by decide))
    (copy_ne_copy F c (by decide))

def equalityClauses (F : Formula) (c : Fin F.clauses.length) (i : Fin 3) :
    List (NormalizedClause (outputVariables F)) :=
  let x := copyVariable F c i
  let v := oldVariable F (PCP.clauseAt F c)[i].variableIndex
  let z := paddingVariable F c
  let hxv := copy_ne_old F c i (PCP.clauseAt F c)[i].variableIndex
  let hxz := copy_ne_padding F c i
  let hvz := old_ne_padding F c (PCP.clauseAt F c)[i].variableIndex
  [normalizedTriple x v z false true true hxv hxz hvz,
   normalizedTriple x v z false true false hxv hxz hvz,
   normalizedTriple x v z true false true hxv hxz hvz,
   normalizedTriple x v z true false false hxv hxz hvz]

def gadget (F : Formula) (c : Fin F.clauses.length) :
    List (NormalizedClause (outputVariables F)) :=
  [mainClause F c] ++ equalityClauses F c 0 ++
    equalityClauses F c 1 ++ equalityClauses F c 2

@[simp] theorem equalityClauses_length (F : Formula) (c : Fin F.clauses.length)
    (i : Fin 3) : (equalityClauses F c i).length = 4 := rfl

@[simp] theorem gadget_length (F : Formula) (c : Fin F.clauses.length) :
    (gadget F c).length = 13 := by simp [gadget]

end PerfectCompleteness.Normalization



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_OriginalChildScalarAssemblyLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.ChildBlockCardinality


open RecursiveSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {n t calls : Nat} {rows : Nat → Nat}
    {slots : Slots branch n → Fin t → MixedSupport.Slot}

def zeroRaw (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) : Raw calls rows slots :=
  (fun _ => 0, fun _ _ => 0)

def allZero (x : Raw calls rows slots) : Bool := by
  classical
  exact decide ((∀ q, x.1 q = 0) ∧ ∀ node row, x.2 node row = 0)

def cleanLowerBound (branch : Nat → Nat) (n t calls : Nat) (rows : Nat → Nat) : ℝ :=
  1 / (bound branch n t calls rows : ℝ)

end
end PerfectCompleteness.ChildBlockCardinality


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeCutCallsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BucketUniform.evaluateLinear_apply _root_.OAI.PerfectCompleteness.BucketUsefulCollision.fill_self _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_refl _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_refl_right _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_step _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.WholeCutCalls

open RecursiveSpaces DescendantSpaces TerminalCalls
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m : Nat}

def Index (rows repeats : Nat → Nat) : {n m : Nat} → Path branch n m → Type
  | m, _, .refl _ => Fin (rows m)
  | n + 1, _, .step i p =>
      (BucketSampler.Direction (rows (n + 1)) × TerminalIndex repeats (.step i p)) ⊕
        Index rows repeats p

instance indexFintype (rows repeats : Nat → Nat) (p : Path branch n m) :
    Fintype (Index rows repeats p) := by
  induction p with
  | refl m => exact inferInstanceAs (Fintype (Fin (rows m)))
  | @step n m i p ih =>
      letI : Fintype (Index rows repeats p) := ih
      exact inferInstanceAs (Fintype
        ((BucketSampler.Direction (rows (n + 1)) × TerminalIndex repeats (.step i p)) ⊕
          Index rows repeats p))

def directRow (rows repeats : Nat → Nat) : {n m : Nat} → (p : Path branch n m) →
    Fin (rows m) → Index rows repeats p
  | _, _, .refl _, q => q
  | _, _, .step _ p, q => Sum.inr (directRow rows repeats p q)

theorem directRow_injective (rows repeats : Nat → Nat) (p : Path branch n m) :
    Function.Injective (directRow rows repeats p) := by
  induction p with
  | refl m => exact fun _ _ h => h
  | step i p ih =>
      intro a b h
      exact ih (Sum.inr.inj h)

theorem direction_card (ℓ : Nat) :
    Fintype.card (BucketSampler.Direction ℓ) = 2 ^ ℓ - 1 := by
  have h : 2 ^ ℓ = 1 + Fintype.card (BucketSampler.Direction ℓ) := by
    simpa [BucketSampler.Direction, BucketSampler.F2] using
      Fintype.sum_eq_add_sum_subtype_ne (fun _ : Fin ℓ → BucketSampler.F2 => (1 : Nat)) 0
  omega

@[simp] theorem card_refl (rows repeats : Nat → Nat) :
    Fintype.card (Index (branch := branch) rows repeats (.refl m)) = rows m := by
  exact Fintype.card_fin (rows m)

end
end PerfectCompleteness.WholeCutCalls



namespace PerfectCompleteness.OriginalCutCalls

open RecursiveSpaces DescendantSpaces TerminalCalls
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m : Nat}

def Index (rows repeats : Nat → Nat) : {n m : Nat} → Path branch n m → Type
  | m, _, .refl _ => BucketSampler.Direction (rows m)
  | n + 1, _, .step i p =>
      (BucketSampler.Direction (rows (n + 1)) × TerminalIndex repeats (.step i p)) ⊕
        Index rows repeats p

instance indexFintype (rows repeats : Nat → Nat) (p : Path branch n m) :
    Fintype (Index rows repeats p) := by
  induction p with
  | refl m => exact inferInstanceAs (Fintype (BucketSampler.Direction (rows m)))
  | @step n m i p ih =>
      letI : Fintype (Index rows repeats p) := ih
      exact inferInstanceAs (Fintype
        ((BucketSampler.Direction (rows (n + 1)) × TerminalIndex repeats (.step i p)) ⊕
          Index rows repeats p))

@[simp] theorem card_refl (rows repeats : Nat → Nat) :
    Fintype.card (Index (branch := branch) rows repeats (.refl m)) = 2 ^ rows m - 1 :=
  WholeCutCalls.direction_card (rows m)

end
end PerfectCompleteness.OriginalCutCalls

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceQuestionReconstruction
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceQuestionReconstruction

open SourceClause SourceKeys

noncomputable section

variable {I E Q : Type*} {Leaf : I → Type*}
  (designated : (i : I) → Leaf i) (clean : I → Prop) [DecidablePred clean]
  [∀ i, DecidableEq (Leaf i)]


variable {v m t : Nat}
  (clauses : Fin m → NormalizedClause v)

def rightTuple (projected : Bool) (e : SourceTuple m t) : Fin t → Endpoint v m :=
  fun k => if projected then .variable (occurrenceVariable clauses (e k)) else .clause (e k).1

def reconstructRight (projected : I → Bool)
    (visible : Visible (E := SourceTuple m t) designated clean)
    (own : {i : I // clean i} → Fin t → Fin v) :
    (i : I) → Leaf i → Fin t → Endpoint v m :=
  reconstruct designated clean (fun i => rightTuple clauses (projected i)) visible
    (fun i k => .variable (own i k))

theorem reconstructRight_eq (projected : I → Bool)
    (clean_projected : ∀ i, clean i → projected i = true)
    (x : (i : I) → Leaf i → SourceTuple m t) :
    reconstructRight designated clean clauses projected (reveal designated clean x)
      (fun i k => occurrenceVariable clauses (x i.1 (designated i.1) k)) =
        fun i s => rightTuple clauses (projected i) (x i s) := by
  have hown : (fun (i : {i : I // clean i}) k =>
      Endpoint.variable (m := m) (occurrenceVariable clauses (x i.1 (designated i.1) k))) =
      (fun (i : {i : I // clean i}) =>
        rightTuple clauses (projected i.1) (x i.1 (designated i.1))) := by
    funext i k
    simp only [rightTuple, clean_projected i.1 i.2, ite_true, if_true]
  unfold reconstructRight
  rw [hown]
  exact reconstruct_eq designated clean (fun i => rightTuple clauses (projected i)) x

end
end PerfectCompleteness.SourceQuestionReconstruction

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CutChildCleanLawLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CutChildCleanLaw

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces TreeSourceSpaces PointwiseSpaces HierarchicalArrays ProjectedCardinality

noncomputable section

variable {branch : Nat → Nat} {n t : Nat} {C : Type*} [Fintype C]
  (rows : Nat → Nat) (ids : Slots branch n → Fin t → Nat)

abbrev Raw :=
  (C → squareSpace (H (projectedSlots ids))) × Arrays (projectedSlots ids) rows

def rawEquiv : Raw (C := C) rows ids ≃ CleanTreeFactors.Raw (Fintype.card C) rows ids where
  toFun x := (fun q => x.1 ((Fintype.equivFin C).symm q), x.2)
  invFun x := (fun q => x.1 (Fintype.equivFin C q), x.2)
  left_inv x := by
    apply Prod.ext
    · funext q
      exact congrArg x.1 ((Fintype.equivFin C).symm_apply_apply q)
    · rfl
  right_inv x := by
    apply Prod.ext
    · funext q
      exact congrArg x.1 ((Fintype.equivFin C).apply_symm_apply q)
    · rfl


end
end PerfectCompleteness.CutChildCleanLaw



namespace PerfectCompleteness.UniformCleanSources

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open FiniteProduct CleanConditioning SelectedSources UniformLatent

noncomputable section

attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]
  {E R J D : I → Type*}
  [∀ i, Fintype (E i)] [∀ i, Fintype (R i)] [∀ i, Fintype (J i)] [∀ i, Fintype (D i)]
  [∀ i, DecidableEq (E i)] [∀ i, DecidableEq (R i)]
  [∀ i, DecidableEq (J i)] [∀ i, DecidableEq (D i)]
  (Ω : (i : I) → (E i × R i) → J i → Type*)
  [∀ i s j, Fintype (Ω i s j)] [∀ i s j, Nonempty (Ω i s j)]
  [∀ i s j, DecidableEq (Ω i s j)]

def childKernel (flag : (i : I) → FiniteDistribution Bool)
    (nonprojected : (i : I) → E i × R i → FiniteDistribution (D i))
    (i : I) (e : E i) (r : R i) : FiniteDistribution (ChildRaw (D := D) Ω i) :=
  projectedKernel (Ω i) (flag i) (nonprojected i) (e, r)

def childrenLaw (μ : (i : I) → FiniteDistribution (E i))
    (ν : (i : I) → FiniteDistribution (R i))
    (flag : (i : I) → FiniteDistribution Bool)
    (nonprojected : (i : I) → E i × R i → FiniteDistribution (D i)) :
    FiniteDistribution ((i : I) → E i × (R i × ChildRaw (D := D) Ω i)) :=
  law (fun i => kernelJoint (μ i) (fun e =>
    kernelJoint (ν i) (childKernel Ω flag nonprojected i e)))

end
end PerfectCompleteness.UniformCleanSources



namespace PerfectCompleteness.CleanSourceRecord

open scoped Classical
open SourceQuestionReconstruction

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Leaf : I → Type*} [∀ i, Fintype (Leaf i)] [∀ i, DecidableEq (Leaf i)]
  (designated : (i : I) → Leaf i) {m t : Nat}

def assemble (i : I) (e : SourceTuple m t) (r : Rest designated (m := m) (t := t) i) :
    Leaf i → SourceTuple m t :=
  (Equiv.piSplitAt (designated i) (fun _ : Leaf i => SourceTuple m t)).symm (e, r)

omit [Fintype I] [DecidableEq I] [∀ index, Fintype (Leaf index)] in
@[simp] theorem assemble_designated (i : I) (e : SourceTuple m t)
    (r : Rest designated (m := m) (t := t) i) :
    assemble designated i e r (designated i) = e := by
  simp [assemble, Equiv.piSplitAt]

omit [Fintype I] [DecidableEq I] [∀ index, Fintype (Leaf index)] in
@[simp] theorem assemble_other (i : I) (e : SourceTuple m t)
    (r : Rest designated (m := m) (t := t) i) (leaf : {leaf : Leaf i // leaf ≠ designated i}) :
    assemble designated i e r leaf.val = r leaf := by
  simp [assemble, Equiv.piSplitAt, leaf.property]

variable {J D : I → Type*}
  [∀ i, Fintype (J i)] [∀ i, Fintype (D i)]
  [∀ i, DecidableEq (J i)] [∀ i, DecidableEq (D i)]
  (Ω : (i : I) → (SourceTuple m t × Rest designated (m := m) (t := t) i) → J i → Type*)
  [∀ i q j, Fintype (Ω i q j)] [∀ i q j, Nonempty (Ω i q j)]
  [∀ i q j, DecidableEq (Ω i q j)]

abbrev Sample := (i : I) → SourceTuple m t ×
  (Rest designated (m := m) (t := t) i × UniformCleanSources.ChildRaw (D := D) Ω i)

abbrev Record := (i : I) → UniformCleanSources.Record (D := D) Ω i

def clean (record : Record (D := D) designated Ω) (i : I) : Prop :=
  UniformCleanSources.cleanRecord Ω (record i) = true

def sourceTree (x : Sample (D := D) designated Ω) : (i : I) → Leaf i → SourceTuple m t :=
  fun i => assemble designated i (x i).1 (x i).2.1

omit [∀ index, Fintype (J index)] [∀ index, Fintype (D index)]
  [∀ index, DecidableEq (J index)] [∀ index, DecidableEq (D index)]
  [∀ index seed coord, Fintype (Ω index seed coord)]
  [∀ index seed coord, Nonempty (Ω index seed coord)]
  [∀ index seed coord, DecidableEq (Ω index seed coord)] in
omit [Fintype I] [DecidableEq I] [∀ index, Fintype (Leaf index)] in
@[simp] theorem sourceTree_designated (x : Sample (D := D) designated Ω) (i : I) :
    sourceTree designated Ω x i (designated i) = (x i).1 :=
  assemble_designated designated i _ _

def visible (record : Record (D := D) designated Ω) :
    Visible (E := SourceTuple m t) designated (clean designated Ω record) :=
  fun i leaf =>
    match hrecord : record i with
    | .inl x => assemble designated i x.1 x.2.1 leaf.val
    | .inr r => r ⟨leaf.val, by
        intro heq
        apply leaf.property
        exact ⟨by simp only [clean, hrecord, UniformCleanSources.cleanRecord], heq⟩⟩

def rawProjected (i : I) : UniformCleanSources.ChildRaw (D := D) Ω i → Bool
  | .inl _ => false
  | .inr _ => true

def projected (record : Record (D := D) designated Ω) (i : I) : Bool :=
  match record i with
  | .inl x => rawProjected designated Ω i x.2.2
  | .inr _ => true

omit [Fintype I] [DecidableEq I] [∀ index, Fintype (Leaf index)]
  [∀ index, DecidableEq (Leaf index)]
  [∀ index, Fintype (J index)] [∀ index, Fintype (D index)]
  [∀ index, DecidableEq (J index)] [∀ index, DecidableEq (D index)]
  [∀ index seed coord, Fintype (Ω index seed coord)]
  [∀ index seed coord, Nonempty (Ω index seed coord)]
  [∀ index seed coord, DecidableEq (Ω index seed coord)] in
theorem clean_projected (record : Record (D := D) designated Ω) (i : I)
    (hc : clean designated Ω record i) : projected designated Ω record i = true := by
  cases hrecord : record i with
  | inl x => simp only [clean, hrecord, UniformCleanSources.cleanRecord, Bool.false_eq_true] at hc
  | inr r => simp only [projected, hrecord]

variable (zero : (i : I) → (q : SourceTuple m t × Rest designated (m := m) (t := t) i) →
  (j : J i) → Ω i q j)

omit [DecidableEq I] [∀ index, Fintype (D index)]
  [∀ index, DecidableEq (J index)] [∀ index, DecidableEq (D index)]
  [∀ index seed coord, Fintype (Ω index seed coord)]
  [∀ index seed coord, Nonempty (Ω index seed coord)] in
theorem observation_eq (record : Record (D := D) designated Ω) (x : Sample (D := D) designated Ω)
    (hevent : UniformCleanSources.recordEvent (D := D) Ω zero record x = true) (i : I) :
    SelectedSources.childObservation (UniformCleanSources.childClean (D := D) Ω zero i) (x i) =
      record i := by
  have hall : ∀ j, UniformCleanSources.rowEvent (D := D) Ω zero record j (x j) = true := by
    simpa only [UniformCleanSources.recordEvent, CleanConditioning.allEvent, decide_eq_true_eq] using hevent
  simpa only [UniformCleanSources.rowEvent, decide_eq_true_eq] using hall i

omit [DecidableEq I] [∀ index, Fintype (D index)]
  [∀ index, DecidableEq (J index)] [∀ index, DecidableEq (D index)]
  [∀ index seed coord, Fintype (Ω index seed coord)]
  [∀ index seed coord, Nonempty (Ω index seed coord)] in
theorem visible_eq_reveal (record : Record (D := D) designated Ω) (x : Sample (D := D) designated Ω)
    (hevent : UniformCleanSources.recordEvent (D := D) Ω zero record x = true) :
    visible designated Ω record =
      reveal designated (clean designated Ω record) (sourceTree designated Ω x) := by
  funext i leaf
  have hi := observation_eq designated Ω zero record x hevent i
  cases hc : UniformCleanSources.childClean (D := D) Ω zero i (x i).1 (x i).2.1 (x i).2.2 with
  | false =>
      have hr : record i = .inl (x i) := by
        simpa only [SelectedSources.childObservation, hc, Bool.false_eq_true, ite_false, if_false] using hi.symm
      dsimp only [visible, reveal, sourceTree]
      split
      · rename_i y hy
        have hyx : y = x i := Sum.inl.inj (hy.symm.trans hr)
        exact congrArg (fun z => assemble designated i z.1 z.2.1 leaf.val) hyx
      · rename_i r hy
        have hbad := hy.symm.trans hr
        cases hbad
  | true =>
      have hr : record i = .inr (x i).2.1 := by
        simpa only [SelectedSources.childObservation, hc, ite_true, if_true] using hi.symm
      have hn : leaf.val ≠ designated i := by
        intro heq
        apply leaf.property
        exact ⟨by simp only [clean, hr, UniformCleanSources.cleanRecord], heq⟩
      dsimp only [visible, reveal, sourceTree]
      split
      · rename_i y hy
        have hbad := hy.symm.trans hr
        cases hbad
      · rename_i r hy
        have hrx : r = (x i).2.1 := Sum.inr.inj (hy.symm.trans hr)
        exact (congrFun hrx ⟨leaf.val, hn⟩).trans
          (assemble_other designated i (x i).1 (x i).2.1 ⟨leaf.val, hn⟩).symm

omit [DecidableEq I] [∀ index, Fintype (D index)]
  [∀ index, DecidableEq (J index)] [∀ index, DecidableEq (D index)]
  [∀ index seed coord, Fintype (Ω index seed coord)]
  [∀ index seed coord, Nonempty (Ω index seed coord)] in
theorem projected_eq_raw (record : Record (D := D) designated Ω) (x : Sample (D := D) designated Ω)
    (hevent : UniformCleanSources.recordEvent (D := D) Ω zero record x = true) :
    projected designated Ω record = fun i => rawProjected designated Ω i (x i).2.2 := by
  funext i
  have hi := observation_eq designated Ω zero record x hevent i
  cases hc : UniformCleanSources.childClean (D := D) Ω zero i (x i).1 (x i).2.1 (x i).2.2 with
  | false =>
      have hr : record i = .inl (x i) := by
        simpa only [SelectedSources.childObservation, hc, Bool.false_eq_true, ite_false, if_false] using hi.symm
      simp only [projected, hr]
  | true =>
      have hr : record i = .inr (x i).2.1 := by
        simpa only [SelectedSources.childObservation, hc, ite_true, if_true] using hi.symm
      rw [projected, hr]
      cases hraw : (x i).2.2 with
      | inl d =>
          simp only [UniformCleanSources.childClean, UniformLatent.projectedZero,
            hraw, Bool.false_eq_true] at hc
      | inr raw => rfl

variable {v : Nat} (clauses : Fin m → SourceClause.NormalizedClause v)

omit [DecidableEq I] [∀ index, Fintype (D index)]
  [∀ index, DecidableEq (J index)] [∀ index, DecidableEq (D index)]
  [∀ index seed coord, Fintype (Ω index seed coord)]
  [∀ index seed coord, Nonempty (Ω index seed coord)] in
theorem reconstructLeft_eq (record : Record (D := D) designated Ω) (x : Sample (D := D) designated Ω)
    (hevent : UniformCleanSources.recordEvent (D := D) Ω zero record x = true) :
    SourceQuestionReconstruction.reconstructLeft designated (clean designated Ω record)
      (v := v) (visible designated Ω record)
      (fun i k => ((x i.val).1 k).1) =
        fun i leaf => leftTuple (v := v) (sourceTree designated Ω x i leaf) := by
  rw [visible_eq_reveal designated Ω zero record x hevent]
  simpa only [sourceTree_designated] using
    SourceQuestionReconstruction.reconstructLeft_eq designated (clean designated Ω record)
      (v := v) (sourceTree designated Ω x)

omit [DecidableEq I] [∀ index, Fintype (D index)]
  [∀ index, DecidableEq (J index)] [∀ index, DecidableEq (D index)]
  [∀ index seed coord, Fintype (Ω index seed coord)]
  [∀ index seed coord, Nonempty (Ω index seed coord)] in
theorem reconstructRight_eq (record : Record (D := D) designated Ω) (x : Sample (D := D) designated Ω)
    (hevent : UniformCleanSources.recordEvent (D := D) Ω zero record x = true) :
    SourceQuestionReconstruction.reconstructRight designated (clean designated Ω record) clauses
      (projected designated Ω record) (visible designated Ω record)
      (fun i k => SourceClause.occurrenceVariable clauses ((x i.val).1 k)) =
        fun i leaf => rightTuple clauses (rawProjected designated Ω i (x i).2.2)
          (sourceTree designated Ω x i leaf) := by
  rw [visible_eq_reveal designated Ω zero record x hevent]
  have h := SourceQuestionReconstruction.reconstructRight_eq designated (clean designated Ω record)
    clauses (projected designated Ω record) (clean_projected designated Ω record)
    (sourceTree designated Ω x)
  simpa only [sourceTree_designated, projected_eq_raw designated Ω zero record x hevent] using h

end
end PerfectCompleteness.CleanSourceRecord



namespace PerfectCompleteness.UniformCleanSoundness

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open FiniteProduct CleanConditioning SelectedSources UniformLatent UniformCleanSources

noncomputable section

attribute [local instance] Classical.propDecidable

variable {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
  {R J D : I → Type*}
  [∀ i, Fintype (R i)] [∀ i, Fintype (J i)] [∀ i, Fintype (D i)]
  [∀ i, DecidableEq (R i)] [∀ i, DecidableEq (J i)] [∀ i, DecidableEq (D i)]
  (Ω : (i : I) → (E × R i) → J i → Type*)
  [∀ i s j, Fintype (Ω i s j)] [∀ i s j, Nonempty (Ω i s j)]
  [∀ i s j, DecidableEq (Ω i s j)]

abbrev Sample := (i : I) → E × (R i × ChildRaw (D := D) Ω i)

def observations (zero : (i : I) → (s : E × R i) → (j : J i) → Ω i s j)
    (x : Sample (D := D) Ω) : FullRecord (D := D) Ω :=
  fun i => childObservation (childClean (D := D) Ω zero i) (x i)

omit [DecidableEq I] [Fintype E] [DecidableEq E]
  [∀ index, Fintype (R index)] [∀ index, Fintype (D index)]
  [∀ index, DecidableEq (J index)] [∀ index, DecidableEq (D index)]
  [∀ index seed coord, Fintype (Ω index seed coord)]
  [∀ index seed coord, Nonempty (Ω index seed coord)] in
theorem recordEvent_eq
    (zero : (i : I) → (s : E × R i) → (j : J i) → Ω i s j)
    (record : FullRecord (D := D) Ω) :
    recordEvent (D := D) Ω zero record =
      (fun x => decide (observations (D := D) Ω zero x = record)) := by
  funext x
  apply Bool.eq_iff_iff.mpr
  simp only [recordEvent, rowEvent, allEvent, decide_eq_true_eq,
    observations, funext_iff]

end
end PerfectCompleteness.UniformCleanSoundness



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_UniformLatentSupportLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.NativeTaggedUniform

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

section Native

variable {S : Type*} [Fintype S] [DecidableEq S]
  (Native : S → Type*) [∀ s, Fintype (Native s)] [∀ s, Nonempty (Native s)]

def kernel (s : S) : FiniteDistribution (Raw Native) :=
  (FiniteDistribution.uniform (Native s)).pushforward (fun x => (⟨s, x⟩ : Raw Native))

end Native

end
end PerfectCompleteness.NativeTaggedUniform



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceChildKernelLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftKeys_length _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_accepts _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightKeys_length _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.Normalization.equalityClauses_length _root_.OAI.PerfectCompleteness.Normalization.gadget_length _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceChildKernel

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces TreeSourceSpaces PointwiseSpaces HierarchicalArrays
open SourceQuestionReconstruction

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat} {C : Type*} [Fintype C]

abbrev Block (C : Type*) (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  (C → squareSpace (H slots)) × Arrays slots rows

instance blockFintype (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (Block C rows slots) := Fintype.ofFinite _

def zeroBlock (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) : Block C rows slots :=
  (fun _ => 0, fun _ _ => 0)

instance blockNonempty (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Nonempty (Block C rows slots) := ⟨zeroBlock rows slots⟩

variable (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

abbrev Rest (i : Fin (branch n)) :=
  CleanSourceRecord.Rest (m := m) (t := t) designated i

abbrev Source (i : Fin (branch n)) := SourceTuple m t × Rest (m := m) (t := t) designated i

def tree (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    Slots branch n → SourceTuple m t :=
  CleanSourceRecord.assemble designated i s.1 s.2

def nativeSlots (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    Slots branch n → Fin t → MixedSupport.Slot :=
  fun leaf k => SourceKeys.slot clauses (.clause (tree designated i s leaf k).1)

def ids (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    Slots branch n → Fin t → Nat :=
  fun leaf k => (SourceClause.occurrenceVariable clauses (tree designated i s leaf k)).val

def mixedSlots (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    Bool → Slots branch n → Fin t → MixedSupport.Slot
  | false => nativeSlots clauses designated i s
  | true => ProjectedCardinality.projectedSlots (ids clauses designated i s)

theorem mixedSlots_eq_rightTuple (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i)
    (b : Bool) (leaf : Slots branch n) (k : Fin t) :
    mixedSlots clauses designated i s b leaf k =
      SourceKeys.slot clauses (rightTuple clauses b (tree designated i s leaf) k) := by
  cases b <;> rfl

abbrev Native (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :=
  Block C rows (nativeSlots clauses designated i s)

abbrev Projected (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :=
  Block C rows (ProjectedCardinality.projectedSlots (ids clauses designated i s))

abbrev Factors (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :=
  CleanTreeFactors.Factors (Fintype.card C) rows (ids clauses designated i s)

abbrev D (i : Fin (branch n)) :=
  NativeTaggedUniform.Raw (Native (C := C) (t := t) rows clauses designated i)

abbrev Raw (i : Fin (branch n)) :=
  D (C := C) (t := t) rows clauses designated i ⊕
    UniformLatent.Raw (Factors (C := C) (t := t) rows clauses designated i)

instance rawFintype (i : Fin (branch n)) :
    Fintype (Raw (C := C) (t := t) rows clauses designated i) := by
  unfold Raw
  infer_instance

def nonprojected (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    FiniteDistribution (D (C := C) (t := t) rows clauses designated i) :=
  NativeTaggedUniform.kernel (Native (C := C) (t := t) rows clauses designated i) s

def projectedEquiv (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    ((j : CleanTreeFactors.Index branch n (Fintype.card C) rows) →
      Factors (C := C) (t := t) rows clauses designated i s j) ≃
        Projected (C := C) (t := t) rows clauses designated i s :=
  (CleanTreeFactors.rawEquiv (Fintype.card C) rows (ids clauses designated i s)).trans
    (CutChildCleanLaw.rawEquiv (C := C) rows (ids clauses designated i s)).symm

def zero (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i)
    (j : CleanTreeFactors.Index branch n (Fintype.card C) rows) :
    Factors (C := C) (t := t) rows clauses designated i s j :=
  ProjectedCardinality.factorZero (CleanTreeFactors.square (Fintype.card C) rows j)
    (CleanTreeFactors.factorIds (Fintype.card C) rows (ids clauses designated i s) j)

def rawProjected (i : Fin (branch n)) : Raw (C := C) (t := t) rows clauses designated i → Bool
  | .inl _ => false
  | .inr _ => true

def decodeNative (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i)
    (raw : D (C := C) (t := t) rows clauses designated i) : Native (C := C) (t := t) rows clauses designated i s :=
  if h : raw.1 = s then
    cast (congrArg (Native (C := C) (t := t) rows clauses designated i) h) raw.2
  else zeroBlock rows (nativeSlots clauses designated i s)

def decodeProjected (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i)
    (raw : UniformLatent.Raw (Factors (C := C) (t := t) rows clauses designated i)) :
    Projected (C := C) (t := t) rows clauses designated i s :=
  if h : raw.1 = s then
    cast (congrArg (Projected (C := C) (t := t) rows clauses designated i) h)
      (projectedEquiv (C := C) (t := t) rows clauses designated i raw.1 raw.2)
  else zeroBlock rows (ProjectedCardinality.projectedSlots (ids clauses designated i s))

omit [Fintype C] in
@[simp] theorem decodeNative_tagged (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i)
    (x : Native (C := C) (t := t) rows clauses designated i s) :
    decodeNative rows clauses designated i s ⟨s, x⟩ = x := by
  simp [decodeNative]

@[simp] theorem decodeProjected_tagged (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i)
    (x : (j : CleanTreeFactors.Index branch n (Fintype.card C) rows) →
      Factors (C := C) (t := t) rows clauses designated i s j) :
    decodeProjected rows clauses designated i s ⟨s, x⟩ =
      projectedEquiv (C := C) (t := t) rows clauses designated i s x := by
  simp [decodeProjected]

def decodeRight (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    (raw : Raw (C := C) (t := t) rows clauses designated i) →
      Block C rows (mixedSlots clauses designated i s (rawProjected rows clauses designated i raw))
  | .inl raw => decodeNative rows clauses designated i s raw
  | .inr raw => decodeProjected rows clauses designated i s raw

def projection (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) (b : Bool) :
    ∀ leaf k, MixedSupport.Projection (nativeSlots clauses designated i s leaf k)
      (mixedSlots clauses designated i s b leaf k) := by
  cases b with
  | false => exact fun leaf k => .keep (nativeSlots clauses designated i s leaf k)
  | true => exact fun leaf k =>
      (SourceKeys.Step.select (clauses := clauses)
        (tree designated i s leaf k).1 (tree designated i s leaf k).2).projection

abbrev Sources := (i : Fin (branch n)) → Source (m := m) (t := t) designated i

def parentLeftSlots (sources : Sources (m := m) (t := t) designated) :
    Slots branch (n + 1) → Fin t → MixedSupport.Slot :=
  fun leaf k => nativeSlots clauses designated leaf.1 (sources leaf.1) leaf.2 k

def parentRightSlots (sources : Sources (m := m) (t := t) designated)
    (raw : (i : Fin (branch n)) → Raw (C := C) (t := t) rows clauses designated i) :
    Slots branch (n + 1) → Fin t → MixedSupport.Slot :=
  fun leaf k => mixedSlots clauses designated leaf.1 (sources leaf.1)
    (rawProjected rows clauses designated leaf.1 (raw leaf.1)) leaf.2 k

def parentProjection (sources : Sources (m := m) (t := t) designated)
    (raw : (i : Fin (branch n)) → Raw (C := C) (t := t) rows clauses designated i) :
    ∀ leaf k, MixedSupport.Projection (parentLeftSlots clauses designated sources leaf k)
      (parentRightSlots rows clauses designated sources raw leaf k) :=
  fun leaf k => projection clauses designated leaf.1 (sources leaf.1)
    (rawProjected rows clauses designated leaf.1 (raw leaf.1)) leaf.2 k

def rightChildren (sources : Sources (m := m) (t := t) designated)
    (raw : (i : Fin (branch n)) → Raw (C := C) (t := t) rows clauses designated i) :
    CutChildGrouping.Raw (C := C) (t := t) (parentRightSlots rows clauses designated sources raw) rows :=
  fun i => decodeRight rows clauses designated i (sources i) (raw i)

def leftChildren (sources : Sources (m := m) (t := t) designated)
    (raw : (i : Fin (branch n)) → Raw (C := C) (t := t) rows clauses designated i) :
    CutChildGrouping.Raw (C := C) (t := t) (parentLeftSlots clauses designated sources) rows :=
  ChildAssemblyProjection.rawPullback rows
    (parentProjection rows clauses designated sources raw)
    (rightChildren rows clauses designated sources raw)

abbrev Sample := (i : Fin (branch n)) → SourceTuple m t ×
  (Rest (m := m) (t := t) designated i × Raw (C := C) (t := t) rows clauses designated i)

instance sampleFintype : Fintype (Sample (C := C) (t := t) rows clauses designated) := by
  unfold Sample
  infer_instance

def childrenLaw (μ : Fin (branch n) → FiniteDistribution (SourceTuple m t))
    (ν : (i : Fin (branch n)) → FiniteDistribution (Rest (m := m) (t := t) designated i))
    (flag : Fin (branch n) → FiniteDistribution Bool) :
    FiniteDistribution (Sample (C := C) (t := t) rows clauses designated) :=
  UniformCleanSources.childrenLaw (Factors (C := C) (t := t) rows clauses designated) μ ν flag
    (nonprojected (C := C) (t := t) rows clauses designated)

def originalLaw [NeZero m] (flag : Fin (branch n) → FiniteDistribution Bool) :
    FiniteDistribution (Sample (C := C) (t := t) rows clauses designated) :=
  childrenLaw rows clauses designated (fun _ => SourceOddLists.tupleLaw m t)
    (fun i => FiniteProduct.law (fun _ : {leaf : Slots branch n // leaf ≠ designated i} =>
      SourceOddLists.tupleLaw m t)) flag

end
end PerfectCompleteness.SourceChildKernel

end

section

namespace PerfectCompleteness.SourceChildKernelJoint

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces SourceQuestionReconstruction

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat} {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

abbrev RawTuple :=
  (i : Fin (branch n)) → SourceChildKernel.Raw (C := C) (t := t) rows clauses designated i

def groupEquiv :
    SourceChildKernel.Sample (C := C) (t := t) rows clauses designated ≃
      SourceChildKernel.Sources (m := m) (t := t) designated ×
        RawTuple (C := C) (t := t) rows clauses designated where
  toFun x := (fun i => ((x i).1, (x i).2.1), fun i => (x i).2.2)
  invFun x := fun i => ((x.1 i).1, (x.1 i).2, x.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem groupEquiv_sources
    (x : SourceChildKernel.Sample (C := C) (t := t) rows clauses designated)
    (i : Fin (branch n)) :
    (groupEquiv rows clauses designated x).1 i = ((x i).1, (x i).2.1) := rfl

@[simp] theorem groupEquiv_raw
    (x : SourceChildKernel.Sample (C := C) (t := t) rows clauses designated)
    (i : Fin (branch n)) :
    (groupEquiv rows clauses designated x).2 i = (x i).2.2 := rfl

end
end PerfectCompleteness.SourceChildKernelJoint

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_NativeLeafAlphabet
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.HierarchicalArrays.joint_component _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.NodeEmbedding.embed_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.embeddedRows_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.equiv_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.matrix_evaluate _root_.OAI.PerfectCompleteness.NodeEmbedding.rowsEquiv_apply _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.TreeCanonical.assignmentEquiv_apply _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_selected _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.NativeLeafAlphabet

open SourceClause

variable {I : Type*} {v m t : Nat}

def castAssignment {a b : I → MixedSupport.Slot} (h : a = b) :
    MixedSupport.Assignment a ≃ MixedSupport.Assignment b :=
  Equiv.cast (congrArg (fun slots : I → MixedSupport.Slot =>
    MixedSupport.Assignment slots) h)

@[simp] theorem castAssignment_rfl (a : I → MixedSupport.Slot) :
    castAssignment (rfl : a = a) = Equiv.refl (MixedSupport.Assignment a) := rfl

def nativeLeftEquiv (clauses : Fin m → NormalizedClause v)
    (question : Fin t → Fin m) {a : Fin t → MixedSupport.Slot}
    (ha : a = SourceAnswerEquiv.leftSlots clauses question) :
    MixedSupport.Assignment a ≃ SourceOddLists.LeftLabels t :=
  (castAssignment ha).trans (SourceAnswerEquiv.leftEquiv clauses question)

def nativeRightEquiv (clauses : Fin m → NormalizedClause v)
    (question : Fin t → Fin v) {b : Fin t → MixedSupport.Slot}
    (hb : b = SourceAnswerEquiv.rightSlots clauses question) :
    MixedSupport.Assignment b ≃ SourceOddLists.RightLabels t :=
  (castAssignment hb).trans (SourceAnswerEquiv.rightEquiv clauses question)

end PerfectCompleteness.NativeLeafAlphabet

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceLocalOddLists
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceLocalOddLists

open scoped Classical
open PointwiseSpaces TreeSourceSpaces SourceAnswerEquiv
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {h t v m s : Nat}

abbrev Form (slots : RecursiveSpaces.Slots branch h → Fin t → MixedSupport.Slot) :=
  H slots →ₗ[F2] H slots →ₗ[F2] F2

def leafSupport (slots : RecursiveSpaces.Slots branch h → Fin t → MixedSupport.Slot)
    (F : Form slots) (leaf : RecursiveSpaces.Slots branch h) : Finset (LeafDomain slots leaf) :=
  OddLists.support (fun a => F
    (OddListExtraction.atom (H slots) (fun x => x leaf)
      (OddListExtraction.source_leaf_indicator_mem slots leaf) a)
    (OddListExtraction.atom (H slots) (fun x => x leaf)
      (OddListExtraction.source_leaf_indicator_mem slots leaf) a))

def extract (positive : 0 < s)
    (slots : RecursiveSpaces.Slots branch h → Fin t → MixedSupport.Slot)
    (F : Form slots) (leaf : RecursiveSpaces.Slots branch h) (fallback : LeafDomain slots leaf) :
    OddLists.OddList s (LeafDomain slots leaf) :=
  OddLists.OddList.extract positive fallback (leafSupport slots F leaf)

end
end PerfectCompleteness.SourceLocalOddLists

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_HiddenBucketBias
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HiddenBucketBias

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators TensorProduct Classical

noncomputable section

abbrev F2 := BucketSampler.F2

variable {ℓ : Nat} {Ω H : Type*} [Fintype Ω]
  [AddCommGroup H] [Module F2 H]

abbrev HiddenDirection (W : Submodule F2 (Fin ℓ → F2)) :=
  {v : BucketSampler.Direction ℓ // v.val ∈ W}

abbrev VisibleDirection (W : Submodule F2 (Fin ℓ → F2)) :=
  {v : BucketSampler.Direction ℓ // v.val ∉ W}

abbrev HiddenTape (W : Submodule F2 (Fin ℓ → F2)) (Ω : Type*) := HiddenDirection W → Ω
abbrev VisibleTape (W : Submodule F2 (Fin ℓ → F2)) (Ω : Type*) := VisibleDirection W → Ω

def hiddenTapeLaw (W : Submodule F2 (Fin ℓ → F2)) (μ : FiniteDistribution Ω) :
    FiniteDistribution (HiddenTape W Ω) :=
  FiniteProduct.law (fun _ : HiddenDirection W => μ)

def splitTape (W : Submodule F2 (Fin ℓ → F2)) (Ω : Type*) :
    BucketSampler.Tape ℓ Ω ≃ HiddenTape W Ω × VisibleTape W Ω :=
  Equiv.piEquivPiSubtypeProd (fun v : BucketSampler.Direction ℓ => v.val ∈ W) (fun _ => Ω)

def directionIn (W : Submodule F2 (Fin ℓ → F2)) (v : HiddenDirection W) : W :=
  ⟨v.val.val, v.property⟩

def hiddenSum (W : Submodule F2 (Fin ℓ → F2)) (eval : Ω → H) (ω : HiddenTape W Ω) :
    W ⊗[F2] H :=
  ∑ v : HiddenDirection W, directionIn W v ⊗ₜ[F2] eval (ω v)

def scalarRestriction (W : Submodule F2 (Fin ℓ → F2))
    (Φ : Module.Dual F2 (W ⊗[F2] H)) (v : W) : Module.Dual F2 H :=
  Φ.comp (TensorProduct.mk F2 W H v)

@[simp] theorem scalarRestriction_apply (W : Submodule F2 (Fin ℓ → F2))
    (Φ : Module.Dual F2 (W ⊗[F2] H)) (v : W) (h : H) :
    scalarRestriction W Φ v h = Φ (v ⊗ₜ[F2] h) := rfl

instance tensorFinite (W : Submodule F2 (Fin ℓ → F2)) [Finite H] :
    Finite (W ⊗[F2] H) := by
  let : Fintype W := Fintype.ofFinite _
  apply Finite.of_surjective (fun f : W → H => ∑ w, w ⊗ₜ[F2] f w)
  intro z
  obtain ⟨s, hs⟩ := TensorProduct.exists_finsupp_left z
  refine ⟨fun w => s w, ?_⟩
  exact (s.sum_fintype (fun w h => w ⊗ₜ[F2] h) (fun _ => by simp)).symm.trans hs.symm

instance tensorFintype (W : Submodule F2 (Fin ℓ → F2)) [Finite H] :
    Fintype (W ⊗[F2] H) := Fintype.ofFinite _

def law (W : Submodule F2 (Fin ℓ → F2)) [Finite H]
    (μ : FiniteDistribution Ω) (eval : Ω → H) : FiniteDistribution (W ⊗[F2] H) :=
  (hiddenTapeLaw W μ).pushforward (hiddenSum W eval)

section Recursive

universe u
variable {branch : Nat → Nat} {n m : Nat}

def recursiveLaw (W : Submodule F2 (Fin ℓ → F2)) (repeats : Nat → Nat)
    (p : DescendantSpaces.Path branch n m) (A : RecursiveSpaces.Slots branch n → Type u)
    [∀ s, Finite (A s)] :
    FiniteDistribution (W ⊗[F2] RecursiveSpaces.space F2 branch n A) :=
  law W (RecursiveSampler.tapeLaw F2 repeats p A) (RecursiveSampler.evaluate F2 repeats p A)

end Recursive


end

end PerfectCompleteness.HiddenBucketBias

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_CutSamplerRefinement
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.stepFactorFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutSamplerRefinement

open PointwiseSpaces RecursiveSpaces DescendantSpaces RecursiveSampler
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m : Nat}

theorem refined_finite (𝕜 : Type w) [Field 𝕜] [Finite 𝕜]
    (repeats : Nat → Nat) (p : Path branch n m) :
    ∀ (A : Slots branch n → Type u), (∀ s, Finite (A s)) →
      ∀ j : DrawIndex repeats p, Finite (RefinedSpace 𝕜 repeats p A j) := by
  induction p with
  | refl n =>
      intro A hA j
      let : ∀ s, Finite (A s) := hA
      cases n with
      | zero =>
          change Finite (space 𝕜 branch 0 A)
          infer_instance
      | succ n =>
          change Finite ((i : Fin (branch n)) →
            squareSpace (space 𝕜 branch n (childFamily A i)))
          let : ∀ i : Fin (branch n),
              Finite (squareSpace (space 𝕜 branch n (childFamily A i))) := fun i => by
            let : ∀ s, Finite ((childFamily A i) s) := fun s => hA (i, s)
            infer_instance
          infer_instance
  | @step n m i p ih =>
      intro A hA j
      cases j with
      | inl j =>
          let : ∀ s, Finite ((childFamily A j.val) s) := fun s => hA (j.val, s)
          change Finite (squareSpace (space 𝕜 branch n (childFamily A j.val)))
          infer_instance
      | inr j =>
          exact ih (childFamily A i) (fun s => hA (i, s)) j.2

instance refinedFinite (𝕜 : Type w) [Field 𝕜] [Finite 𝕜]
    (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) [∀ s, Finite (A s)] (j : DrawIndex repeats p) :
    Finite (RefinedSpace 𝕜 repeats p A j) :=
  refined_finite 𝕜 repeats p A (fun _ => inferInstance) j

instance refinedFintype (𝕜 : Type w) [Field 𝕜] [Finite 𝕜]
    (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) [∀ s, Finite (A s)] (j : DrawIndex repeats p) :
    Fintype (RefinedSpace 𝕜 repeats p A j) := Fintype.ofFinite _

def collapseFactor (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) → (A : Slots branch n → Type u) →
      (j : DrawIndex repeats p) → RefinedSpace 𝕜 repeats p A j → DrawSpace 𝕜 repeats p A j
  | 0, _, .refl _, _, _, x => x
  | _ + 1, _, .refl _, A, _, x => UniformChildSum.recursiveSum A x
  | _ + 1, _, .step i p, A, j, x =>
      match j with
      | Sum.inl _ => x
      | Sum.inr j => collapseFactor 𝕜 repeats p (childFamily A i) j.2 x

def collapse (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) (A : Slots branch n → Type u) :
    Tape 𝕜 repeats p A → RecursiveSampler.Tape 𝕜 repeats p A :=
  fun x j => collapseFactor 𝕜 repeats p A j (x j)

end
end PerfectCompleteness.CutSamplerRefinement

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_WholeCutSampler
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeCutSampler

open TreeSourceSpaces HierarchicalArrays DescendantSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

abbrev RootTape (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :=
  BucketSampler.Direction (rows n) →
    CutSamplerRefinement.Tape F2 repeats p (LeafDomain slots)

def Tape (rows repeats : Nat → Nat) :
    {n m : Nat} → Path branch n m →
      (RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) → Type
  | 0, _, .refl _, slots => Arrays slots rows
  | n + 1, _, .refl _, slots =>
      CutChildGrouping.Raw (C := Fin (rows (n + 1))) slots rows
  | _, _, .step i p, slots =>
      RootTape rows repeats (.step i p) slots ×
        (Tape rows repeats p (childSlots slots i) ×
          ((j : RecursiveSampler.OffPath i) → Arrays (childSlots slots j.val) rows))

@[instance_reducible] def tapeFintypeAux (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) →
      (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) →
        Fintype (Tape rows repeats p slots)
  | 0, _, .refl _, slots => inferInstanceAs (Fintype (Arrays slots rows))
  | n + 1, _, .refl _, slots =>
      inferInstanceAs (Fintype (CutChildGrouping.Raw (C := Fin (rows (n + 1))) slots rows))
  | _, _, .step i p, slots =>
      letI : Fintype (Tape rows repeats p (childSlots slots i)) :=
        tapeFintypeAux rows repeats p (childSlots slots i)
      inferInstanceAs (Fintype
        (RootTape rows repeats (.step i p) slots ×
          (Tape rows repeats p (childSlots slots i) ×
            ((j : RecursiveSampler.OffPath i) → Arrays (childSlots slots j.val) rows))))

def stepEquiv (i : Fin (branch n)) (Root Selected : Type)
    (Ordinary : RecursiveSampler.OffPath i → Type) :
    (Root × (Selected × ((j : RecursiveSampler.OffPath i) → Ordinary j))) ≃
      WholeArraySampler.StepTape (i := i) Root Selected Ordinary where
  toFun x k := match k with
    | .inl _ => x.1
    | .inr (.inl _) => x.2.1
    | .inr (.inr j) => x.2.2 j
  invFun x := (x (.inl ()), x (.inr (.inl ())), fun j => x (.inr (.inr j)))
  left_inv x := rfl
  right_inv x := by
    funext k
    rcases k with u | (u | j)
    · cases u
      rfl
    · cases u
      rfl
    · rfl

def assembleArrays
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (rows : Nat → Nat) :
    CutChildGrouping.Assembled (C := Fin (rows (n + 1))) slots rows →ₗ[F2]
      Arrays slots rows where
  toFun x := WholeArraySampler.assemble slots rows x.1 x.2
  map_add' x y := by
    funext node
    rcases node with u | ⟨i, node⟩ <;> rfl
  map_smul' c x := by
    funext node
    rcases node with u | ⟨i, node⟩ <;> rfl

def collapseRoot (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    RootTape rows repeats p slots → WholeArraySampler.RootTape rows repeats p slots :=
  fun x v => CutSamplerRefinement.collapse F2 repeats p (LeafDomain slots) (x v)

def collapse (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) →
      (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) →
        Tape rows repeats p slots → WholeArraySampler.Tape rows repeats p slots
  | 0, _, .refl _, _, x => x
  | _ + 1, _, .refl _, slots, x =>
      assembleArrays slots rows (CutChildGrouping.assemble slots rows x)
  | _, _, .step i p, slots, x =>
      stepEquiv i (WholeArraySampler.RootTape rows repeats (.step i p) slots)
        (WholeArraySampler.Tape rows repeats p (childSlots slots i))
        (fun j => Arrays (childSlots slots j.val) rows)
        (collapseRoot rows repeats (.step i p) slots x.1,
          collapse rows repeats p (childSlots slots i) x.2.1, x.2.2)

def evaluate (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (x : Tape rows repeats p slots) : Arrays slots rows :=
  WholeArraySampler.evaluate rows repeats p slots (collapse rows repeats p slots x)

end

end PerfectCompleteness.WholeCutSampler

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeCutGrouping
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeCutGrouping

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

abbrev cutSlots (p : Path branch n m)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Slots branch m → Fin t → MixedSupport.Slot :=
  fun s => slots (p.slotEmbedding s)

def Exterior (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (Slots branch n → Fin t → MixedSupport.Slot) → Type
  | _, _, .refl _, _ => Unit
  | n + 1, _, .step i p, slots =>
      (BucketSampler.Direction (rows (n + 1)) →
        CutTerminalSplit.ExteriorTape F2 repeats (.step i p) (LeafDomain slots)) ×
      (Exterior rows repeats p (childSlots slots i) ×
        ((j : RecursiveSampler.OffPath i) → Arrays (childSlots slots j.val) rows))

@[instance_reducible] def exteriorFintypeAux (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
        Fintype (Exterior rows repeats p slots)
  | _, _, .refl _, _ => inferInstanceAs (Fintype Unit)
  | n + 1, _, .step i p, slots =>
      letI : Fintype (Exterior rows repeats p (childSlots slots i)) :=
        exteriorFintypeAux rows repeats p (childSlots slots i)
      inferInstanceAs (Fintype
        ((BucketSampler.Direction (rows (n + 1)) →
          CutTerminalSplit.ExteriorTape F2 repeats (.step i p) (LeafDomain slots)) ×
        (Exterior rows repeats p (childSlots slots i) ×
          ((j : RecursiveSampler.OffPath i) → Arrays (childSlots slots j.val) rows))))

def splitTape (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
      WholeCutSampler.Tape rows repeats p slots ≃
        Exterior rows repeats p slots ×
          CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) (cutSlots p slots) rows
  | _, _, .refl _, slots =>
      { toFun := fun x => ((), x)
        invFun := Prod.snd
        left_inv := fun _ => rfl
        right_inv := by rintro ⟨⟨⟩, x⟩; rfl }
  | n + 1, _, .step i p, slots =>
      (Equiv.prodCongr
        (Equiv.piCongrRight (fun _ : BucketSampler.Direction (rows (n + 1)) =>
          CutTerminalSplit.splitTape F2 repeats (.step i p) (LeafDomain slots)))
        (Equiv.prodCongr (splitTape rows repeats p (childSlots slots i)) (Equiv.refl _))).trans
          regroupStep

end
end PerfectCompleteness.WholeCutGrouping

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeCutExteriorTransportLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_refl _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_refl_right _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_step _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_castSucc _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_last _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.NodeEmbedding.embed_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.embeddedRows_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.equiv_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.matrix_evaluate _root_.OAI.PerfectCompleteness.NodeEmbedding.rowsEquiv_apply _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeCutExteriorTransport

open PointwiseSpaces RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open RecursiveSampler TerminalCalls
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def Outside (p : Path branch n m) (s : Slots branch n) : Prop :=
  s ∉ Set.range p.slotEmbedding

theorem outside_ordinary (i : Fin (branch n)) (p : Path branch n m)
    (j : OffPath i) (s : Slots branch n) : Outside (.step i p) (j.val, s) := by
  rintro ⟨u, hu⟩
  exact j.property (congrArg Prod.fst hu).symm

theorem outside_selected (i : Fin (branch n)) (p : Path branch n m)
    (s : Slots branch n) (hs : Outside p s) : Outside (.step i p) (i, s) := by
  rintro ⟨u, hu⟩
  exact hs ⟨u, congrArg Prod.snd hu⟩

theorem ordinarySlots_eq (i : Fin (branch n)) (p : Path branch n m)
    (slots target : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (hs : ∀ s, Outside (.step i p) s → slots s = target s) (j : OffPath i) :
    childSlots slots j.val = childSlots target j.val := by
  funext s
  exact hs (j.val, s) (outside_ordinary i p j s)

theorem factor_eq (repeats : Nat → Nat) (p : Path branch n m) :
    ∀ (slots target : Slots branch n → Fin t → MixedSupport.Slot),
      (∀ s, Outside p s → slots s = target s) →
      ∀ (j : DrawIndex repeats p), ¬ IsTerminal repeats p j →
        CutSamplerRefinement.RefinedSpace F2 repeats p (LeafDomain slots) j =
          CutSamplerRefinement.RefinedSpace F2 repeats p (LeafDomain target) j := by
  induction p with
  | refl n =>
      intro slots target hs j hj
      exact False.elim (hj True.intro)
  | @step n m i p ih =>
      intro slots target hs j hj
      cases j with
      | inl j =>
          exact congrArg
            (fun ss : Slots branch n → Fin t → MixedSupport.Slot =>
              (squareSpace (space F2 branch n (LeafDomain ss)) : Type))
            (ordinarySlots_eq i p slots target hs j)
      | inr j =>
          exact ih (childSlots slots i) (childSlots target i)
            (fun s h => hs (i, s) (outside_selected i p s h)) j.2 hj

theorem scalarExterior_eq (repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (hs : ∀ s, Outside p s → slots s = target s) :
    CutTerminalSplit.ExteriorTape F2 repeats p (LeafDomain slots) =
      CutTerminalSplit.ExteriorTape F2 repeats p (LeafDomain target) :=
  congrArg
    (fun A : CutTerminalSplit.ExteriorIndex repeats p → Type =>
      (j : CutTerminalSplit.ExteriorIndex repeats p) → A j)
    (funext (fun j => factor_eq repeats p slots target hs j.val j.property))

def scalarEquiv (repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (hs : ∀ s, Outside p s → slots s = target s) :
    CutTerminalSplit.ExteriorTape F2 repeats p (LeafDomain slots) ≃
      CutTerminalSplit.ExteriorTape F2 repeats p (LeafDomain target) :=
  Equiv.piCongrRight (fun j => Equiv.cast (factor_eq repeats p slots target hs j.val j.property))

@[simp] theorem scalarEquiv_apply (repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (hs : ∀ s, Outside p s → slots s = target s)
    (x : CutTerminalSplit.ExteriorTape F2 repeats p (LeafDomain slots))
    (j : CutTerminalSplit.ExteriorIndex repeats p) :
    scalarEquiv repeats p slots target hs x j =
      cast (factor_eq repeats p slots target hs j.val j.property) (x j) := rfl

theorem exterior_eq (rows repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (slots target : Slots branch n → Fin t → MixedSupport.Slot),
      (∀ s, Outside p s → slots s = target s) →
      WholeCutGrouping.Exterior rows repeats p slots =
        WholeCutGrouping.Exterior rows repeats p target := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl => intro slots target hs; rfl
      | step i p =>
          intro slots target hs
          have hroot := scalarExterior_eq repeats (.step i p) slots target hs
          have hselected := ih p (childSlots slots i) (childSlots target i)
            (fun s h => hs (i, s) (outside_selected i p s h))
          have hord :
              ((j : OffPath i) → Arrays (childSlots slots j.val) rows) =
                ((j : OffPath i) → Arrays (childSlots target j.val) rows) :=
            congrArg (fun A : OffPath i → Type => (j : OffPath i) → A j)
              (funext (fun j => congrArg
                (fun ss : Slots branch n → Fin t → MixedSupport.Slot => Arrays ss rows)
                (ordinarySlots_eq i p slots target hs j)))
          exact congrArg₂ (fun A B : Type => A × B)
            (congrArg (fun A : Type => BucketSampler.Direction (rows (n + 1)) → A) hroot)
            (congrArg₂ (fun A B : Type => A × B) hselected hord)

def equiv (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (hs : ∀ s, Outside p s → slots s = target s) :
    WholeCutGrouping.Exterior rows repeats p slots ≃
      WholeCutGrouping.Exterior rows repeats p target :=
  Equiv.cast (exterior_eq rows repeats p slots target hs)

end
end PerfectCompleteness.WholeCutExteriorTransport

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_CutSamplerKeyLocalityLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.stepFactorFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CutSamplerKeyLocality

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces

noncomputable section

universe u

variable {branch : Nat → Nat} {n m t : Nat}

def keptLeaf : {n m : Nat} → Path branch n (m + 1) →
    (Fin (branch m) → Prop) → Slots branch n → Prop
  | _, _, .refl _, clean, s => ¬ clean s.1
  | _, _, .step i p, clean, s => s.1 ≠ i ∨ keptLeaf p clean s.2


end
end PerfectCompleteness.CutSamplerKeyLocality



namespace PerfectCompleteness.CutSamplerReplay

open scoped BigOperators Classical
open RecursiveSpaces DescendantSpaces RecursiveSampler PointwiseSpaces

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m : Nat}

def Tape (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) → (A : Slots branch n → Type u) →
      (clean : Fin (branch m) → Prop) → Type (max u w)
  | _, m, .refl _, A, clean =>
      (i : {i : Fin (branch m) // ¬ clean i}) →
        squareSpace (space 𝕜 branch m (childFamily A i.val))
  | n + 1, _, .step i p, A, clean =>
      ((j : OffPath i) → squareSpace (space 𝕜 branch n (childFamily A j.val))) ×
        ((call : Fin (repeats (n + 1)) × Bool) → Tape 𝕜 repeats p (childFamily A i) clean)

end
end PerfectCompleteness.CutSamplerReplay



namespace PerfectCompleteness.CutSamplerReplayGrouping

open RecursiveSpaces DescendantSpaces RecursiveSampler TerminalCalls PointwiseSpaces

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m : Nat}

abbrev RetainedTerminal (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (A : Slots branch n → Type u)
    (clean : Fin (branch m) → Prop) :=
  TerminalIndex repeats p → (i : {i : Fin (branch m) // ¬ clean i}) →
    squareSpace (space 𝕜 branch m (childFamily (p.family A) i.val))

def exteriorStepIndex (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1)) (call : Fin (repeats (n + 1)) × Bool)
    (j : CutTerminalSplit.ExteriorIndex repeats p) :
    CutTerminalSplit.ExteriorIndex repeats (.step i p) :=
  ⟨.inr (call, j.val), j.property⟩

def subExterior (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (i : Fin (branch n)) (p : Path branch n (m + 1))
    (A : Slots branch (n + 1) → Type u) (call : Fin (repeats (n + 1)) × Bool)
    (exterior : CutTerminalSplit.ExteriorTape 𝕜 repeats (.step i p) A) :
    CutTerminalSplit.ExteriorTape 𝕜 repeats p (childFamily A i) :=
  fun j => exterior (exteriorStepIndex repeats i p call j)

def assemble (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) → (A : Slots branch n → Type u) →
      (clean : Fin (branch m) → Prop) →
      CutTerminalSplit.ExteriorTape 𝕜 repeats p A →
      RetainedTerminal 𝕜 repeats p A clean → CutSamplerReplay.Tape 𝕜 repeats p A clean
  | _, _, .refl _, _, _, _, terminal => terminal ()
  | _, _, .step i p, A, clean, exterior, terminal =>
      (fun j => exterior ⟨.inl j, not_isTerminal_ordinary repeats i p j⟩,
        fun call => assemble 𝕜 repeats p (childFamily A i) clean
          (subExterior 𝕜 repeats i p A call exterior)
          (fun location child => terminal (call, location) child))

end
end PerfectCompleteness.CutSamplerReplayGrouping

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_CutSamplerReplayTransportLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.stepFactorFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CutSamplerReplayTransport

open PointwiseSpaces RecursiveSpaces DescendantSpaces RecursiveSampler
open CutSamplerKeyLocality
open scoped BigOperators Classical

noncomputable section

universe u v w

variable {branch : Nat → Nat} {n m : Nat}
  (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)

def transport (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
    (A : Slots branch n → Type u) → (B : Slots branch n → Type v) →
    (clean : Fin (branch m) → Prop) →
    (∀ s, keptLeaf p clean s → A s ≃ B s) →
    CutSamplerReplay.Tape 𝕜 repeats p A clean →
      CutSamplerReplay.Tape 𝕜 repeats p B clean
  | _, _, .refl _, _, _, _, e, tape =>
      fun i => (RecursiveSpaceEquiv.squareEquiv (𝕜 := 𝕜)
        (fun s => e (i.val, s) i.property)).symm (tape i)
  | _, _, .step i p, A, B, clean, e, tape =>
      (fun j => (RecursiveSpaceEquiv.squareEquiv (𝕜 := 𝕜)
        (fun s => e (j.val, s) (Or.inl j.property))).symm (tape.1 j),
        fun call => transport 𝕜 repeats p (childFamily A i) (childFamily B i) clean
          (fun s hs => e (i, s) (Or.inr hs)) (tape.2 call))

end
end PerfectCompleteness.CutSamplerReplayTransport


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeCutReplayLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_castSucc _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_last _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.NodeEmbedding.embed_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.embeddedRows_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.equiv_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.matrix_evaluate _root_.OAI.PerfectCompleteness.NodeEmbedding.rowsEquiv_apply _root_.OAI.PerfectCompleteness.OddListExtraction.form_atom_self _root_.OAI.PerfectCompleteness.OddListExtraction.multiplicationForm_apply _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.squareProduct_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeCutReplay

open scoped BigOperators Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def Tape (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
      (clean : Fin (branch m) → Prop) → Type
  | _, m, .refl _, slots, clean =>
      (i : {i : Fin (branch m) // ¬ clean i}) →
        CutChildGrouping.Child (C := Fin (rows (m + 1))) slots rows i.val
  | n + 1, _, .step i p, slots, clean =>
      (BucketSampler.Direction (rows (n + 1)) →
        CutSamplerReplay.Tape F2 repeats (.step i p) (LeafDomain slots) clean) ×
      (Tape rows repeats p (childSlots slots i) clean ×
        ((j : RecursiveSampler.OffPath i) → Arrays (childSlots slots j.val) rows))

end
end PerfectCompleteness.WholeCutReplay

end

section

namespace PerfectCompleteness.WholeCutReplayGrouping

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

abbrev RetainedChildren (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (clean : Fin (branch m) → Prop) :=
  (i : {i : Fin (branch m) // ¬ clean i}) →
    CutChildGrouping.Child (C := WholeCutCalls.Index rows repeats p)
      (WholeCutGrouping.cutSlots p slots) rows i.val

def assemble (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
      (clean : Fin (branch m) → Prop) → WholeCutGrouping.Exterior rows repeats p slots →
        RetainedChildren rows repeats p slots clean → WholeCutReplay.Tape rows repeats p slots clean
  | _, _, .refl _, _, _, _, children => children
  | _, _, .step i p, slots, clean, exterior, children =>
      (fun bucket => CutSamplerReplayGrouping.assemble F2 repeats (.step i p)
        (LeafDomain slots) clean (exterior.1 bucket)
        (fun terminal child => (children child).1 (.inl (bucket, terminal))),
        assemble rows repeats p (childSlots slots i) clean exterior.2.1
          (fun child => (fun q => (children child).1 (.inr q), (children child).2)),
        exterior.2.2)

end
end PerfectCompleteness.WholeCutReplayGrouping

end

section

namespace PerfectCompleteness.CutSamplerReplay

open scoped BigOperators Classical
open RecursiveSpaces DescendantSpaces RecursiveSampler PointwiseSpaces

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m : Nat}

def retainedSum (𝕜 : Type w) [Field 𝕜]
    (A : Slots branch (m + 1) → Type u) (clean : Fin (branch m) → Prop)
    (tape : (i : {i : Fin (branch m) // ¬ clean i}) →
      squareSpace (space 𝕜 branch m (childFamily A i.val))) :
    space 𝕜 branch (m + 1) A :=
  ⟨∑ i : {i : Fin (branch m) // ¬ clean i},
      pullback 𝕜 (childRestriction A i.val) (tape i).val, by
    apply (space 𝕜 branch (m + 1) A).sum_mem
    intro i _
    exact child_square_le_space A i.val
      (Submodule.mem_map_of_mem (tape i).property)⟩

@[simp] theorem retainedSum_apply (𝕜 : Type w) [Field 𝕜]
    (A : Slots branch (m + 1) → Type u) (clean : Fin (branch m) → Prop)
    (tape : (i : {i : Fin (branch m) // ¬ clean i}) →
      squareSpace (space 𝕜 branch m (childFamily A i.val))) (x : Assignment A) :
    (retainedSum 𝕜 A clean tape).val x =
      ∑ i : {i : Fin (branch m) // ¬ clean i},
        (tape i).val (childRestriction A i.val x) := by
  simp only [retainedSum, Finset.sum_apply, PointwiseSpaces.pullback_apply]

def evaluateSpace (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) → (A : Slots branch n → Type u) →
      (clean : Fin (branch m) → Prop) → Tape 𝕜 repeats p A clean →
        space 𝕜 branch n A
  | _, _, .refl _, A, clean, tape => retainedSum 𝕜 A clean tape
  | n + 1, _, .step i p, A, clean, tape =>
      RecursiveSampler.combine 𝕜 A i (repeats (n + 1)) tape.1
        (fun h => evaluateSpace 𝕜 repeats p (childFamily A i) clean (tape.2 (h, false)))
        (fun h => evaluateSpace 𝕜 repeats p (childFamily A i) clean (tape.2 (h, true)))

end
end PerfectCompleteness.CutSamplerReplay

namespace PerfectCompleteness.WholeCutReplay

open scoped BigOperators Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def evaluateArrays (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
      (clean : Fin (branch m) → Prop) → Tape rows repeats p slots clean → Arrays slots rows
  | _, m, .refl _, slots, clean, tape =>
      WholeArraySampler.assemble slots rows
        (fun row => CutSamplerReplay.evaluateSpace F2 repeats (.refl (m + 1))
          (LeafDomain slots) clean (fun i => (tape i).1 row))
        (fun i => if hi : ¬ clean i then (tape ⟨i, hi⟩).2 else fun _ _ => 0)
  | n + 1, _, .step i p, slots, clean, tape =>
      WholeArraySampler.assemble slots rows
        (BucketSampler.evaluate (rows (n + 1))
          (CutSamplerReplay.evaluateSpace F2 repeats (.step i p) (LeafDomain slots) clean) tape.1)
        (WholeArraySampler.childrenAt slots rows i
          (evaluateArrays rows repeats p (childSlots slots i) clean tape.2.1) tape.2.2)

def bucketSpace (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (tape : Tape rows repeats (.step i p) slots clean)
    (bucket : BucketSampler.Direction (rows (n + 1))) : H slots :=
  CutSamplerReplay.evaluateSpace F2 repeats (.step i p) (LeafDomain slots) clean
    (tape.1 bucket)

end
end PerfectCompleteness.WholeCutReplay

end

section

namespace PerfectCompleteness.WholeCutReplayTransport

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open CutSamplerKeyLocality
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def arraysTransport (rows : Nat → Nat)
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (e : ∀ s, LeafDomain slots s ≃ LeafDomain target s)
    (arrays : Arrays slots rows) : Arrays target rows :=
  fun node row => (RecursiveSpaceEquiv.spaceEquiv (𝕜 := F2)
    (fun s => e ((Nodes.path node).slotEmbedding s))).symm (arrays node row)

def transport (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
    (slots target : Slots branch n → Fin t → MixedSupport.Slot) →
    (clean : Fin (branch m) → Prop) →
    (∀ s, keptLeaf p clean s → LeafDomain slots s ≃ LeafDomain target s) →
    WholeCutReplay.Tape rows repeats p slots clean →
      WholeCutReplay.Tape rows repeats p target clean
  | _, _, .refl _, slots, target, _, e, tape =>
      fun i =>
        (fun q => (RecursiveSpaceEquiv.squareEquiv (𝕜 := F2)
          (fun s => e (i.val, s) i.property)).symm ((tape i).1 q),
          arraysTransport rows (childSlots slots i.val) (childSlots target i.val)
            (fun s => e (i.val, s) i.property) (tape i).2)
  | _, _, .step i p, slots, target, clean, e, tape =>
      (fun v => CutSamplerReplayTransport.transport F2 repeats (.step i p)
        (LeafDomain slots) (LeafDomain target) clean e (tape.1 v),
        transport rows repeats p (childSlots slots i) (childSlots target i) clean
          (fun s hs => e (i, s) (Or.inr hs)) tape.2.1,
        fun j => arraysTransport rows (childSlots slots j.val) (childSlots target j.val)
          (fun s => e (j.val, s) (Or.inl j.property)) (tape.2.2 j))

end
end PerfectCompleteness.WholeCutReplayTransport

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeCutReplayKeys
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeCutReplayKeys

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open CutSamplerKeyLocality
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat} {Y : Type*}

def leafEquiv (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf p clean s → slots s = target s)
    (s : Slots branch n) (hkeep : keptLeaf p clean s) :
    LeafDomain slots s ≃ LeafDomain target s :=
  Equiv.cast (congrArg MixedSupport.Assignment (hs s hkeep))

def transportTape (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf p clean s → slots s = target s)
    (tape : WholeCutReplay.Tape rows repeats p slots clean) :
    WholeCutReplay.Tape rows repeats p target clean :=
  WholeCutReplayTransport.transport rows repeats p slots target clean
    (leafEquiv p slots target clean hs) tape

end
end PerfectCompleteness.WholeCutReplayKeys

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_CutSlotAssembly
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_refl _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_refl_right _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_step _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_castSucc _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_last _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.NodeEmbedding.embed_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.embeddedRows_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.equiv_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.matrix_evaluate _root_.OAI.PerfectCompleteness.NodeEmbedding.rowsEquiv_apply _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutSlotAssembly

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces

variable {branch : Nat → Nat} {n m : Nat} {V : Type*}

def fill : {n m : Nat} → Path branch n m →
    (Slots branch n → V) → (Slots branch m → V) → Slots branch n → V
  | _, _, .refl _, _, inside, s => inside s
  | _, _, .step i p, outside, inside, s =>
      if s.1 = i then fill p (fun j => outside (i, j)) inside s.2 else outside s

@[simp] theorem fill_at_cut (p : Path branch n m)
    (outside : Slots branch n → V) (inside : Slots branch m → V)
    (s : Slots branch m) :
    fill p outside inside (p.slotEmbedding s) = inside s := by
  revert outside inside s
  induction p with
  | refl _ => intros; rfl
  | step i p ih =>
      intro outside inside s
      simp only [fill, Path.slotEmbedding]
      exact ih (fun j => outside (i, j)) inside s

theorem fill_kept_eq (p : Path branch n (m + 1))
    (outside : Slots branch n → V) (left right : Slots branch (m + 1) → V)
    (clean : Fin (branch m) → Prop)
    (h : ∀ (i : Fin (branch m)), ¬ clean i → ∀ s, left (i, s) = right (i, s)) :
    ∀ s, CutSamplerKeyLocality.keptLeaf p clean s →
      fill p outside left s = fill p outside right s := by
  revert outside left right clean h
  induction n generalizing m with
  | zero =>
      have hp := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro outside left right clean h s hs
          exact h s.1 hs s.2
      | step i p =>
          intro outside left right clean h s hs
          by_cases hi : s.1 = i
          · simp only [fill, ite_eq_left hi]
            exact ih p (fun j => outside (i, j)) left right clean h s.2
              (hs.resolve_left (not_not_intro hi))
          · simp only [fill, ite_eq_right hi]

section Replay

variable {t : Nat} (rows repeats : Nat → Nat)
  (p : Path branch n (m + 1))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)
  (reference target : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
  (clean : Fin (branch m) → Prop)
  (h : ∀ (i : Fin (branch m)), ¬ clean i → ∀ s, reference (i, s) = target (i, s))

def transport (tape : WholeCutReplay.Tape rows repeats p (fill p outside reference) clean) :
    WholeCutReplay.Tape rows repeats p (fill p outside target) clean :=
  WholeCutReplayKeys.transportTape rows repeats p (fill p outside reference)
    (fill p outside target) clean (fill_kept_eq p outside reference target clean h) tape

end Replay

end
end PerfectCompleteness.CutSlotAssembly

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CutProjectionAssembly
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.NodeEmbedding.embed_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.embeddedRows_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.equiv_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.matrix_evaluate _root_.OAI.PerfectCompleteness.NodeEmbedding.rowsEquiv_apply _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutProjectionAssembly

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces MixedSupport

variable {branch : Nat → Nat} {n m t : Nat}

def castProjection {a b c d : Slot} (hab : a = b) (hcd : c = d)
    (q : Projection a c) : Projection b d := by
  cases hab
  cases hcd
  exact q

@[simp] theorem castProjection_heq {a b c d : Slot} (hab : a = b) (hcd : c = d)
    (q : Projection a c) : HEq (castProjection hab hcd q) q := by
  cases hab
  cases hcd
  rfl

def fillProjection : {n m : Nat} → (p : Path branch n m) →
    (outside : Slots branch n → Fin t → Slot) →
    (left right : Slots branch m → Fin t → Slot) →
    (∀ s k, Projection (left s k) (right s k)) →
    ∀ s k, Projection (CutSlotAssembly.fill p outside left s k)
      (CutSlotAssembly.fill p outside right s k)
  | _, _, .refl _, _, _, _, q => q
  | _, _, .step i p, outside, left, right, q => fun s k =>
      if hs : s.1 = i then
        castProjection
          (by simp only [CutSlotAssembly.fill, ite_eq_left hs])
          (by simp only [CutSlotAssembly.fill, ite_eq_left hs])
          (fillProjection p (fun j => outside (i, j)) left right q s.2 k)
      else
        castProjection
          (by simp only [CutSlotAssembly.fill, ite_eq_right hs])
          (by simp only [CutSlotAssembly.fill, ite_eq_right hs])
          (Projection.keep (outside s k))

end
end PerfectCompleteness.CutProjectionAssembly

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanEndpointSlots
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanEndpointSlots

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces
open SourceQuestionReconstruction

variable {branch : Nat → Nat} {n h t v m : Nat} [NeZero m]
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)
  (clean : Fin (branch h) → Prop)
  (visible : Visible (E := SourceTuple m t) designated clean)

def leftInside (own : {i : Fin (branch h) // clean i} → Fin t → Fin m) :
    Slots branch (h + 1) → Fin t → MixedSupport.Slot :=
  fun s k => SourceKeys.slot clauses
    (reconstructLeft designated clean visible own s.1 s.2 k)

def rightInside (projected : Fin (branch h) → Bool)
    (own : {i : Fin (branch h) // clean i} → Fin t → Fin v) :
    Slots branch (h + 1) → Fin t → MixedSupport.Slot :=
  fun s k => SourceKeys.slot clauses
    (reconstructRight designated clean clauses projected visible own s.1 s.2 k)

omit [NeZero m] in
theorem leftInside_nonclean
    (own other : {i : Fin (branch h) // clean i} → Fin t → Fin m)
    (i : Fin (branch h)) (hi : ¬ clean i) (s : Slots branch h) :
    leftInside clauses designated clean visible own (i, s) =
      leftInside clauses designated clean visible other (i, s) := by
  funext k
  have hn : ¬ (clean i ∧ s = designated i) := fun h => hi h.1
  simp only [leftInside, reconstructLeft, reconstruct, dite_eq_right hn]

omit [NeZero m] in
theorem rightInside_nonclean (projected : Fin (branch h) → Bool)
    (own other : {i : Fin (branch h) // clean i} → Fin t → Fin v)
    (i : Fin (branch h)) (hi : ¬ clean i) (s : Slots branch h) :
    rightInside clauses designated clean visible projected own (i, s) =
      rightInside clauses designated clean visible projected other (i, s) := by
  funext k
  have hn : ¬ (clean i ∧ s = designated i) := fun h => hi h.1
  simp only [rightInside, reconstructRight, reconstruct, dite_eq_right hn]

def leftReference : Slots branch (h + 1) → Fin t → MixedSupport.Slot :=
  leftInside clauses designated clean visible (fun _ _ => 0)

def rightReference (projected : Fin (branch h) → Bool) :
    Slots branch (h + 1) → Fin t → MixedSupport.Slot :=
  rightInside clauses designated clean visible projected
    (fun _ _ => (clauses 0).variable 0)

variable (rows repeats : Nat → Nat) (p : Path branch n (h + 1))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)

def leftSlots (own : {i : Fin (branch h) // clean i} → Fin t → Fin m) :=
  CutSlotAssembly.fill p outside (leftInside clauses designated clean visible own)

def rightSlots (projected : Fin (branch h) → Bool)
    (own : {i : Fin (branch h) // clean i} → Fin t → Fin v) :=
  CutSlotAssembly.fill p outside (rightInside clauses designated clean visible projected own)

def leftReplay
    (record : WholeCutReplay.Tape rows repeats p
      (CutSlotAssembly.fill p outside (leftReference clauses designated clean visible)) clean)
    (own : {i : Fin (branch h) // clean i} → Fin t → Fin m) :
    WholeCutReplay.Tape rows repeats p
      (leftSlots clauses designated clean visible p outside own) clean :=
  CutSlotAssembly.transport rows repeats p outside
    (leftReference clauses designated clean visible)
    (leftInside clauses designated clean visible own) clean
    (leftInside_nonclean clauses designated clean visible (fun _ _ => 0) own) record

def rightReplay (projected : Fin (branch h) → Bool)
    (record : WholeCutReplay.Tape rows repeats p
      (CutSlotAssembly.fill p outside
        (rightReference clauses designated clean visible projected)) clean)
    (own : {i : Fin (branch h) // clean i} → Fin t → Fin v) :
    WholeCutReplay.Tape rows repeats p
      (rightSlots clauses designated clean visible p outside projected own) clean :=
  CutSlotAssembly.transport rows repeats p outside
    (rightReference clauses designated clean visible projected)
    (rightInside clauses designated clean visible projected own) clean
    (rightInside_nonclean clauses designated clean visible projected
      (fun _ _ => (clauses 0).variable 0) own) record

end
end PerfectCompleteness.CleanEndpointSlots

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CleanEndpointProjection
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanEndpointProjection

open scoped Classical
open RecursiveSpaces MixedSupport SourceQuestionReconstruction

noncomputable section

variable {v m t : Nat} (clauses : Fin m → SourceClause.NormalizedClause v)

def sourceProjection (projected : Bool) (e : SourceOddLists.Occurrences m t) :
    ∀ k, Projection (SourceAnswerEquiv.leftSlots clauses (SourceOddLists.left e) k)
      (SourceKeys.slot clauses (rightTuple clauses projected e k)) :=
  match projected with
  | false => fun k => Projection.keep
      (SourceAnswerEquiv.leftSlots clauses (SourceOddLists.left e) k)
  | true => SourceAnswerEquiv.slotProjection clauses e

variable {branch : Nat → Nat} {h : Nat}
  (designated : Fin (branch h) → Slots branch h)
  (clean : Fin (branch h) → Prop)
  (visible : Visible (E := SourceTuple m t) designated clean)

theorem leftInside_designated
    (own : {i : Fin (branch h) // clean i} → Fin t → Fin m)
    (i : {i : Fin (branch h) // clean i}) :
    CleanEndpointSlots.leftInside clauses designated clean visible own
        (i.val, designated i.val) =
      SourceAnswerEquiv.leftSlots clauses (own i) := by
  funext k
  exact congrArg
    (fun question : Fin t → SourceKeys.Endpoint v m => SourceKeys.slot clauses (question k))
    (reconstruct_designated designated clean (fun _ => leftTuple (v := v)) visible
      (fun j k => SourceKeys.Endpoint.clause (v := v) (own j k)) i)

variable (projected : Fin (branch h) → Bool)

theorem rightInside_designated
    (own : {i : Fin (branch h) // clean i} → Fin t → Fin v)
    (i : {i : Fin (branch h) // clean i}) :
    CleanEndpointSlots.rightInside clauses designated clean visible projected own
        (i.val, designated i.val) =
      SourceAnswerEquiv.rightSlots clauses (own i) := by
  funext k
  exact congrArg
    (fun question : Fin t → SourceKeys.Endpoint v m => SourceKeys.slot clauses (question k))
    (reconstruct_designated designated clean (fun j => rightTuple clauses (projected j)) visible
      (fun j k => SourceKeys.Endpoint.variable (m := m) (own j k)) i)

def insideProjection (cleanProjected : ∀ i, clean i → projected i = true)
    (e : {i : Fin (branch h) // clean i} → SourceOddLists.Occurrences m t) :
    ∀ s k, Projection
      (CleanEndpointSlots.leftInside clauses designated clean visible
        (fun i => SourceOddLists.left (e i)) s k)
      (CleanEndpointSlots.rightInside clauses designated clean visible projected
        (fun i => SourceOddLists.right clauses (e i)) s k) :=
  fun s k => if hs : clean s.1 ∧ s.2 = designated s.1 then
    CutProjectionAssembly.castProjection
      (by simp only [SourceAnswerEquiv.leftSlots, SourceOddLists.left,
        CleanEndpointSlots.leftInside, reconstructLeft, reconstruct, dite_eq_left hs])
      (by simp only [rightTuple, cleanProjected s.1 hs.1, ite_true, if_true,
        CleanEndpointSlots.rightInside, reconstructRight, reconstruct, dite_eq_left hs,
        SourceOddLists.right])
      (sourceProjection clauses (projected s.1) (e ⟨s.1, hs.1⟩) k)
  else
    CutProjectionAssembly.castProjection
      (by simp only [SourceAnswerEquiv.leftSlots, SourceOddLists.left,
        CleanEndpointSlots.leftInside, reconstructLeft, reconstruct, dite_eq_right hs, leftTuple])
      (by simp only [CleanEndpointSlots.rightInside, reconstructRight, reconstruct, dite_eq_right hs])
      (sourceProjection clauses (projected s.1) (visible s.1 ⟨s.2, hs⟩) k)

end
end PerfectCompleteness.CleanEndpointProjection

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_RepresentativeBucketCollisionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.DenseWitnessRealization

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open ClauseSupport MixedSupport CanonicalKeys
open DirectionQuotient (F2)
open ManyGoodRows PartialTableInverse

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype


variable {n : Nat} {K Z : Type*} [AddCommGroup K] [Module F2 K]
  (slots : Fin n → Slot) (H : Submodule F2 (Assignment slots → F2))
  (other : Assignment slots → Z) (σ : KeyStrategy.Strategy n)
  (W : Submodule F2 H) (s : (H ⧸ W) →ₗ[F2] H)
  [FiniteDimensional F2 H] [FiniteDimensional F2 K]
  [Fintype H] [Fintype K] [Fintype Z]
  (useful : (Module.Dual F2 (H ⧸ W) →ₗ[F2] K) → Prop)
  {r : Nat} {ρ : ℝ} {A : RowMap K r}
  {U : Module.Dual F2 (H ⧸ W) →ₗ[F2] (Fin r → F2)}

abbrev RepresentativeWitness :=
  Witness (RepresentativeMatrixTable.partialTable slots H other σ W s useful) r ρ A U

end
end PerfectCompleteness.DenseWitnessRealization

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LeftDecoder
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.LeftDecoder

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open ClauseSupport MixedSupport

noncomputable section

section Affine

variable {V : Type*} [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 V]

attribute [local instance] OAI.PerfectCompleteness.LeftDecoder.dualFintype
def affineLaw (W : Submodule F2 V)
    (C : Submodule F2 (Module.Dual F2 (V ⧸ W))) (center : Module.Dual F2 V) :
    FiniteDistribution (Module.Dual F2 V) :=
  (FiniteDistribution.uniform (PulledColumnSpace.Candidates W C center)).pushforward Subtype.val

end Affine


attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

variable {n : Nat} {K Z : Type*} [AddCommGroup K] [Module F2 K]
  (slots : Fin n → Slot) (H : Submodule F2 (Assignment slots → F2))
  (other : Assignment slots → Z) (labeling : KeyStrategy.Strategy n)
  (W : Submodule F2 H) (s : (H ⧸ W) →ₗ[F2] H)
  (hs : W.mkQ.comp s = LinearMap.id)
  [FiniteDimensional F2 H] [FiniteDimensional F2 K]
  [Fintype H] [Fintype K] [Fintype Z]
  (useful : (Module.Dual F2 (H ⧸ W) →ₗ[F2] K) → Prop)
  {r : Nat} {ρ : ℝ} {A : ManyGoodRows.RowMap K r}
  {U : Module.Dual F2 (H ⧸ W) →ₗ[F2] (Fin r → F2)}

local instance representativeDualFintype : Fintype (Module.Dual F2 H) :=
  dualFintype (V := H)

def center (w : DenseWitnessRealization.RepresentativeWitness
    slots H other labeling W s useful (r := r) (ρ := ρ) (A := A) (U := U)) :
    Module.Dual F2 H :=
  RepresentativeMatrixTable.correctionFunctional slots H other W s hs w.value.2

def law (w : DenseWitnessRealization.RepresentativeWitness
    slots H other labeling W s useful (r := r) (ρ := ρ) (A := A) (U := U)) :
    FiniteDistribution (Module.Dual F2 H) :=
  affineLaw W w.columnSpace (center slots H other labeling W s hs useful w)

omit [FiniteDimensional F2 K] [Fintype Z]

def adviceLaw (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap K r)
    (U : Module.Dual F2 (H ⧸ W) →ₗ[F2] (Fin r → F2)) :
    FiniteDistribution (Module.Dual F2 H) :=
  if hgood : ManyGoodRows.GoodRow
      (RepresentativeMatrixTable.partialTable slots H other labeling W s useful) r ρ A U then
    law slots H other labeling W s hs useful
      (ManyGoodRows.selectWitness
        (RepresentativeMatrixTable.partialTable slots H other labeling W s useful) r ρ A U hgood)
  else
    affineLaw W ⊥ (RepresentativeMatrixTable.correctionFunctional slots H other W s hs
      (CanonicalMatrixTable.response slots H other labeling (0 : CanonicalMatrixTable.Matrix
        (K := K) slots H)).2)


end

end PerfectCompleteness.LeftDecoder

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalFrozenTablesLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HierarchicalFrozenTables

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)

variable (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)

def knownSpace : Submodule F2 (NodeEmbedding.NumberedDomain slots → F2) :=
  HierarchicalKnownRows.knownSpace slots upper background (lowerIndex upper lowerLevel)

def knownRows : Submodule F2 (NodeEmbedding.RowSpace slots upper) :=
  (knownSpace slots upper lowerLevel background).comap
    (NodeEmbedding.RowSpace slots upper).subtype

def sectionMap :
    (NodeEmbedding.RowSpace slots upper ⧸ knownRows slots upper lowerLevel background) →ₗ[F2]
      NodeEmbedding.RowSpace slots upper :=
  Classical.choose (MatrixRowQuotient.exists_section (knownRows slots upper lowerLevel background))

theorem sectionMap_spec :
    (knownRows slots upper lowerLevel background).mkQ.comp
      (sectionMap slots upper lowerLevel background) = LinearMap.id :=
  Classical.choose_spec (MatrixRowQuotient.exists_section (knownRows slots upper lowerLevel background))

abbrev QuotientMatrix :=
  Module.Dual F2 (NodeEmbedding.RowSpace slots upper ⧸ knownRows slots upper lowerLevel background)
    →ₗ[F2] Block rows upper

end
end PerfectCompleteness.HierarchicalFrozenTables



namespace PerfectCompleteness.HierarchicalUsefulness

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

noncomputable section

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)

abbrev Coarse :=
  (background : HierarchicalMatrixTable.Background (rows := rows) slots upper) ×
    HierarchicalFrozenTables.QuotientMatrix slots upper lowerLevel background

def observe (arrays : Arrays slots rows) : Coarse (rows := rows) slots upper lowerLevel :=
  ⟨HierarchicalMatrixTable.backgroundOf slots upper arrays,
    MatrixRowQuotient.projectMatrix
      (HierarchicalFrozenTables.knownRows slots upper lowerLevel
        (HierarchicalMatrixTable.backgroundOf slots upper arrays))
      (NodeEmbedding.matrix arrays upper)⟩

variable {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (arrays : Ω → Arrays slots rows)
  (lower : Ω → Bool) (κ : ℝ)

def mark (z : Coarse (rows := rows) slots upper lowerLevel) : Bool :=
  UsefulMark.useful original (fun x => observe slots upper lowerLevel (arrays x)) lower κ z

end
end PerfectCompleteness.HierarchicalUsefulness



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_HierarchicalLeftDecoder
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalLeftDecoder

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)

local instance rowSpaceFintype (node : Nodes branch n) :
    Fintype (NodeEmbedding.RowSpace slots node) := Fintype.ofFinite _

local instance nodeSpaceFintype_r70ae7a_1 (node : Nodes branch n) :
    Fintype (NodeEmbedding.NodeH slots node) := Fintype.ofFinite _
local instance upperDualFintype : Fintype (Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)

variable (hbranch : ∀ k < n, 0 < branch k)

def output (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (q : Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :
    Module.Dual F2 (squareSpace (NodeEmbedding.NodeH slots (LowerNode upper lowerLevel d))) :=
  q.comp (squareEmbedding slots upper lowerLevel hbranch d)

variable (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)

def testedMatrix (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :
    Module.Dual F2 (NodeEmbedding.NodeH slots (LowerNode upper lowerLevel d)) →ₗ[F2]
      Block rows (LowerNode upper lowerLevel d) :=
  EvaluationMatrix.ofRows (NodeEmbedding.NodeH slots (LowerNode upper lowerLevel d))
    (background (HierarchicalFrozenTables.lowerIndex upper lowerLevel d))

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : HierarchicalFrozenTables.QuotientMatrix slots upper lowerLevel background → Prop)

def adviceLaw (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
    (U : Module.Dual F2 (NodeEmbedding.RowSpace slots upper ⧸
      HierarchicalFrozenTables.knownRows slots upper lowerLevel background) →ₗ[F2]
        (Fin r → F2)) : FiniteDistribution (Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :=
  LeftDecoder.adviceLaw (TreeCanonical.numberedSlots slots) (NodeEmbedding.RowSpace slots upper)
    (HierarchicalMatrixTable.other slots upper background) σ
    (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
    (HierarchicalFrozenTables.sectionMap slots upper lowerLevel background)
    (HierarchicalFrozenTables.sectionMap_spec slots upper lowerLevel background) useful r ρ A U

end
end PerfectCompleteness.HierarchicalLeftDecoder

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_DecoderContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.DecoderContraction

open scoped TensorProduct Classical
open TensorCosetEvaluation
open PointwiseSpaces RecursiveSpaces

noncomputable section

variable {K H : Type*} [AddCommGroup K] [Module F2 K]
  [AddCommGroup H] [Module F2 H]

def contract (W : Submodule F2 K) (σ : Module.Dual F2 K)
    (Φ : Module.Dual F2 (W ⊗[F2] H)) : Module.Dual F2 H :=
  if hσ : σ.comp W.subtype ≠ 0 then scalarRestriction Φ (chosenRow W σ hσ) else 0


end
end PerfectCompleteness.DecoderContraction

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_TensorBucketEvaluationLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.TensorBucketEvaluation

open scoped BigOperators TensorProduct Classical

noncomputable section

abbrev F2 := BucketSampler.F2

variable {ℓ : Nat} {Ω H : Type*} [AddCommGroup H] [Module F2 H]

def tensorOutputLinear (W : Submodule F2 (Fin ℓ → F2))
    (q : Module.Dual F2 H) : (W ⊗[F2] H) →ₗ[F2] (Fin ℓ → F2) :=
  W.subtype.comp
    ((TensorProduct.rid F2 W).toLinearMap.comp
      (TensorProduct.map (LinearMap.id : W →ₗ[F2] W) q))

def tensorOutput (W : Submodule F2 (Fin ℓ → F2))
    (q : Module.Dual F2 H) (X : W ⊗[F2] H) : Fin ℓ → F2 :=
  tensorOutputLinear W q X

@[simp] theorem tensorOutput_tmul (W : Submodule F2 (Fin ℓ → F2))
    (q : Module.Dual F2 H) (w : W) (h : H) :
    tensorOutput W q (w ⊗ₜ[F2] h) = q h • w.val := by
  simp [tensorOutput, tensorOutputLinear]

@[simp] theorem tensorOutput_zero (W : Submodule F2 (Fin ℓ → F2))
    (q : Module.Dual F2 H) : tensorOutput W q 0 = 0 :=
  (tensorOutputLinear W q).map_zero

@[simp] theorem tensorOutput_add (W : Submodule F2 (Fin ℓ → F2))
    (q : Module.Dual F2 H) (X Y : W ⊗[F2] H) :
    tensorOutput W q (X + Y) = tensorOutput W q X + tensorOutput W q Y :=
  (tensorOutputLinear W q).map_add X Y

end

end PerfectCompleteness.TensorBucketEvaluation



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_OwnInputReferenceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.OwnInputReference

open scoped BigOperators TensorProduct Classical
open UniqueGamesTheorem.Foundations.Games
open TreeSourceSpaces HierarchicalArrays

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat) (upper lower : Nodes branch n)

variable (W : Submodule F2 (UpperVector rows upper)) (a : LowerVector rows lower)

structure Input where
  knownBuckets : HiddenBucketBias.VisibleDirection W → UpperSpace slots upper
  otherArrays : OtherArrays slots rows upper lower
  lowerQuotient : Domain (nodeSlots slots lower) → DirectionQuotient.Space a

def readInput {Ω : Type*} (eval : Ω → UpperSpace slots upper)
    (data : HiddenBucketBias.VisibleTape W Ω × Exterior slots rows upper lower) :
    Input slots rows upper lower W a where
  knownBuckets v := eval (data.1 v)
  otherArrays := data.2.otherArrays
  lowerQuotient x := DirectionQuotient.proj a
    (fun i => (data.2.lowerRows i).val x)

abbrev SideOutput := DirectionQuotient.Space a ×
  ((node : OtherNodes upper lower) → Block rows node.1)

def sideFunction (input : Input slots rows upper lower W a) :
    Domain slots → SideOutput rows upper lower a :=
  fun x =>
    (input.lowerQuotient (restrictNode slots lower x),
      fun node row => (input.otherArrays node row).val (restrictNode slots node.1 x))

def knownOutput (input : Input slots rows upper lower W a)
    (x : Domain (nodeSlots slots upper)) : UpperVector rows upper :=
  ∑ v : HiddenBucketBias.VisibleDirection W,
    (input.knownBuckets v).val x • v.val.val

def query (input : Input slots rows upper lower W a)
    (X : W ⊗[F2] UpperSpace slots upper) :
    Domain slots → UpperVector rows upper × SideOutput rows upper lower a :=
  fun x =>
    (knownOutput slots rows upper lower W a input (restrictNode slots upper x) +
      TensorBucketEvaluation.tensorOutput W
        (EvaluationMatrix.evaluation (UpperSpace slots upper) (restrictNode slots upper x)) X,
     sideFunction slots rows upper lower W a input x)

def response (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (input : Input slots rows upper lower W a)
    (X : W ⊗[F2] UpperSpace slots upper) : UpperVector rows upper :=
  (KeyStrategy.response labeling .right (TreeCanonical.numberedSlots slots)
    (TreeCanonical.numberedFunction slots (query slots rows upper lower W a input X))).1

def referenceLaw (repeats : Nat → Nat) (cut : Cut upper lower) :
    FiniteDistribution (W ⊗[F2] UpperSpace slots upper) :=
  HiddenBucketBias.recursiveLaw W repeats cut.path (LeafDomain (nodeSlots slots upper))

instance frequencyFintype : Fintype (Module.Dual F2 (W ⊗[F2] UpperSpace slots upper)) :=
  Fintype.ofInjective
    (fun f : Module.Dual F2 (W ⊗[F2] UpperSpace slots upper) =>
      (f : (W ⊗[F2] UpperSpace slots upper) → F2)) DFunLike.coe_injective

def heavyList (repeats : Nat → Nat) (cut : Cut upper lower)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (input : Input slots rows upper lower W a)
    (σ : Module.Dual F2 (UpperVector rows upper)) (threshold : ℝ) :
    Finset (Module.Dual F2 (W ⊗[F2] UpperSpace slots upper)) :=
  SmallBias.heavySet (referenceLaw slots rows upper lower W repeats cut)
    (fun Φ X => QuarterBalance.sign (Φ X))
    (fun X => QuarterBalance.sign (σ (response slots rows upper lower W a labeling input X)))
    threshold

end
end PerfectCompleteness.OwnInputReference



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_RightDecoderLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.RightDecoder

open scoped TensorProduct Classical
open UniqueGamesTheorem.Foundations.Games
open TreeSourceSpaces HierarchicalArrays OwnInputReference

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat) (upper lower : Nodes branch n)
  (W : Submodule F2 (UpperVector rows upper)) (a : LowerVector rows lower)

variable (repeats : Nat → Nat) (cut : Cut upper lower)
  (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (input : Input slots rows upper lower W a) (threshold : ℝ)

attribute [local instance] OAI.PerfectCompleteness.RightDecoder.characterFintype
attribute [local instance] OAI.PerfectCompleteness.RightDecoder.scalarFintype
def law : FiniteDistribution (Module.Dual F2 (UpperSpace slots upper)) :=
  BoundedListSampling.outputLaw
    (fun σ => heavyList slots rows upper lower W a repeats cut labeling input σ threshold)
    0 (DecoderContraction.contract W)

end
end PerfectCompleteness.RightDecoder



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_DecoderSourcePullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.DecoderSourcePullback

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces OwnInputReference
open ChildBlockProjection

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  {slots projected : Slots branch n → Fin t → MixedSupport.Slot}

theorem upperBranch (upper : Nodes branch n) (hbranch : ∀ k < n, 0 < branch k) :
    ∀ k < Nodes.height upper, 0 < branch k :=
  fun k hk => hbranch k (Nat.lt_of_lt_of_le hk (Nodes.height_le upper))


end
end PerfectCompleteness.DecoderSourcePullback

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeArraySubtreeSplit
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalCutCalls.card_refl _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset _root_.OAI.PerfectCompleteness.TerminalCalls.card_refl _root_.OAI.PerfectCompleteness.TerminalCalls.drawIndex_refl _root_.OAI.PerfectCompleteness.TerminalCalls.drawIndex_step _root_.OAI.PerfectCompleteness.TerminalCalls.isTerminal_recursive _root_.OAI.PerfectCompleteness.TerminalCalls.isTerminal_refl _root_.OAI.PerfectCompleteness.TerminalCalls.not_isTerminal_ordinary _root_.OAI.PerfectCompleteness.TerminalCalls.terminalSubtypeEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutCalls.card_refl _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeArraySubtreeSplit

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays WholeArraySampler
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m k t : Nat}

abbrev subtreeSlots (p : Path branch n m)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Slots branch m → Fin t → MixedSupport.Slot :=
  fun s => slots (p.slotEmbedding s)

def Complement (rows repeats : Nat → Nat) :
    {n m k : Nat} → (p : Path branch n m) → (q : Path branch m k) →
      (Slots branch n → Fin t → MixedSupport.Slot) → Type
  | _, _, _, .refl _, _, _ => Unit
  | _, _, _, .step i p, q, slots =>
      RootTape rows repeats (.step i (p.append q)) slots ×
        (((j : RecursiveSampler.OffPath i) → Arrays (childSlots slots j.val) rows) ×
          Complement rows repeats p q (childSlots slots i))

@[instance_reducible] def complementFintypeAux (rows repeats : Nat → Nat) :
    {n m k : Nat} → (p : Path branch n m) → (q : Path branch m k) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
        Fintype (Complement rows repeats p q slots)
  | _, _, _, .refl _, _, _ => inferInstanceAs (Fintype Unit)
  | _, _, _, .step i p, q, slots =>
      letI := complementFintypeAux rows repeats p q (childSlots slots i)
      inferInstanceAs (Fintype
        (RootTape rows repeats (.step i (p.append q)) slots ×
          (((j : RecursiveSampler.OffPath i) → Arrays (childSlots slots j.val) rows) ×
            Complement rows repeats p q (childSlots slots i))))

def splitEquiv (rows repeats : Nat → Nat) :
    {n m k : Nat} → (p : Path branch n m) → (q : Path branch m k) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
        Tape rows repeats (p.append q) slots ≃
          Complement rows repeats p q slots × Tape rows repeats q (subtreeSlots p slots)
  | _, _, _, .refl _, _, _ =>
      { toFun := fun ω => ((), ω)
        invFun := Prod.snd
        left_inv := fun _ => rfl
        right_inv := by rintro ⟨u, ω⟩; cases u; rfl }
  | _, _, _, .step i p, q, slots =>
      let e := splitEquiv rows repeats p q (childSlots slots i)
      { toFun := fun ω =>
          ((ω (.inl ()), (fun j => ω (.inr (.inr j)),
              (e (ω (.inr (.inl ())))).1)),
            (e (ω (.inr (.inl ())))).2)
        invFun := fun x field => match field with
          | .inl _ => x.1.1
          | .inr (.inl _) => e.symm (x.1.2.2, x.2)
          | .inr (.inr j) => x.1.2.1 j
        left_inv := by
          intro ω
          funext field
          rcases field with u | (u | j)
          · cases u
            rfl
          · cases u
            exact e.symm_apply_apply (ω (.inr (.inl ())))
          · rfl
        right_inv := by
          rintro ⟨⟨root, ordinary, lower⟩, selected⟩
          change ((root, (ordinary, (e (e.symm (lower, selected))).1)),
            (e (e.symm (lower, selected))).2) = ((root, (ordinary, lower)), selected)
          rw [e.apply_symm_apply]
          rfl }

def extract (rows repeats : Nat → Nat) (p : Path branch n m) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (ω : Tape rows repeats (p.append q) slots) :
    Tape rows repeats q (subtreeSlots p slots) :=
  (splitEquiv rows repeats p q slots ω).2

@[simp] theorem extract_refl (rows repeats : Nat → Nat) (q : Path branch n k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (ω : Tape rows repeats q slots) :
    extract rows repeats (.refl n) q slots ω = ω := rfl

@[simp] theorem extract_step (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (q : Path branch m k)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : Tape rows repeats ((Path.step i p).append q) slots) :
    extract rows repeats (.step i p) q slots ω =
      extract rows repeats p q (childSlots slots i) (ω (.inr (.inl ()))) := rfl

def restrictArrays (rows : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
        Arrays slots rows → Arrays (subtreeSlots p slots) rows
  | _, _, .refl _, _, arrays => arrays
  | _, _, .step i p, slots, arrays =>
      restrictArrays rows p (childSlots slots i) (fun node => arrays (.inr (i, node)))

end
end PerfectCompleteness.WholeArraySubtreeSplit

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_WholeArrayHiddenLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeArrayHiddenLaw

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open TreeSourceSpaces HierarchicalArrays DescendantSpaces WholeArraySampler

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

abbrev RestIndex (i : Fin (branch n)) :=
  {k : StepIndex i // k ≠ Sum.inl ()}

abbrev Factor (rows repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot) :=
  StepFactor (i := i) (RootTape rows repeats (.step i p) slots)
    (Tape rows repeats p (childSlots slots i))
    (fun j => Arrays (childSlots slots j.val) rows)

instance factorFintype (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    (k : StepIndex i) → Fintype (Factor rows repeats i p slots k) :=
  fun k => WholeArraySampler.stepFactorFintype _ _ _ k

abbrev RestTape (rows repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot) :=
  (k : RestIndex i) → Factor rows repeats i p slots k.val

instance restTapeFintype (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    Fintype (RestTape rows repeats i p slots) := by
  letI : (k : RestIndex i) → Fintype (Factor rows repeats i p slots k.val) :=
    fun k => factorFintype rows repeats i p slots k.val
  change Fintype ((k : RestIndex i) → Factor rows repeats i p slots k.val)
  infer_instance

abbrev ScalarTape (repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot) :=
  RecursiveSampler.Tape F2 repeats (.step i p) (LeafDomain slots)

def split (rows repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows (n + 1)) → F2))
    (ω : Tape rows repeats (.step i p) slots) :
    HiddenBucketBias.HiddenTape W (ScalarTape repeats i p slots) ×
      (HiddenBucketBias.VisibleTape W (ScalarTape repeats i p slots) ×
        RestTape rows repeats i p slots) :=
  ((HiddenBucketBias.splitTape W _ (ω (.inl ()))).1,
    ((HiddenBucketBias.splitTape W _ (ω (.inl ()))).2, fun k => ω k.val))

end
end PerfectCompleteness.WholeArrayHiddenLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_WholeArrayInteriorHiddenLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeArrayInteriorHiddenLaw

open TreeSourceSpaces HierarchicalArrays DescendantSpaces WholeArraySampler
open WholeArraySubtreeSplit
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {N n m t : Nat}

abbrev ScalarTape (repeats : Nat → Nat) (p : Path branch N (n + 1))
    (i : Fin (branch n)) (q : Path branch n m)
    (slots : RecursiveSpaces.Slots branch N → Fin t → MixedSupport.Slot) :=
  WholeArrayHiddenLaw.ScalarTape repeats i q (subtreeSlots p slots)

abbrev Exterior (rows repeats : Nat → Nat) (p : Path branch N (n + 1))
    (i : Fin (branch n)) (q : Path branch n m)
    (slots : RecursiveSpaces.Slots branch N → Fin t → MixedSupport.Slot) :=
  Complement rows repeats p (.step i q) slots ×
    WholeArrayHiddenLaw.RestTape rows repeats i q (subtreeSlots p slots)

def split (rows repeats : Nat → Nat) (p : Path branch N (n + 1))
    (i : Fin (branch n)) (q : Path branch n m)
    (slots : RecursiveSpaces.Slots branch N → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows (n + 1)) → F2))
    (ω : Tape rows repeats (p.append (.step i q)) slots) :
    HiddenBucketBias.HiddenTape W (ScalarTape repeats p i q slots) ×
      (HiddenBucketBias.VisibleTape W (ScalarTape repeats p i q slots) ×
        Exterior rows repeats p i q slots) :=
  let subtree := splitEquiv rows repeats p (.step i q) slots ω
  let buckets := WholeArrayHiddenLaw.split rows repeats i q (subtreeSlots p slots) W subtree.2
  (buckets.1, (buckets.2.1, (subtree.1, buckets.2.2)))

end
end PerfectCompleteness.WholeArrayInteriorHiddenLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeArrayInteriorExteriorLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalCutCalls.card_refl _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset _root_.OAI.PerfectCompleteness.TerminalCalls.card_refl _root_.OAI.PerfectCompleteness.TerminalCalls.drawIndex_refl _root_.OAI.PerfectCompleteness.TerminalCalls.drawIndex_step _root_.OAI.PerfectCompleteness.TerminalCalls.isTerminal_recursive _root_.OAI.PerfectCompleteness.TerminalCalls.isTerminal_refl _root_.OAI.PerfectCompleteness.TerminalCalls.not_isTerminal_ordinary _root_.OAI.PerfectCompleteness.TerminalCalls.terminalSubtypeEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutCalls.card_refl _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.WholeArrayInteriorExterior

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays WholeArraySampler
open WholeArraySubtreeSplit
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {N n m t : Nat}

def upperNode : {N n : Nat} → Path branch N (n + 1) → Nodes branch N
  | _, _, .refl _ => .inl ()
  | _, _, .step j p => .inr (j, upperNode p)

@[simp] theorem upperNode_refl :
    upperNode (DescendantSpaces.Path.refl (n + 1) : Path branch (n + 1) (n + 1)) =
      (Sum.inl () : Nodes branch (n + 1)) := rfl

@[simp] theorem upperNode_step (j : Fin (branch N)) (p : Path branch N (n + 1)) :
    upperNode (.step j p) = .inr (j, upperNode p) := rfl

@[simp] theorem upperNode_height :
    {N n : Nat} → (p : Path branch N (n + 1)) → Nodes.height (upperNode p) = n + 1
  | _, _, .refl _ => rfl
  | _, _, .step _ p => upperNode_height p

def selectedNode : {N h : Nat} → (p : Path branch N h) → 0 < h → Nodes branch N
  | _, 0, _, hpos => False.elim (Nat.not_lt_zero _ hpos)
  | _, _ + 1, p, _ => upperNode p

@[simp] theorem selectedNode_succ (p : Path branch N (n + 1)) (hpos : 0 < n + 1) :
    selectedNode p hpos = upperNode p := rfl

theorem selectedNode_step {h : Nat} (j : Fin (branch N)) (p : Path branch N h)
    (hpos : 0 < h) :
    selectedNode (.step j p) hpos = .inr (j, selectedNode p hpos) := by
  cases h with
  | zero => exact False.elim (Nat.not_lt_zero _ hpos)
  | succ h => rfl

@[simp] theorem selectedNode_nodePath :
    {N : Nat} → (node : Nodes branch N) → (hpos : 0 < Nodes.height node) →
      selectedNode (Nodes.path node) hpos = node
  | 0, node, _ => nomatch node
  | _ + 1, .inl u, _ => by cases u; rfl
  | N + 1, .inr (j, node), hpos =>
      (selectedNode_step j (Nodes.path node) hpos).trans
        (congrArg (fun a : Nodes branch N => (Sum.inr (j, a) : Nodes branch (N + 1)))
          (selectedNode_nodePath node hpos))

end
end PerfectCompleteness.WholeArrayInteriorExterior


namespace PerfectCompleteness.SelectedArrayReplacement

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArraySubtreeSplit WholeArrayInteriorExterior
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def selectedRows (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (arrays : Arrays slots rows) :
    Fin (rows (m + 1)) → H (subtreeSlots p slots) :=
  restrictArrays rows p slots arrays (.inl ())

def replace (rows : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) → Arrays slots rows →
        (Fin (rows (m + 1)) → H (subtreeSlots p slots)) → Arrays slots rows
  | _, _, .refl _, slots, arrays, fresh =>
      WholeArraySampler.assemble slots rows fresh
        (fun child node => arrays (.inr (child, node)))
  | _, _, .step i p, slots, arrays, fresh =>
      WholeArraySampler.assemble slots rows (arrays (.inl ()))
        (WholeArraySampler.childrenAt slots rows i
          (replace rows p (childSlots slots i) (fun node => arrays (.inr (i, node))) fresh)
          (fun child node => arrays (.inr (child.val, node))))

@[simp] theorem selectedRows_refl (rows : Nat → Nat)
    (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) (arrays : Arrays slots rows) :
    selectedRows rows (.refl (m + 1)) slots arrays = arrays (.inl ()) := rfl

@[simp] theorem selectedRows_step (rows : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) (arrays : Arrays slots rows) :
    selectedRows rows (.step i p) slots arrays =
      selectedRows rows p (childSlots slots i) (fun node => arrays (.inr (i, node))) := rfl

@[simp] theorem selectedRows_assemble_refl (rows : Nat → Nat)
    (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (root : Fin (rows (m + 1)) → H slots)
    (children : ∀ child, Arrays (childSlots slots child) rows) :
    selectedRows rows (.refl (m + 1)) slots
      (WholeArraySampler.assemble slots rows root children) = root := rfl

@[simp] theorem selectedRows_assemble_step (rows : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (root : Fin (rows (n + 1)) → H slots) (selected : Arrays (childSlots slots i) rows)
    (ordinary : ∀ child : RecursiveSampler.OffPath i, Arrays (childSlots slots child.val) rows) :
    selectedRows rows (.step i p) slots
        (WholeArraySampler.assemble slots rows root
          (WholeArraySampler.childrenAt slots rows i selected ordinary)) =
      selectedRows rows p (childSlots slots i) selected := by
  exact congrArg (selectedRows rows p (childSlots slots i))
    (WholeArraySampler.childrenAt_selected slots rows i selected ordinary)

@[simp] theorem replace_assemble_refl (rows : Nat → Nat)
    (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (root : Fin (rows (m + 1)) → H slots)
    (children : ∀ child, Arrays (childSlots slots child) rows)
    (fresh : Fin (rows (m + 1)) → H slots) :
    replace rows (.refl (m + 1)) slots
        (WholeArraySampler.assemble slots rows root children) fresh =
      WholeArraySampler.assemble slots rows fresh children := rfl

@[simp] theorem selectedRows_replace (rows : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (slots : Slots branch n → Fin t → MixedSupport.Slot) (arrays : Arrays slots rows)
      (fresh : Fin (rows (m + 1)) → H (subtreeSlots p slots)),
      selectedRows rows p slots (replace rows p slots arrays fresh) = fresh := by
  induction n generalizing m with
  | zero => cases p
  | succ n ih =>
      cases p with
      | refl => intro slots arrays fresh; rfl
      | step i p =>
          intro slots arrays fresh
          exact (selectedRows_assemble_step rows i p slots (arrays (.inl ()))
            (replace rows p (childSlots slots i) (fun node => arrays (.inr (i, node))) fresh)
            (fun child node => arrays (.inr (child.val, node)))).trans
              (ih p (childSlots slots i) (fun node => arrays (.inr (i, node))) fresh)

end
end PerfectCompleteness.SelectedArrayReplacement

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeArrayPositiveSplit
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeArrayPositiveSplit

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays WholeArraySampler
open WholeArraySubtreeSplit
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {N h k t : Nat}

abbrev ScalarTape (repeats : Nat → Nat) (p : Path branch N h) (q : Path branch h k)
    (slots : Slots branch N → Fin t → MixedSupport.Slot) :=
  RecursiveSampler.Tape F2 repeats q (LeafDomain (subtreeSlots p slots))

def RestTape (rows repeats : Nat → Nat) :
    {h k : Nat} → (q : Path branch h k) →
      (Slots branch h → Fin t → MixedSupport.Slot) → Type
  | _, _, .refl _, _ => Unit
  | _, _, .step i q, slots => WholeArrayHiddenLaw.RestTape rows repeats i q slots

@[instance_reducible] def restTapeFintypeAux (rows repeats : Nat → Nat) :
    {h k : Nat} → (q : Path branch h k) →
      (slots : Slots branch h → Fin t → MixedSupport.Slot) →
        Fintype (RestTape rows repeats q slots)
  | _, _, .refl _, _ => inferInstanceAs (Fintype Unit)
  | _, _, .step i q, slots => WholeArrayHiddenLaw.restTapeFintype rows repeats i q slots

abbrev Exterior (rows repeats : Nat → Nat) (p : Path branch N h) (q : Path branch h k)
    (slots : Slots branch N → Fin t → MixedSupport.Slot) :=
  Complement rows repeats p q slots × RestTape rows repeats q (subtreeSlots p slots)

def split (rows repeats : Nat → Nat) (p : Path branch N h) (q : Path branch h k)
    (hproper : k < h) (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows h) → F2))
    (ω : Tape rows repeats (p.append q) slots) :
    HiddenBucketBias.HiddenTape W (ScalarTape repeats p q slots) ×
      (HiddenBucketBias.VisibleTape W (ScalarTape repeats p q slots) ×
        Exterior rows repeats p q slots) := by
  cases q with
  | refl => exact False.elim ((Nat.lt_irrefl _) hproper)
  | step i q => exact WholeArrayInteriorHiddenLaw.split rows repeats p i q slots W ω

end
end PerfectCompleteness.WholeArrayPositiveSplit

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeReplaySubtreeLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BucketUniform.evaluateLinear_apply _root_.OAI.PerfectCompleteness.BucketUsefulCollision.fill_self _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeReplaySubtree

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArraySubtreeSplit

noncomputable section

variable {branch : Nat → Nat} {n k m t : Nat}

def extract (rows repeats : Nat → Nat) :
    {n k m : Nat} → (pUp : Path branch n k) → (pDown : Path branch k (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
      (clean : Fin (branch m) → Prop) →
      WholeCutReplay.Tape rows repeats (pUp.append pDown) slots clean →
        WholeCutReplay.Tape rows repeats pDown (subtreeSlots pUp slots) clean
  | _, _, _, .refl _, _, _, _, tape => tape
  | _, _, _, .step i pUp, pDown, slots, clean, tape =>
      extract rows repeats pUp pDown (childSlots slots i) clean tape.2.1

@[simp] theorem extract_refl (rows repeats : Nat → Nat) (pDown : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (clean : Fin (branch m) → Prop)
    (tape : WholeCutReplay.Tape rows repeats pDown slots clean) :
    extract rows repeats (.refl n) pDown slots clean tape = tape := by
  cases pDown <;> rfl

@[simp] theorem extract_step (rows repeats : Nat → Nat) (i : Fin (branch n))
    (pUp : Path branch n k) (pDown : Path branch k (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) (clean : Fin (branch m) → Prop)
    (tape : WholeCutReplay.Tape rows repeats ((Path.step i pUp).append pDown) slots clean) :
    extract rows repeats (.step i pUp) pDown slots clean tape =
      extract rows repeats pUp pDown (childSlots slots i) clean tape.2.1 := rfl

def rootBuckets (rows repeats : Nat → Nat) :
    {k m : Nat} → (pDown : Path branch k (m + 1)) → m + 1 < k →
      (slots : Slots branch k → Fin t → MixedSupport.Slot) →
      (clean : Fin (branch m) → Prop) → WholeCutReplay.Tape rows repeats pDown slots clean →
        BucketSampler.Direction (rows k) → H slots
  | _, _, .refl _, hproper, _, _, _, _ => False.elim ((Nat.lt_irrefl _) hproper)
  | _, _, .step i pDown, _, slots, clean, tape, bucket =>
      WholeCutReplay.bucketSpace rows repeats i pDown slots clean tape bucket

@[simp] theorem rootBuckets_step (rows repeats : Nat → Nat) (i : Fin (branch k))
    (pDown : Path branch k (m + 1)) (hproper : m + 1 < k + 1)
    (slots : Slots branch (k + 1) → Fin t → MixedSupport.Slot) (clean : Fin (branch m) → Prop)
    (tape : WholeCutReplay.Tape rows repeats (.step i pDown) slots clean)
    (bucket : BucketSampler.Direction (rows (k + 1))) :
    rootBuckets rows repeats (.step i pDown) hproper slots clean tape bucket =
      WholeCutReplay.bucketSpace rows repeats i pDown slots clean tape bucket := rfl

def buckets (rows repeats : Nat → Nat)
    (pUp : Path branch n k) (pDown : Path branch k (m + 1)) (hproper : m + 1 < k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (clean : Fin (branch m) → Prop)
    (tape : WholeCutReplay.Tape rows repeats (pUp.append pDown) slots clean) :
    BucketSampler.Direction (rows k) → H (subtreeSlots pUp slots) :=
  rootBuckets rows repeats pDown hproper (subtreeSlots pUp slots) clean
    (extract rows repeats pUp pDown slots clean tape)

def knownBuckets (rows repeats : Nat → Nat)
    (pUp : Path branch n k) (pDown : Path branch k (m + 1)) (hproper : m + 1 < k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (clean : Fin (branch m) → Prop)
    (W : Submodule F2 (Fin (rows k) → F2))
    (tape : WholeCutReplay.Tape rows repeats (pUp.append pDown) slots clean) :
    HiddenBucketBias.VisibleDirection W → H (subtreeSlots pUp slots) :=
  fun v => buckets rows repeats pUp pDown hproper slots clean tape v.val

def knownBucketsAtNode (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n)
    (pDown : Path branch (Nodes.height upper) (m + 1)) (hproper : m + 1 < Nodes.height upper)
    (clean : Fin (branch m) → Prop) (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
    (tape : WholeCutReplay.Tape rows repeats ((Nodes.path upper).append pDown) slots clean) :
    HiddenBucketBias.VisibleDirection W → OwnInputReference.UpperSpace slots upper :=
  knownBuckets rows repeats (Nodes.path upper) pDown hproper slots clean W tape

@[simp] theorem knownBucketsAtNode_apply (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n)
    (pDown : Path branch (Nodes.height upper) (m + 1)) (hproper : m + 1 < Nodes.height upper)
    (clean : Fin (branch m) → Prop) (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
    (tape : WholeCutReplay.Tape rows repeats ((Nodes.path upper).append pDown) slots clean)
    (v : HiddenBucketBias.VisibleDirection W) :
    knownBucketsAtNode rows repeats slots upper pDown hproper clean W tape v =
      rootBuckets rows repeats pDown hproper (nodeSlots slots upper) clean
        (extract rows repeats (Nodes.path upper) pDown slots clean tape) v.val := rfl

end
end PerfectCompleteness.WholeReplaySubtree

end

section

namespace PerfectCompleteness.WholeCutSubtree

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArraySubtreeSplit

variable {branch : Nat → Nat} {n k m t : Nat}

def extract (rows repeats : Nat → Nat) :
    {n k m : Nat} → (pUp : Path branch n k) → (pDown : Path branch k m) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
      WholeCutSampler.Tape rows repeats (pUp.append pDown) slots →
        WholeCutSampler.Tape rows repeats pDown (subtreeSlots pUp slots)
  | _, _, _, .refl _, _, _, tape => tape
  | _, _, _, .step i pUp, pDown, slots, tape =>
      extract rows repeats pUp pDown (childSlots slots i) tape.2.1

@[simp] theorem extract_refl (rows repeats : Nat → Nat) (pDown : Path branch n m)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (tape : WholeCutSampler.Tape rows repeats pDown slots) :
    extract rows repeats (.refl n) pDown slots tape = tape := rfl

@[simp] theorem extract_step (rows repeats : Nat → Nat) (i : Fin (branch n))
    (pUp : Path branch n k) (pDown : Path branch k m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (tape : WholeCutSampler.Tape rows repeats ((Path.step i pUp).append pDown) slots) :
    extract rows repeats (.step i pUp) pDown slots tape =
      extract rows repeats pUp pDown (childSlots slots i) tape.2.1 := rfl

end
end PerfectCompleteness.WholeCutSubtree

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CleanLeftDecoderLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftKeys_length _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_accepts _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightKeys_length _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.Normalization.equalityClauses_length _root_.OAI.PerfectCompleteness.Normalization.gadget_length _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanLeftDecoder

noncomputable section

open scoped BigOperators Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games

structure Exposed (branch rows repeats : Nat → Nat) (n h t v m : Nat) [NeZero m] where
  clauses : Fin m → SourceClause.NormalizedClause v
  designated : Fin (branch h) → Slots branch h
  clean : Fin (branch h) → Prop
  visible : SourceQuestionReconstruction.Visible
    (E := SourceQuestionReconstruction.SourceTuple m t) designated clean
  path : Path branch n (h + 1)
  outside : Slots branch n → Fin t → MixedSupport.Slot
  tape : WholeCutReplay.Tape rows repeats path
    (CutSlotAssembly.fill path outside
      (CleanEndpointSlots.leftReference clauses designated clean visible)) clean

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  (E : Exposed branch rows repeats n h t v m)

abbrev Own := {i : Fin (branch h) // E.clean i} → Fin t → Fin m

instance ownFintype : Fintype (Own E) := Fintype.ofFinite _

def slots (own : Own E) : Slots branch n → Fin t → MixedSupport.Slot :=
  CleanEndpointSlots.leftSlots E.clauses E.designated E.clean E.visible E.path E.outside own

def replay (own : Own E) : WholeCutReplay.Tape rows repeats E.path (slots E own) E.clean :=
  CleanEndpointSlots.leftReplay E.clauses E.designated E.clean E.visible
    rows repeats E.path E.outside E.tape own

def arrays (own : Own E) : Arrays (slots E own) rows :=
  WholeCutReplay.evaluateArrays rows repeats E.path (slots E own) E.clean (replay E own)

variable (upper : Nodes branch n) (lowerLevel : Nat)

def background (own : Own E) :
    HierarchicalMatrixTable.Background (rows := rows) (slots E own) upper :=
  HierarchicalMatrixTable.backgroundOf (slots E own) upper (arrays E own)

def upperMatrix (own : Own E) :
    HierarchicalMatrixTable.Matrix (rows := rows) (slots E own) upper :=
  NodeEmbedding.matrix (arrays E own) upper

def quotientMatrix (own : Own E) :
    HierarchicalFrozenTables.QuotientMatrix (slots E own) upper lowerLevel
      (background E upper own) :=
  MatrixRowQuotient.projectMatrix
    (HierarchicalFrozenTables.knownRows (slots E own) upper lowerLevel (background E upper own))
    (upperMatrix E upper own)

abbrev QuotientAdvice (r : Nat) (own : Own E) :=
  Module.Dual F2 (NodeEmbedding.RowSpace (slots E own) upper ⧸
    HierarchicalFrozenTables.knownRows (slots E own) upper lowerLevel (background E upper own))
      →ₗ[F2] (Fin r → F2)

def advice (r : Nat) (A : ManyGoodRows.RowMap (Block rows upper) r) (own : Own E) :
    ManyGoodRows.RowMap (Block rows upper) r × QuotientAdvice E upper lowerLevel r own :=
  (A, A.comp (quotientMatrix E upper lowerLevel own))

abbrev UpperAnswer (own : Own E) := Module.Dual F2 (NodeEmbedding.RowSpace (slots E own) upper)

local instance rowSpaceFintype_r70ae7a_1 (own : Own E) (node : Nodes branch n) :
    Fintype (NodeEmbedding.RowSpace (slots E own) node) := Fintype.ofFinite _
local instance nodeSpaceFintype_r70ae7a_2 (own : Own E) (node : Nodes branch n) :
    Fintype (NodeEmbedding.NodeH (slots E own) node) := Fintype.ofFinite _
instance upperAnswerFintype (own : Own E) : Fintype (UpperAnswer E upper own) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace (slots E own) upper)

abbrev Useful := (own : Own E) →
  HierarchicalFrozenTables.QuotientMatrix (slots E own) upper lowerLevel
    (background E upper own) → Prop

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : Useful E upper lowerLevel)

def law (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r) (own : Own E) :
    FiniteDistribution (UpperAnswer E upper own) :=
  HierarchicalLeftDecoder.adviceLaw (slots E own) upper lowerLevel (background E upper own)
    σ (useful own) r ρ (advice E upper lowerLevel r A own).1
      (advice E upper lowerLevel r A own).2

abbrev Seed := (own : Own E) → UpperAnswer E upper own

def seedLaw (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r) :
    FiniteDistribution (Seed E upper) :=
  FiniteProduct.law (I := Own E) (Ω := UpperAnswer E upper)
    (law E upper lowerLevel σ useful r ρ A)

variable (hbranch : ∀ k < n, 0 < branch k)

abbrev LowerH (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (own : Own E) :=
  NodeEmbedding.NodeH (slots E own) (HierarchicalLeftDecoder.LowerNode upper lowerLevel d)

abbrev LowerAnswer (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (own : Own E) :=
  Module.Dual F2 (squareSpace (LowerH E upper lowerLevel d own))

instance lowerAnswerFintype (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (own : Own E) : Fintype (LowerAnswer E upper lowerLevel d own) :=
  LeftDecoder.dualFintype (V := squareSpace (LowerH E upper lowerLevel d own))

def output (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (own : Own E)
    (q : UpperAnswer E upper own) : LowerAnswer E upper lowerLevel d own :=
  HierarchicalLeftDecoder.output (slots E own) upper lowerLevel hbranch d q

def form (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (own : Own E)
    (q : UpperAnswer E upper own) :
    LowerH E upper lowerLevel d own →ₗ[F2] LowerH E upper lowerLevel d own →ₗ[F2] F2 :=
  OddListExtraction.multiplicationForm (LowerH E upper lowerLevel d own)
    (output E upper lowerLevel hbranch d own q)

end
end PerfectCompleteness.CleanLeftDecoder

end

section

namespace PerfectCompleteness.CleanRightDecoder

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {N h : Nat}

def suffix (upper lower : Nodes branch N) (cut : OwnInputReference.Cut upper lower)
    (hlower : Nodes.height lower = h + 1) : Path branch (Nodes.height upper) (h + 1) :=
  hlower ▸ cut.path

theorem suffix_proper (upper lower : Nodes branch N)
    (cut : OwnInputReference.Cut upper lower) (hlower : Nodes.height lower = h + 1) :
    h + 1 < Nodes.height upper := by
  simpa only [hlower] using cut.proper

def fullPath (upper lower : Nodes branch N) (cut : OwnInputReference.Cut upper lower)
    (hlower : Nodes.height lower = h + 1) : Path branch N (h + 1) :=
  (Nodes.path upper).append (suffix upper lower cut hlower)

variable {t v m : Nat}

variable [NeZero m]
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)
  (clean : Fin (branch h) → Prop)
  (visible : SourceQuestionReconstruction.Visible
    (E := SourceQuestionReconstruction.SourceTuple m t) designated clean)
  (projected : Fin (branch h) → Bool)
  (upper lower : Nodes branch N) (cut : OwnInputReference.Cut upper lower)
  (hlower : Nodes.height lower = h + 1)
  (outside : Slots branch N → Fin t → MixedSupport.Slot)

def slots (own : OwnQuestions (t := t) (v := v) clean) :
    Slots branch N → Fin t → MixedSupport.Slot :=
  CleanEndpointSlots.rightSlots clauses designated clean visible
    (fullPath upper lower cut hlower) outside projected own

variable (rows repeats : Nat → Nat)

abbrev Record := WholeCutReplay.Tape rows repeats (fullPath upper lower cut hlower)
  (CutSlotAssembly.fill (fullPath upper lower cut hlower) outside
    (CleanEndpointSlots.rightReference clauses designated clean visible projected)) clean

variable (record : Record clauses designated clean visible projected
  upper lower cut hlower outside rows repeats)

def replay (own : OwnQuestions (t := t) (v := v) clean) :
    WholeCutReplay.Tape rows repeats (fullPath upper lower cut hlower)
      (slots clauses designated clean visible projected upper lower cut hlower outside own) clean :=
  CleanEndpointSlots.rightReplay clauses designated clean visible rows repeats
    (fullPath upper lower cut hlower) outside projected record own

def arrays (own : OwnQuestions (t := t) (v := v) clean) :
    Arrays (slots clauses designated clean visible projected upper lower cut hlower outside own) rows :=
  WholeCutReplay.evaluateArrays rows repeats (fullPath upper lower cut hlower)
    (slots clauses designated clean visible projected upper lower cut hlower outside own) clean
    (replay clauses designated clean visible projected upper lower cut hlower outside
      rows repeats record own)

def exterior (own : OwnQuestions (t := t) (v := v) clean) :
    OwnInputReference.Exterior
      (slots clauses designated clean visible projected upper lower cut hlower outside own)
      rows upper lower where
  otherArrays node := arrays clauses designated clean visible projected
    upper lower cut hlower outside rows repeats record own node.val
  lowerRows := arrays clauses designated clean visible projected
    upper lower cut hlower outside rows repeats record own lower

variable (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
  (a : OwnInputReference.LowerVector rows lower)

def knownBuckets (own : OwnQuestions (t := t) (v := v) clean) :
    HiddenBucketBias.VisibleDirection W →
      OwnInputReference.UpperSpace
        (slots clauses designated clean visible projected upper lower cut hlower outside own) upper :=
  WholeReplaySubtree.knownBucketsAtNode rows repeats
    (slots clauses designated clean visible projected upper lower cut hlower outside own)
    upper (suffix upper lower cut hlower) (suffix_proper upper lower cut hlower) clean W
    (replay clauses designated clean visible projected upper lower cut hlower outside
      rows repeats record own)

def input (own : OwnQuestions (t := t) (v := v) clean) :
    OwnInputReference.Input
      (slots clauses designated clean visible projected upper lower cut hlower outside own)
      rows upper lower W a :=
  OwnInputReference.readInput
    (slots clauses designated clean visible projected upper lower cut hlower outside own)
    rows upper lower W a id
    (knownBuckets clauses designated clean visible projected upper lower cut hlower outside
      rows repeats record W own,
      exterior clauses designated clean visible projected upper lower cut hlower outside
        rows repeats record own)

@[simp] theorem input_knownBuckets (own : OwnQuestions (t := t) (v := v) clean) :
    (input clauses designated clean visible projected upper lower cut hlower outside
      rows repeats record W a own).knownBuckets =
      knownBuckets clauses designated clean visible projected upper lower cut hlower outside
        rows repeats record W own := rfl

@[simp] theorem input_otherArrays (own : OwnQuestions (t := t) (v := v) clean)
    (node : OwnInputReference.OtherNodes upper lower) :
    (input clauses designated clean visible projected upper lower cut hlower outside
      rows repeats record W a own).otherArrays node =
      arrays clauses designated clean visible projected upper lower cut hlower outside
        rows repeats record own node.val := rfl

@[simp] theorem input_lowerQuotient (own : OwnQuestions (t := t) (v := v) clean)
    (x : Domain (nodeSlots
      (slots clauses designated clean visible projected upper lower cut hlower outside own) lower)) :
    (input clauses designated clean visible projected upper lower cut hlower outside
      rows repeats record W a own).lowerQuotient x =
      DirectionQuotient.proj a (fun row =>
        (arrays clauses designated clean visible projected upper lower cut hlower outside
          rows repeats record own lower row).val x) := rfl

abbrev Answer (own : OwnQuestions (t := t) (v := v) clean) :=
  Module.Dual F2 (OwnInputReference.UpperSpace
    (slots clauses designated clean visible projected upper lower cut hlower outside own) upper)

local instance answerFintype (own : OwnQuestions (t := t) (v := v) clean) :
    Fintype (Answer clauses designated clean visible projected upper lower cut hlower outside own) :=
  RightDecoder.scalarFintype
    (slots clauses designated clean visible projected upper lower cut hlower outside own) upper

variable (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch N t))
  (threshold : ℝ)

def kernel (own : OwnQuestions (t := t) (v := v) clean) :
    FiniteDistribution (Answer clauses designated clean visible projected
      upper lower cut hlower outside own) :=
  RightDecoder.law
    (slots clauses designated clean visible projected upper lower cut hlower outside own)
    rows upper lower W a repeats cut labeling
    (input clauses designated clean visible projected upper lower cut hlower outside
      rows repeats record W a own) threshold

abbrev Seed := (own : OwnQuestions (t := t) (v := v) clean) →
  Answer clauses designated clean visible projected upper lower cut hlower outside own

def seedLaw : FiniteDistribution
    (Seed clauses designated clean visible projected upper lower cut hlower outside) :=
  FiniteProduct.law
    (kernel clauses designated clean visible projected upper lower cut hlower outside
      rows repeats record W a labeling threshold)

variable (hbranch : ∀ k < Nodes.height upper, 0 < branch k)

abbrev Form (own : OwnQuestions (t := t) (v := v) clean) :=
  RightDecoderDescendant.Form
    (slots clauses designated clean visible projected upper lower cut hlower outside own) lower

def forms (seed : Seed clauses designated clean visible projected upper lower cut hlower outside)
    (own : OwnQuestions (t := t) (v := v) clean) :
    Form clauses designated clean visible projected upper lower cut hlower outside own :=
  RightDecoderDescendant.form
    (slots clauses designated clean visible projected upper lower cut hlower outside own)
    upper lower cut hbranch (seed own)

end
end PerfectCompleteness.CleanRightDecoder

end

section

namespace PerfectCompleteness.CleanDecoderContext

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

variable {branch : Nat → Nat} {n h : Nat}

theorem lowerHeight (upper : Nodes branch n)
    (d : HierarchicalFrozenTables.LowerNodes upper (h + 1)) :
    Nodes.height (HierarchicalLeftDecoder.LowerNode upper (h + 1) d) = h + 1 :=
  (RelativeDescendantProducts.relativeNode_height upper d.val.val).trans d.property

structure Exposed (branch rows repeats : Nat → Nat) (n h t v m : Nat) [NeZero m]
    (upper : Nodes branch n) (d : HierarchicalFrozenTables.LowerNodes upper (h + 1)) where
  clauses : Fin m → SourceClause.NormalizedClause v
  designated : Fin (branch h) → Slots branch h
  clean : Fin (branch h) → Prop
  visible : SourceQuestionReconstruction.Visible
    (E := SourceQuestionReconstruction.SourceTuple m t) designated clean
  projected : Fin (branch h) → Bool
  cleanProjected : ∀ i, clean i → projected i = true
  cut : OwnInputReference.Cut upper (HierarchicalLeftDecoder.LowerNode upper (h + 1) d)
  outside : Slots branch n → Fin t → MixedSupport.Slot
  leftTape : WholeCutReplay.Tape rows repeats
    (CleanRightDecoder.fullPath upper (HierarchicalLeftDecoder.LowerNode upper (h + 1) d)
      cut (lowerHeight upper d))
    (CutSlotAssembly.fill
      (CleanRightDecoder.fullPath upper (HierarchicalLeftDecoder.LowerNode upper (h + 1) d)
        cut (lowerHeight upper d)) outside
      (CleanEndpointSlots.leftReference clauses designated clean visible)) clean
  rightTape : CleanRightDecoder.Record clauses designated clean visible projected upper
    (HierarchicalLeftDecoder.LowerNode upper (h + 1) d) cut (lowerHeight upper d)
    outside rows repeats

variable {rows repeats : Nat → Nat} {t v m : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (E : Exposed branch rows repeats n h t v m upper d)

abbrev lower (_E : Exposed branch rows repeats n h t v m upper d) :=
  HierarchicalLeftDecoder.LowerNode upper (h + 1) d

def path : Path branch n (h + 1) :=
  CleanRightDecoder.fullPath upper (lower E) E.cut (lowerHeight upper d)

abbrev CleanChildren := {i : Fin (branch h) // E.clean i}
abbrev LeftOwn := CleanChildren E → Fin t → Fin m
abbrev RightOwn := CleanChildren E → Fin t → Fin v

def leftExposed : CleanLeftDecoder.Exposed branch rows repeats n h t v m where
  clauses := E.clauses
  designated := E.designated
  clean := E.clean
  visible := E.visible
  path := path E
  outside := E.outside
  tape := E.leftTape

abbrev leftSlots (own : LeftOwn E) := CleanLeftDecoder.slots (leftExposed E) own
abbrev rightSlots (own : RightOwn E) :=
  CleanRightDecoder.slots E.clauses E.designated E.clean E.visible E.projected
    upper (lower E) E.cut (lowerHeight upper d) E.outside own

abbrev LeftSeed := CleanLeftDecoder.Seed (leftExposed E) upper
abbrev RightSeed := CleanRightDecoder.Seed E.clauses E.designated E.clean E.visible
  E.projected upper (lower E) E.cut (lowerHeight upper d) E.outside

variable (hbranch : ∀ k < n, 0 < branch k)

def leftOutput (seed : LeftSeed E) (own : LeftOwn E) :=
  CleanLeftDecoder.output (leftExposed E) upper (h + 1) hbranch d own (seed own)

def leftForm (seed : LeftSeed E) (own : LeftOwn E) :=
  CleanLeftDecoder.form (leftExposed E) upper (h + 1) hbranch d own (seed own)

def rightForm (seed : RightSeed E) (own : RightOwn E) :=
  CleanRightDecoder.forms E.clauses E.designated E.clean E.visible E.projected
    upper (lower E) E.cut (lowerHeight upper d) E.outside
    (DecoderSourcePullback.upperBranch upper hbranch) seed own

end
end PerfectCompleteness.CleanDecoderContext

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CleanDecoderOddLists
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanDecoderOddLists

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open ChildBlockProjection CleanDecoderContext
open UniqueGamesTheorem.Foundations.Games

variable {branch rows repeats : Nat → Nat} {n h t v m s : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (E : Exposed branch rows repeats n h t v m upper d)

def nativeLeaf (_E : Exposed branch rows repeats n h t v m upper d)
    (leaf : Slots branch (h + 1)) : Slots branch (Nodes.height (lower _E)) :=
  cast (congrArg (Slots branch) (lowerHeight upper d).symm) leaf

theorem slotEmbedding_cast_target {a b c : Nat} (hab : b = c)
    (p : Path branch a b) (leaf : Slots branch c) :
    (hab ▸ p).slotEmbedding leaf =
      p.slotEmbedding (cast (congrArg (Slots branch) hab.symm) leaf) := by
  cases hab
  rfl

theorem nativeLeaf_embedding (leaf : Slots branch (h + 1)) :
    (Nodes.path (lower E)).slotEmbedding (nativeLeaf E leaf) =
      (path E).slotEmbedding leaf := by
  rw [← E.cut.slots_agree]
  unfold path CleanRightDecoder.fullPath CleanRightDecoder.suffix
  simp only [Path.slotEmbedding_append, slotEmbedding_cast_target, nativeLeaf]

theorem nativeLeaf_slots (inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (leaf : Slots branch (h + 1)) :
    nodeSlots (CutSlotAssembly.fill (path E) E.outside inside) (lower E)
      (nativeLeaf E leaf) = inside leaf := by
  change CutSlotAssembly.fill (path E) E.outside inside
    ((Nodes.path (lower E)).slotEmbedding (nativeLeaf E leaf)) = inside leaf
  rw [nativeLeaf_embedding]
  exact CutSlotAssembly.fill_at_cut (path E) E.outside inside leaf

abbrev leftNative (own : LeftOwn E) := nodeSlots (leftSlots E own) (lower E)
abbrev rightNative (own : RightOwn E) := nodeSlots (rightSlots E own) (lower E)

def designatedLeaf (i : CleanChildren E) := nativeLeaf E (i.val, E.designated i.val)

theorem leftNative_designated (own : LeftOwn E) (i : CleanChildren E) :
    leftNative E own (designatedLeaf E i) = SourceAnswerEquiv.leftSlots E.clauses (own i) := by
  exact (nativeLeaf_slots E
    (CleanEndpointSlots.leftInside E.clauses E.designated E.clean E.visible own)
    (i.val, E.designated i.val)).trans
      (CleanEndpointProjection.leftInside_designated
        E.clauses E.designated E.clean E.visible own i)

theorem rightNative_designated (own : RightOwn E) (i : CleanChildren E) :
    rightNative E own (designatedLeaf E i) = SourceAnswerEquiv.rightSlots E.clauses (own i) := by
  exact (nativeLeaf_slots E
    (CleanEndpointSlots.rightInside E.clauses E.designated E.clean E.visible E.projected own)
    (i.val, E.designated i.val)).trans
      (CleanEndpointProjection.rightInside_designated
        E.clauses E.designated E.clean E.visible E.projected own i)

def leftEncoding (own : LeftOwn E) (i : CleanChildren E) :
    LeafDomain (leftNative E own) (designatedLeaf E i) ≃ SourceOddLists.LeftLabels t :=
  NativeLeafAlphabet.nativeLeftEquiv E.clauses (own i) (leftNative_designated E own i)

def rightEncoding (own : RightOwn E) (i : CleanChildren E) :
    LeafDomain (rightNative E own) (designatedLeaf E i) ≃ SourceOddLists.RightLabels t :=
  NativeLeafAlphabet.nativeRightEquiv E.clauses (own i) (rightNative_designated E own i)

abbrev Occurrences := CleanChildren E → SourceOddLists.Occurrences m t

def leftQuestions (e : Occurrences E) : LeftOwn E := fun i => SourceOddLists.left (e i)
def rightQuestions (e : Occurrences E) : RightOwn E :=
  fun i => SourceOddLists.right E.clauses (e i)

def fullProjection (e : Occurrences E) : ∀ leaf k,
    MixedSupport.Projection (leftSlots E (leftQuestions E e) leaf k)
      (rightSlots E (rightQuestions E e) leaf k) :=
  CutProjectionAssembly.fillProjection (path E) E.outside
    (CleanEndpointSlots.leftInside E.clauses E.designated E.clean E.visible (leftQuestions E e))
    (CleanEndpointSlots.rightInside E.clauses E.designated E.clean E.visible E.projected
      (rightQuestions E e))
    (CleanEndpointProjection.insideProjection E.clauses E.designated E.clean E.visible
      E.projected E.cleanProjected e)

variable (hbranch : ∀ k < n, 0 < branch k)

def target (seed : LeftSeed E) (e : Occurrences E) :=
  DecoderSourcePullback.upperTarget (fullProjection E e) upper (seed (leftQuestions E e))

def leftResponse (positive : 0 < s) (seed : LeftSeed E) (own : LeftOwn E)
    (i : CleanChildren E) : OddLists.OddList s (SourceOddLists.LeftLabels t) :=
  OddLists.OddList.map (leftEncoding E own i)
    (SourceLocalOddLists.extract positive (leftNative E own) (leftForm E hbranch seed own)
      (designatedLeaf E i) ((leftEncoding E own i).symm (fun _ => 0)))

def rightResponse (positive : 0 < s) (seed : RightSeed E) (own : RightOwn E)
    (i : CleanChildren E) : OddLists.OddList s (SourceOddLists.RightLabels t) :=
  OddLists.OddList.map (rightEncoding E own i)
    (SourceLocalOddLists.extract positive (rightNative E own) (rightForm E hbranch seed own)
      (designatedLeaf E i) ((rightEncoding E own i).symm (fun _ => false)))

def strategy (positive : 0 < s) (leftSeed : LeftSeed E) (rightSeed : RightSeed E) :
    Strategy (LeftOwn E) (RightOwn E)
      (CleanChildren E → OddLists.OddList s (SourceOddLists.LeftLabels t))
      (CleanChildren E → OddLists.OddList s (SourceOddLists.RightLabels t)) :=
  (leftResponse E hbranch positive leftSeed, rightResponse E hbranch positive rightSeed)

end
end PerfectCompleteness.CleanDecoderOddLists

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CleanDecoderSeedLawLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanDecoderSeedLaw

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays CleanDecoderContext
open UniqueGamesTheorem.Foundations.Games

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (E : Exposed branch rows repeats n h t v m upper d)

abbrev LeftAnswer (own : LeftOwn E) :=
  CleanLeftDecoder.UpperAnswer (leftExposed E) upper own

abbrev RightAnswer (own : RightOwn E) :=
  CleanRightDecoder.Answer E.clauses E.designated E.clean E.visible E.projected
    upper (lower E) E.cut (lowerHeight upper d) E.outside own

local instance leftOwnFintype : Fintype (LeftOwn E) :=
  CleanLeftDecoder.ownFintype (leftExposed E)

local instance rightOwnFintype : Fintype (RightOwn E) :=
  inferInstanceAs (Fintype ({i : Fin (branch h) // E.clean i} → Fin t → Fin v))

local instance leftAnswerFintype (own : LeftOwn E) : Fintype (LeftAnswer E own) :=
  CleanLeftDecoder.upperAnswerFintype (leftExposed E) upper own

local instance rightAnswerFintype (own : RightOwn E) : Fintype (RightAnswer E own) :=
  RightDecoder.scalarFintype (rightSlots E own) upper

abbrev Seed := LeftSeed E × RightSeed E

instance seedFintype : Fintype (Seed E) :=
  inferInstanceAs (Fintype
    (((own : LeftOwn E) → LeftAnswer E own) ×
      ((own : RightOwn E) → RightAnswer E own)))

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : CleanLeftDecoder.Useful (leftExposed E) upper (h + 1))
  (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
  (a : OwnInputReference.LowerVector rows (lower E)) (threshold : ℝ)

def leftKernel (own : LeftOwn E) : FiniteDistribution (LeftAnswer E own) :=
  CleanLeftDecoder.law (leftExposed E) upper (h + 1) σ useful r ρ A own

def rightKernel (own : RightOwn E) : FiniteDistribution (RightAnswer E own) :=
  CleanRightDecoder.kernel E.clauses E.designated E.clean E.visible E.projected
    upper (lower E) E.cut (lowerHeight upper d) E.outside
    rows repeats E.rightTape W a σ threshold own

def leftSeedLaw : FiniteDistribution (LeftSeed E) :=
  CleanLeftDecoder.seedLaw (leftExposed E) upper (h + 1) σ useful r ρ A

def rightSeedLaw : FiniteDistribution (RightSeed E) :=
  CleanRightDecoder.seedLaw E.clauses E.designated E.clean E.visible E.projected
    upper (lower E) E.cut (lowerHeight upper d) E.outside
    rows repeats E.rightTape W a σ threshold

def seedLaw : FiniteDistribution (Seed E) :=
  (leftSeedLaw E σ useful r ρ A).product (rightSeedLaw E σ W a threshold)

end
end PerfectCompleteness.CleanDecoderSeedLaw

end

section

namespace PerfectCompleteness.OriginalDecoderMark

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

abbrev SlotFamily (branch : Nat → Nat) (n t : Nat) :=
  RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot

structure Family (branch rows : Nat → Nat) (n t : Nat)
    (Sample : SlotFamily branch n t → Type*) [∀ slots, Fintype (Sample slots)] where
  original : (slots : SlotFamily branch n t) → FiniteDistribution (Sample slots)
  arrays : (slots : SlotFamily branch n t) → Sample slots → Arrays slots rows
  lowerEvent : (slots : SlotFamily branch n t) → Sample slots → Bool

variable {branch rows : Nat → Nat} {n t : Nat}
  {Sample : SlotFamily branch n t → Type*} [∀ slots, Fintype (Sample slots)]
  (F : Family branch rows n t Sample) (upper : Nodes branch n) (lowerLevel : Nat) (κ : ℝ)

def mark (slots : SlotFamily branch n t)
    (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)
    (X : HierarchicalFrozenTables.QuotientMatrix slots upper lowerLevel background) : Prop :=
  HierarchicalUsefulness.mark slots upper lowerLevel
    (F.original slots) (F.arrays slots) (F.lowerEvent slots) κ ⟨background, X⟩ = true

variable {repeats : Nat → Nat} {h v m : Nat} [NeZero m]

def useful (E : CleanLeftDecoder.Exposed branch rows repeats n h t v m) :
    CleanLeftDecoder.Useful E upper lowerLevel :=
  fun own X => mark F upper lowerLevel κ
    (CleanLeftDecoder.slots E own) (CleanLeftDecoder.background E upper own) X

end
end PerfectCompleteness.OriginalDecoderMark

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_CutSlotOutside
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutSlotAssembly

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces

variable {branch : Nat → Nat} {n m : Nat} {V : Type*}

theorem fill_outside (p : Path branch n m)
    (outside : Slots branch n → V) (inside : Slots branch m → V)
    (s : Slots branch n) (hs : s ∉ Set.range p.slotEmbedding) :
    fill p outside inside s = outside s := by
  revert outside inside s hs
  induction p with
  | refl _ =>
      intro outside inside s hs
      exact False.elim (hs ⟨s, rfl⟩)
  | step i p ih =>
      intro outside inside s hs
      obtain ⟨j, s⟩ := s
      by_cases hji : j = i
      · subst j
        have htail : s ∉ Set.range p.slotEmbedding := by
          rintro ⟨a, ha⟩
          apply hs
          exact ⟨a, congrArg (fun b => (i, b)) ha⟩
        simpa only [fill, ite_eq_left rfl, ite_true, if_true] using
          ih (fun b => outside (i, b)) inside s htail
      · simp only [fill, ite_eq_right hji]

theorem fill_outside_eq (p : Path branch n m)
    (outside : Slots branch n → V) (left right : Slots branch m → V)
    (s : Slots branch n) (hs : s ∉ Set.range p.slotEmbedding) :
    fill p outside left s = fill p outside right s := by
  rw [fill_outside p outside left s hs, fill_outside p outside right s hs]

end
end PerfectCompleteness.CutSlotAssembly

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanRecordChildBlocks
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanRecordChildBlocks

noncomputable section

open scoped Classical
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces TreeSourceSpaces HierarchicalArrays
open SourceQuestionReconstruction

variable {branch : Nat → Nat} {h t v m : Nat} {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)

abbrev Record :=
  CleanSourceRecord.Record
    (D := SourceChildKernel.D (C := C) (t := t) rows clauses designated) designated
    (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated)

abbrev Sample := SourceChildKernel.Sample (C := C) (t := t) rows clauses designated

abbrev Row (i : Fin (branch h)) := SourceTuple m t ×
  (SourceChildKernel.Rest (m := m) (t := t) designated i ×
    SourceChildKernel.Raw (C := C) (t := t) rows clauses designated i)

def clean (record : Record (C := C) (t := t) rows clauses designated) :
    Fin (branch h) → Prop :=
  CleanSourceRecord.clean designated
    (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated) record

def visible (record : Record (C := C) (t := t) rows clauses designated) :
    Visible (E := SourceTuple m t) designated (clean rows clauses designated record) :=
  CleanSourceRecord.visible designated
    (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated) record

def projected (record : Record (C := C) (t := t) rows clauses designated) :
    Fin (branch h) → Bool :=
  CleanSourceRecord.projected designated
    (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated) record

def event (record : Record (C := C) (t := t) rows clauses designated) :
    Sample (C := C) (t := t) rows clauses designated → Bool :=
  UniformCleanSources.recordEvent
    (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated)
    (SourceChildKernel.zero (C := C) (t := t) rows clauses designated) record

abbrev Nonclean (record : Record (C := C) (t := t) rows clauses designated) :=
  {i : Fin (branch h) // ¬ clean rows clauses designated record i}

def extract (record : Record (C := C) (t := t) rows clauses designated)
    (i : Nonclean rows clauses designated record) : Row (C := C) (t := t) rows clauses designated i.val :=
  match hr : record i.val with
  | .inl row => row
  | .inr _ => False.elim (i.property (by
      simp only [clean, CleanSourceRecord.clean, hr, UniformCleanSources.cleanRecord]))

theorem record_extract (record : Record (C := C) (t := t) rows clauses designated)
    (i : Nonclean rows clauses designated record) :
    record i.val = .inl (extract rows clauses designated record i) := by
  unfold extract
  split
  · rename_i row hr
    exact hr
  · rename_i rest hr
    exact False.elim (i.property (by
      simp only [clean, CleanSourceRecord.clean, hr, UniformCleanSources.cleanRecord]))

def source (record : Record (C := C) (t := t) rows clauses designated)
    (i : Nonclean rows clauses designated record) :
    SourceChildKernel.Source (m := m) (t := t) designated i.val :=
  ((extract rows clauses designated record i).1, (extract rows clauses designated record i).2.1)

def raw (record : Record (C := C) (t := t) rows clauses designated)
    (i : Nonclean rows clauses designated record) :
    SourceChildKernel.Raw (C := C) (t := t) rows clauses designated i.val :=
  (extract rows clauses designated record i).2.2

theorem visible_nonclean (record : Record (C := C) (t := t) rows clauses designated)
    (i : Nonclean rows clauses designated record) (leaf : Slots branch h)
    (hleaf : ¬ (clean rows clauses designated record i.val ∧ leaf = designated i.val)) :
    visible rows clauses designated record i.val ⟨leaf, hleaf⟩ =
      SourceChildKernel.tree designated i.val (source rows clauses designated record i) leaf := by
  dsimp only [visible, CleanSourceRecord.visible]
  split
  · rename_i row hr
    have hrow : row = extract rows clauses designated record i :=
      Sum.inl.inj (hr.symm.trans (record_extract rows clauses designated record i))
    rw [hrow]
    rfl
  · rename_i rest hr
    have hbad := hr.symm.trans (record_extract rows clauses designated record i)
    cases hbad

theorem projected_nonclean (record : Record (C := C) (t := t) rows clauses designated)
    (i : Nonclean rows clauses designated record) :
    projected rows clauses designated record i.val =
      SourceChildKernel.rawProjected rows clauses designated i.val
        (raw rows clauses designated record i) := by
  simp only [projected, CleanSourceRecord.projected,
    record_extract rows clauses designated record i, raw,
    CleanSourceRecord.rawProjected, SourceChildKernel.rawProjected]
  cases (extract rows clauses designated record i).2.2 <;> rfl

variable [NeZero m]

def leftRef (record : Record (C := C) (t := t) rows clauses designated) :
    Slots branch (h + 1) → Fin t → MixedSupport.Slot :=
  CleanEndpointSlots.leftReference clauses designated (clean rows clauses designated record)
    (visible rows clauses designated record)

def rightRef (record : Record (C := C) (t := t) rows clauses designated) :
    Slots branch (h + 1) → Fin t → MixedSupport.Slot :=
  CleanEndpointSlots.rightReference clauses designated (clean rows clauses designated record)
    (visible rows clauses designated record) (projected rows clauses designated record)

theorem leftRef_childSlots (record : Record (C := C) (t := t) rows clauses designated)
    (i : Nonclean rows clauses designated record) :
    childSlots (leftRef rows clauses designated record) i.val =
      SourceChildKernel.nativeSlots clauses designated i.val (source rows clauses designated record i) := by
  funext leaf k
  have hn : ¬ (clean rows clauses designated record i.val ∧ leaf = designated i.val) :=
    fun h => i.property h.1
  simp only [leftRef, CleanEndpointSlots.leftReference, CleanEndpointSlots.leftInside,
    childSlots, reconstructLeft, reconstruct, dite_eq_right hn]
  rw [visible_nonclean rows clauses designated record i leaf hn]
  rfl

theorem rightRef_childSlots (record : Record (C := C) (t := t) rows clauses designated)
    (i : Nonclean rows clauses designated record) :
    childSlots (rightRef rows clauses designated record) i.val =
      SourceChildKernel.mixedSlots clauses designated i.val (source rows clauses designated record i)
        (SourceChildKernel.rawProjected rows clauses designated i.val (raw rows clauses designated record i)) := by
  funext leaf k
  have hn : ¬ (clean rows clauses designated record i.val ∧ leaf = designated i.val) :=
    fun h => i.property h.1
  simp only [rightRef, CleanEndpointSlots.rightReference, CleanEndpointSlots.rightInside,
    childSlots, reconstructRight, reconstruct, dite_eq_right hn]
  rw [visible_nonclean rows clauses designated record i leaf hn,
    projected_nonclean rows clauses designated record i]
  exact (SourceChildKernel.mixedSlots_eq_rightTuple clauses designated i.val
    (source rows clauses designated record i)
    (SourceChildKernel.rawProjected rows clauses designated i.val (raw rows clauses designated record i))
    leaf k).symm

def physicalRight (i : Fin (branch h)) (row : Row (C := C) (t := t) rows clauses designated i) :
    SourceChildKernel.Block C rows (SourceChildKernel.mixedSlots clauses designated i (row.1, row.2.1)
      (SourceChildKernel.rawProjected rows clauses designated i row.2.2)) :=
  SourceChildKernel.decodeRight rows clauses designated i (row.1, row.2.1) row.2.2

def physicalLeft (i : Fin (branch h)) (row : Row (C := C) (t := t) rows clauses designated i) :
    SourceChildKernel.Block C rows (SourceChildKernel.nativeSlots clauses designated i (row.1, row.2.1)) :=
  let p := SourceChildKernel.projection clauses designated i (row.1, row.2.1)
    (SourceChildKernel.rawProjected rows clauses designated i row.2.2)
  let block := physicalRight rows clauses designated i row
  (fun call => ChildBlockProjection.squarePullback p (block.1 call),
    ChildBlockProjection.arraysPullback rows p block.2)

def rightChild (record : Record (C := C) (t := t) rows clauses designated)
    (i : Nonclean rows clauses designated record) :
    SourceChildKernel.Block C rows (childSlots (rightRef rows clauses designated record) i.val) :=
  cast (congrArg (SourceChildKernel.Block C rows) (rightRef_childSlots rows clauses designated record i).symm)
    (physicalRight rows clauses designated i.val (extract rows clauses designated record i))

def leftChild (record : Record (C := C) (t := t) rows clauses designated)
    (i : Nonclean rows clauses designated record) :
    SourceChildKernel.Block C rows (childSlots (leftRef rows clauses designated record) i.val) :=
  cast (congrArg (SourceChildKernel.Block C rows) (leftRef_childSlots rows clauses designated record i).symm)
    (physicalLeft rows clauses designated i.val (extract rows clauses designated record i))

end
end PerfectCompleteness.CleanRecordChildBlocks

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanPhysicalReplay
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanPhysicalReplay

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {root h t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch root (h + 1))
  (outside : Slots branch root → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (h + 1) → Fin t → MixedSupport.Slot)

abbrev Exterior := WholeCutGrouping.Exterior rows repeats p
  (CutSlotAssembly.fill p outside placeholder)

def exteriorAt (inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (external : Exterior rows repeats p outside placeholder) :
    WholeCutGrouping.Exterior rows repeats p (CutSlotAssembly.fill p outside inside) :=
  WholeCutExteriorTransport.equiv rows repeats p
    (CutSlotAssembly.fill p outside placeholder) (CutSlotAssembly.fill p outside inside)
    (CutSlotAssembly.fill_outside_eq p outside placeholder inside) external

theorem cutSlots_fill (inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot) :
    WholeCutGrouping.cutSlots p (CutSlotAssembly.fill p outside inside) = inside := by
  funext s
  exact CutSlotAssembly.fill_at_cut p outside inside s

theorem childSlots_fill (inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (i : Fin (branch h)) :
    childSlots (WholeCutGrouping.cutSlots p (CutSlotAssembly.fill p outside inside)) i =
      childSlots inside i :=
  congrArg (fun ss => childSlots ss i) (cutSlots_fill p outside inside)

def fillChild (inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (i : Fin (branch h))
    (block : CutChildGrouping.Child (C := WholeCutCalls.Index rows repeats p) inside rows i) :
    CutChildGrouping.Child (C := WholeCutCalls.Index rows repeats p)
      (WholeCutGrouping.cutSlots p (CutSlotAssembly.fill p outside inside)) rows i :=
  cast (congrArg (SourceChildKernel.Block (WholeCutCalls.Index rows repeats p) rows)
    (childSlots_fill p outside inside i).symm) block

def retainedAt (inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch h) → Prop)
    (children : (i : {i : Fin (branch h) // ¬ clean i}) →
      CutChildGrouping.Child (C := WholeCutCalls.Index rows repeats p) inside rows i.val) :
    WholeCutReplayGrouping.RetainedChildren rows repeats p
      (CutSlotAssembly.fill p outside inside) clean :=
  fun i => fillChild rows repeats p outside inside i.val (children i)

def assembleAt (inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch h) → Prop)
    (external : Exterior rows repeats p outside placeholder)
    (children : (i : {i : Fin (branch h) // ¬ clean i}) →
      CutChildGrouping.Child (C := WholeCutCalls.Index rows repeats p) inside rows i.val) :
    WholeCutReplay.Tape rows repeats p (CutSlotAssembly.fill p outside inside) clean :=
  WholeCutReplayGrouping.assemble rows repeats p (CutSlotAssembly.fill p outside inside) clean
    (exteriorAt rows repeats p outside placeholder inside external)
    (retainedAt rows repeats p outside inside clean children)

def physicalTape (inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (external : Exterior rows repeats p outside placeholder)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows) :
    WholeCutSampler.Tape rows repeats p (CutSlotAssembly.fill p outside inside) :=
  (WholeCutGrouping.splitTape rows repeats p (CutSlotAssembly.fill p outside inside)).symm
    (exteriorAt rows repeats p outside placeholder inside external,
      fun i => fillChild rows repeats p outside inside i (children i))

section Source

variable {v m : Nat} [NeZero m]
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)

abbrev Record := CleanRecordChildBlocks.Record
  (C := WholeCutCalls.Index rows repeats p) (t := t) rows clauses designated

abbrev Sample := SourceChildKernel.Sample
  (C := WholeCutCalls.Index rows repeats p) (t := t) rows clauses designated

def leftRecord (record : Record (t := t) rows repeats p clauses designated)
    (external : Exterior rows repeats p outside placeholder) :
    WholeCutReplay.Tape rows repeats p
      (CutSlotAssembly.fill p outside (CleanRecordChildBlocks.leftRef rows clauses designated record))
      (CleanRecordChildBlocks.clean rows clauses designated record) :=
  assembleAt rows repeats p outside placeholder
    (CleanRecordChildBlocks.leftRef rows clauses designated record)
    (CleanRecordChildBlocks.clean rows clauses designated record) external
    (CleanRecordChildBlocks.leftChild rows clauses designated record)

def rightRecord (record : Record (t := t) rows repeats p clauses designated)
    (external : Exterior rows repeats p outside placeholder) :
    WholeCutReplay.Tape rows repeats p
      (CutSlotAssembly.fill p outside (CleanRecordChildBlocks.rightRef rows clauses designated record))
      (CleanRecordChildBlocks.clean rows clauses designated record) :=
  assembleAt rows repeats p outside placeholder
    (CleanRecordChildBlocks.rightRef rows clauses designated record)
    (CleanRecordChildBlocks.clean rows clauses designated record) external
    (CleanRecordChildBlocks.rightChild rows clauses designated record)

def leftInside (x : Sample (t := t) rows repeats p clauses designated) :
    Slots branch (h + 1) → Fin t → MixedSupport.Slot :=
  SourceChildKernel.parentLeftSlots clauses designated (fun i => ((x i).1, (x i).2.1))

def rightInside (x : Sample (t := t) rows repeats p clauses designated) :
    Slots branch (h + 1) → Fin t → MixedSupport.Slot :=
  SourceChildKernel.parentRightSlots rows clauses designated
    (fun i => ((x i).1, (x i).2.1)) (fun i => (x i).2.2)

def leftBlocks (x : Sample (t := t) rows repeats p clauses designated) :
    CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
      (leftInside rows repeats p clauses designated x) rows :=
  SourceChildKernel.leftChildren rows clauses designated
    (fun i => ((x i).1, (x i).2.1)) (fun i => (x i).2.2)

def rightBlocks (x : Sample (t := t) rows repeats p clauses designated) :
    CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
      (rightInside rows repeats p clauses designated x) rows :=
  SourceChildKernel.rightChildren rows clauses designated
    (fun i => ((x i).1, (x i).2.1)) (fun i => (x i).2.2)

def leftTape (x : Sample (t := t) rows repeats p clauses designated)
    (external : Exterior rows repeats p outside placeholder) :
    WholeCutSampler.Tape rows repeats p
      (CutSlotAssembly.fill p outside (leftInside rows repeats p clauses designated x)) :=
  physicalTape rows repeats p outside placeholder (leftInside rows repeats p clauses designated x)
    external (leftBlocks rows repeats p clauses designated x)

def rightTape (x : Sample (t := t) rows repeats p clauses designated)
    (external : Exterior rows repeats p outside placeholder) :
    WholeCutSampler.Tape rows repeats p
      (CutSlotAssembly.fill p outside (rightInside rows repeats p clauses designated x)) :=
  physicalTape rows repeats p outside placeholder (rightInside rows repeats p clauses designated x)
    external (rightBlocks rows repeats p clauses designated x)

end Source

end
end PerfectCompleteness.CleanPhysicalReplay

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanRecordObservation
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftKeys_length _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_accepts _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightKeys_length _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.Normalization.equalityClauses_length _root_.OAI.PerfectCompleteness.Normalization.gadget_length _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanRecordObservation

noncomputable section

open scoped Classical
open RecursiveSpaces TreeSourceSpaces SourceQuestionReconstruction

variable {branch : Nat → Nat} {h t v m : Nat} {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)

abbrev Record := CleanRecordChildBlocks.Record (C := C) (t := t) rows clauses designated
abbrev Sample := SourceChildKernel.Sample (C := C) (t := t) rows clauses designated

def observe (x : Sample (C := C) (t := t) rows clauses designated) :
    Record (C := C) (t := t) rows clauses designated :=
  UniformCleanSoundness.observations
    (D := SourceChildKernel.D (C := C) (t := t) rows clauses designated)
    (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated)
    (SourceChildKernel.zero (C := C) (t := t) rows clauses designated) x

theorem event_eq (record : Record (C := C) (t := t) rows clauses designated)
    (x : Sample (C := C) (t := t) rows clauses designated) :
    CleanRecordChildBlocks.event rows clauses designated record x =
      decide (observe rows clauses designated x = record) :=
  congrFun (UniformCleanSoundness.recordEvent_eq
    (D := SourceChildKernel.D (C := C) (t := t) rows clauses designated)
    (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated)
    (SourceChildKernel.zero (C := C) (t := t) rows clauses designated) record) x

@[simp] theorem event_observe (x : Sample (C := C) (t := t) rows clauses designated) :
    CleanRecordChildBlocks.event rows clauses designated
      (observe rows clauses designated x) x = true := by
  rw [event_eq]
  exact decide_eq_true rfl

def leftQuestions (record : Record (C := C) (t := t) rows clauses designated)
    (x : Sample (C := C) (t := t) rows clauses designated) :
    {i : Fin (branch h) // CleanRecordChildBlocks.clean rows clauses designated record i} →
      Fin t → Fin m :=
  fun i k => ((x i.val).1 k).1

def rightQuestions (record : Record (C := C) (t := t) rows clauses designated)
    (x : Sample (C := C) (t := t) rows clauses designated) :
    {i : Fin (branch h) // CleanRecordChildBlocks.clean rows clauses designated record i} →
      Fin t → Fin v :=
  fun i k => SourceClause.occurrenceVariable clauses ((x i.val).1 k)

theorem leftInside_eq (record : Record (C := C) (t := t) rows clauses designated)
    (x : Sample (C := C) (t := t) rows clauses designated)
    (hevent : CleanRecordChildBlocks.event rows clauses designated record x = true) :
    CleanEndpointSlots.leftInside clauses designated
      (CleanRecordChildBlocks.clean rows clauses designated record)
      (CleanRecordChildBlocks.visible rows clauses designated record)
      (leftQuestions rows clauses designated record x) =
    SourceChildKernel.parentLeftSlots clauses designated
      (fun i => ((x i).1, (x i).2.1)) := by
  have h := CleanSourceRecord.reconstructLeft_eq designated
    (D := SourceChildKernel.D (C := C) (t := t) rows clauses designated)
    (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated)
    (SourceChildKernel.zero (C := C) (t := t) rows clauses designated)
    (v := v) record x hevent
  funext s k
  exact congrArg (fun f => SourceKeys.slot clauses (f s.1 s.2 k)) h

theorem rightInside_eq (record : Record (C := C) (t := t) rows clauses designated)
    (x : Sample (C := C) (t := t) rows clauses designated)
    (hevent : CleanRecordChildBlocks.event rows clauses designated record x = true) :
    CleanEndpointSlots.rightInside clauses designated
      (CleanRecordChildBlocks.clean rows clauses designated record)
      (CleanRecordChildBlocks.visible rows clauses designated record)
      (CleanRecordChildBlocks.projected rows clauses designated record)
      (rightQuestions rows clauses designated record x) =
    SourceChildKernel.parentRightSlots rows clauses designated
      (fun i => ((x i).1, (x i).2.1)) (fun i => (x i).2.2) := by
  have h := CleanSourceRecord.reconstructRight_eq designated
    (D := SourceChildKernel.D (C := C) (t := t) rows clauses designated)
    (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated)
    (SourceChildKernel.zero (C := C) (t := t) rows clauses designated)
    clauses record x hevent
  funext s k
  refine (congrArg (fun f => SourceKeys.slot clauses (f s.1 s.2 k)) h).trans ?_
  have hflag : CleanSourceRecord.rawProjected designated
      (D := SourceChildKernel.D (C := C) (t := t) rows clauses designated)
      (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated)
      s.1 (x s.1).2.2 =
        SourceChildKernel.rawProjected rows clauses designated s.1 (x s.1).2.2 := by
    cases (x s.1).2.2 <;> rfl
  exact (congrArg (fun projected : Bool => SourceKeys.slot clauses
    (rightTuple clauses projected
      (CleanSourceRecord.sourceTree designated
        (D := SourceChildKernel.D (C := C) (t := t) rows clauses designated)
        (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated) x s.1 s.2) k)) hflag).trans
    (SourceChildKernel.mixedSlots_eq_rightTuple clauses designated s.1
      ((x s.1).1, (x s.1).2.1)
      (SourceChildKernel.rawProjected rows clauses designated s.1 (x s.1).2.2) s.2 k).symm

end
end PerfectCompleteness.CleanRecordObservation

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_CleanRecordDecoderInput
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftKeys_length _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_accepts _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightKeys_length _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.Normalization.equalityClauses_length _root_.OAI.PerfectCompleteness.Normalization.gadget_length _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanRecordDecoderInput

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

variable {branch : Nat → Nat} {n h t v m : Nat} [NeZero m]
  (rows repeats : Nat → Nat) (upper : Nodes branch n)
  (d : HierarchicalFrozenTables.LowerNodes upper (h + 1))
  (cut : OwnInputReference.Cut upper (HierarchicalLeftDecoder.LowerNode upper (h + 1) d))

abbrev path := CleanRightDecoder.fullPath upper
  (HierarchicalLeftDecoder.LowerNode upper (h + 1) d) cut
  (CleanDecoderContext.lowerHeight upper d)

variable (outside : Slots branch n → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)

abbrev Record := CleanPhysicalReplay.Record (t := t) rows repeats (path upper d cut) clauses designated
abbrev Sample := CleanPhysicalReplay.Sample (t := t) rows repeats (path upper d cut) clauses designated
abbrev Exterior := CleanPhysicalReplay.Exterior rows repeats (path upper d cut) outside placeholder

def exposed (record : Record (t := t) rows repeats upper d cut clauses designated)
    (external : Exterior rows repeats upper d cut outside placeholder) :
    CleanDecoderContext.Exposed branch rows repeats n h t v m upper d where
  clauses := clauses
  designated := designated
  clean := CleanRecordChildBlocks.clean rows clauses designated record
  visible := CleanRecordChildBlocks.visible rows clauses designated record
  projected := CleanRecordChildBlocks.projected rows clauses designated record
  cleanProjected := CleanSourceRecord.clean_projected designated
    (SourceChildKernel.Factors (C := WholeCutCalls.Index rows repeats (path upper d cut))
      (t := t) rows clauses designated) record
  cut := cut
  outside := outside
  leftTape := CleanPhysicalReplay.leftRecord rows repeats (path upper d cut) outside placeholder
    clauses designated record external
  rightTape := CleanPhysicalReplay.rightRecord rows repeats (path upper d cut) outside placeholder
    clauses designated record external

abbrev observe (x : Sample (t := t) rows repeats upper d cut clauses designated) :
    Record (t := t) rows repeats upper d cut clauses designated :=
  CleanRecordObservation.observe rows clauses designated x

omit [NeZero m] in
@[simp] theorem event_observe (x : Sample (t := t) rows repeats upper d cut clauses designated) :
    CleanRecordChildBlocks.event rows clauses designated
      (observe rows repeats upper d cut clauses designated x) x = true :=
  CleanRecordObservation.event_observe rows clauses designated x

def leftQuestions (record : Record (t := t) rows repeats upper d cut clauses designated)
    (x : Sample (t := t) rows repeats upper d cut clauses designated) :=
  CleanRecordObservation.leftQuestions rows clauses designated record x

def rightQuestions (record : Record (t := t) rows repeats upper d cut clauses designated)
    (x : Sample (t := t) rows repeats upper d cut clauses designated) :=
  CleanRecordObservation.rightQuestions rows clauses designated record x

def sources (record : Record (t := t) rows repeats upper d cut clauses designated)
    (x : Sample (t := t) rows repeats upper d cut clauses designated) :
    {i : Fin (branch h) // CleanRecordChildBlocks.clean rows clauses designated record i} →
      SourceOddLists.Occurrences m t := fun i => (x i.val).1

theorem leftSlots_eq (record : Record (t := t) rows repeats upper d cut clauses designated)
    (external : Exterior rows repeats upper d cut outside placeholder)
    (x : Sample (t := t) rows repeats upper d cut clauses designated)
    (hevent : CleanRecordChildBlocks.event rows clauses designated record x = true) :
    CleanDecoderContext.leftSlots
      (exposed rows repeats upper d cut outside placeholder clauses designated record external)
      (leftQuestions rows repeats upper d cut clauses designated record x) =
    CutSlotAssembly.fill (path upper d cut) outside
      (CleanPhysicalReplay.leftInside rows repeats (path upper d cut) clauses designated x) := by
  exact congrArg (CutSlotAssembly.fill (path upper d cut) outside)
    (CleanRecordObservation.leftInside_eq rows clauses designated record x hevent)

theorem rightSlots_eq (record : Record (t := t) rows repeats upper d cut clauses designated)
    (external : Exterior rows repeats upper d cut outside placeholder)
    (x : Sample (t := t) rows repeats upper d cut clauses designated)
    (hevent : CleanRecordChildBlocks.event rows clauses designated record x = true) :
    CleanDecoderContext.rightSlots
      (exposed rows repeats upper d cut outside placeholder clauses designated record external)
      (rightQuestions rows repeats upper d cut clauses designated record x) =
    CutSlotAssembly.fill (path upper d cut) outside
      (CleanPhysicalReplay.rightInside rows repeats (path upper d cut) clauses designated x) := by
  exact congrArg (CutSlotAssembly.fill (path upper d cut) outside)
    (CleanRecordObservation.rightInside_eq rows clauses designated record x hevent)

end
end PerfectCompleteness.CleanRecordDecoderInput

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CleanDecoderRateLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanDecoderRate

noncomputable section

open scoped BigOperators Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

structure Setup (branch rows repeats : Nat → Nat) (n h t v m : Nat) [NeZero m]
    (upper : Nodes branch n) (d : HierarchicalFrozenTables.LowerNodes upper (h + 1)) where
  clauses : Fin m → SourceClause.NormalizedClause v
  designated : Fin (branch h) → Slots branch h
  cut : OwnInputReference.Cut upper (HierarchicalLeftDecoder.LowerNode upper (h + 1) d)
  outside : Slots branch n → Fin t → MixedSupport.Slot
  placeholder : Slots branch (h + 1) → Fin t → MixedSupport.Slot
  exterior : CleanPhysicalReplay.Exterior rows repeats
    (CleanRecordDecoderInput.path upper d cut) outside placeholder

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (S : Setup branch rows repeats n h t v m upper d)

abbrev path := CleanRecordDecoderInput.path upper d S.cut
abbrev Calls := WholeCutCalls.Index rows repeats (path S)
abbrev Record := CleanRecordDecoderInput.Record (t := t) rows repeats upper d S.cut
  S.clauses S.designated
abbrev Sample := CleanRecordDecoderInput.Sample (t := t) rows repeats upper d S.cut
  S.clauses S.designated

def context (record : Record S) :=
  CleanRecordDecoderInput.exposed rows repeats upper d S.cut S.outside S.placeholder
    S.clauses S.designated record S.exterior

abbrev Seed (record : Record S) := CleanDecoderSeedLaw.Seed (context S record)

instance seedFintype (record : Record S) : Fintype (Seed S record) :=
  CleanDecoderSeedLaw.seedFintype (context S record)

abbrev observations (x : Sample S) : Record S :=
  CleanRecordDecoderInput.observe rows repeats upper d S.cut S.clauses S.designated x

abbrev sources (record : Record S) (x : Sample S) :=
  CleanRecordDecoderInput.sources rows repeats upper d S.cut S.clauses S.designated record x

def rawLaw (cube : Nat) (hcube : 0 < cube) : FiniteDistribution (Sample S) :=
  SourceChildKernel.originalLaw (C := Calls S) (t := t) rows S.clauses S.designated
    (fun _ => ProjectedCleanRate.projectionFlag cube hcube)

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (record : Record S) →
    CleanLeftDecoder.Useful (CleanDecoderContext.leftExposed (context S record)) upper (h + 1))
  (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
  (a : OwnInputReference.LowerVector rows (HierarchicalLeftDecoder.LowerNode upper (h + 1) d))
  (threshold : ℝ)

def kernel (record : Record S) : FiniteDistribution (Seed S record) :=
  CleanDecoderSeedLaw.seedLaw (context S record) σ (useful record) r ρ A W a threshold

def law (cube : Nat) (hcube : 0 < cube) :
    FiniteDistribution (Σ x : Sample S, Seed S (observations S x)) :=
  RecordSeedSampling.freshLaw (rawLaw S cube hcube) (observations S)
    (kernel S σ useful r ρ A W a threshold)

variable (hbranch : ∀ k < n, 0 < branch k)

def agrees (s : Nat) (x : Sample S) (seed : Seed S (observations S x)) : Bool :=
  decide
    (OddListExtraction.formRank
      (H (CleanDecoderOddLists.leftNative (context S (observations S x))
        (CleanDecoderOddLists.leftQuestions (context S (observations S x))
          (sources S (observations S x) x))))
      (CleanDecoderContext.leftForm (context S (observations S x)) hbranch seed.1
        (CleanDecoderOddLists.leftQuestions (context S (observations S x))
          (sources S (observations S x) x))) ≤ s ∧
    seed.2 (CleanDecoderOddLists.rightQuestions (context S (observations S x))
      (sources S (observations S x) x)) =
      CleanDecoderOddLists.target (context S (observations S x)) seed.1
        (sources S (observations S x) x))

end
end PerfectCompleteness.CleanDecoderRate

end

section

namespace PerfectCompleteness.CleanDecoderPairLaw

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (S : CleanDecoderRate.Setup branch rows repeats n h t v m upper d)

abbrev context (x : CleanDecoderRate.Sample S) :=
  CleanDecoderRate.context S (CleanDecoderRate.observations S x)

abbrev occurrences (x : CleanDecoderRate.Sample S) :=
  CleanDecoderRate.sources S (CleanDecoderRate.observations S x) x

abbrev leftOwn (x : CleanDecoderRate.Sample S) :=
  CleanDecoderOddLists.leftQuestions (context S x) (occurrences S x)

abbrev rightOwn (x : CleanDecoderRate.Sample S) :=
  CleanDecoderOddLists.rightQuestions (context S x) (occurrences S x)

abbrev LeftAnswer (x : CleanDecoderRate.Sample S) :=
  CleanDecoderSeedLaw.LeftAnswer (context S x) (leftOwn S x)

abbrev RightAnswer (x : CleanDecoderRate.Sample S) :=
  CleanDecoderSeedLaw.RightAnswer (context S x) (rightOwn S x)

instance leftAnswerFintype (x : CleanDecoderRate.Sample S) : Fintype (LeftAnswer S x) :=
  CleanLeftDecoder.upperAnswerFintype
    (CleanDecoderContext.leftExposed (context S x)) upper (leftOwn S x)

instance rightAnswerFintype (x : CleanDecoderRate.Sample S) : Fintype (RightAnswer S x) :=
  RightDecoder.scalarFintype (CleanDecoderContext.rightSlots (context S x) (rightOwn S x)) upper

abbrev Pair (x : CleanDecoderRate.Sample S) := LeftAnswer S x × RightAnswer S x

instance pairFintype (x : CleanDecoderRate.Sample S) : Fintype (Pair S x) :=
  inferInstanceAs (Fintype (LeftAnswer S x × RightAnswer S x))

def read (x : CleanDecoderRate.Sample S)
    (seed : CleanDecoderRate.Seed S (CleanDecoderRate.observations S x)) : Pair S x :=
  (seed.1 (leftOwn S x), seed.2 (rightOwn S x))

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (record : CleanDecoderRate.Record S) →
    CleanLeftDecoder.Useful (CleanDecoderContext.leftExposed (CleanDecoderRate.context S record))
      upper (h + 1))
  (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
  (a : OwnInputReference.LowerVector rows (HierarchicalLeftDecoder.LowerNode upper (h + 1) d))
  (threshold : ℝ)

def pairKernel (x : CleanDecoderRate.Sample S) : FiniteDistribution (Pair S x) :=
  (CleanDecoderSeedLaw.leftKernel (context S x) σ (useful (CleanDecoderRate.observations S x))
    r ρ A (leftOwn S x)).product
      (CleanDecoderSeedLaw.rightKernel (context S x) σ W a threshold (rightOwn S x))

def pairLaw (cube : Nat) (hcube : 0 < cube) :
    FiniteDistribution (Σ x : CleanDecoderRate.Sample S, Pair S x) :=
  CompletionSoundness.sigmaLaw (CleanDecoderRate.rawLaw S cube hcube)
    (pairKernel S σ useful r ρ A W a threshold)

variable (hbranch : ∀ k < n, 0 < branch k)

def pairAgrees (s : Nat) (x : CleanDecoderRate.Sample S) (answer : Pair S x) : Bool :=
  decide
    (OddListExtraction.formRank
      (H (CleanDecoderOddLists.leftNative (context S x) (leftOwn S x)))
      (CleanLeftDecoder.form (CleanDecoderContext.leftExposed (context S x)) upper (h + 1)
        hbranch d (leftOwn S x) answer.1) ≤ s ∧
    answer.2 = DecoderSourcePullback.upperTarget
      (CleanDecoderOddLists.fullProjection (context S x) (occurrences S x)) upper answer.1)

@[simp] theorem pairAgrees_read (s : Nat) (x : CleanDecoderRate.Sample S)
    (seed : CleanDecoderRate.Seed S (CleanDecoderRate.observations S x)) :
    pairAgrees S hbranch s x (read S x seed) = CleanDecoderRate.agrees S hbranch s x seed := rfl

end
end PerfectCompleteness.CleanDecoderPairLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_DecoderRankSplit
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.DecoderRankSplit

noncomputable section

open scoped BigOperators Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (S : CleanDecoderRate.Setup branch rows repeats n h t v m upper d)

def meeting (x : CleanDecoderRate.Sample S) (answer : CleanDecoderPairLaw.Pair S x) : Bool :=
  decide (answer.2 = DecoderSourcePullback.upperTarget
    (CleanDecoderOddLists.fullProjection (CleanDecoderPairLaw.context S x)
      (CleanDecoderPairLaw.occurrences S x)) upper answer.1)

variable (hbranch : ∀ k < n, 0 < branch k)

def nativeRank (x : CleanDecoderRate.Sample S)
    (answer : CleanDecoderPairLaw.Pair S x) : Nat :=
  OddListExtraction.formRank
    (H (CleanDecoderOddLists.leftNative (CleanDecoderPairLaw.context S x)
      (CleanDecoderPairLaw.leftOwn S x)))
    (CleanLeftDecoder.form
      (CleanDecoderContext.leftExposed (CleanDecoderPairLaw.context S x)) upper (h + 1)
      hbranch d (CleanDecoderPairLaw.leftOwn S x) answer.1)

def low (s : Nat) (x : CleanDecoderRate.Sample S)
    (answer : CleanDecoderPairLaw.Pair S x) : Bool :=
  decide (nativeRank S hbranch x answer ≤ s)

def highAgrees (s : Nat) (x : CleanDecoderRate.Sample S)
    (answer : CleanDecoderPairLaw.Pair S x) : Bool :=
  meeting S x answer && !(low S hbranch s x answer)

@[simp] theorem highAgrees_eq_true (s : Nat) (x : CleanDecoderRate.Sample S)
    (answer : CleanDecoderPairLaw.Pair S x) :
    highAgrees S hbranch s x answer = true ↔
      s < nativeRank S hbranch x answer ∧ meeting S x answer = true := by
  simp [highAgrees, low, and_comm]

end
end PerfectCompleteness.DecoderRankSplit

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_ChildCallNumbering
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairAgrees_read _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderRankSplit.highAgrees_eq_true _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.squareProduct_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.UniformChildSum.childSum_apply _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_nodePath _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_succ _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_height _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_refl _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_step _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ChildCallNumbering

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {C : Type*} [Fintype C] {branch : Nat → Nat} {n t : Nat}

abbrev Raw (rows : Nat → Nat) (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  (C → squareSpace (H slots)) × Arrays slots rows

instance rawFintype (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (Raw (C := C) rows slots) := Fintype.ofFinite _

instance rawNonempty (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Nonempty (Raw (C := C) rows slots) := ⟨(fun _ => 0, fun _ _ => 0)⟩

def equiv (rows : Nat → Nat) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Raw (C := C) rows slots ≃ₗ[F2]
      ChildBlockCardinality.Raw (Fintype.card C) rows slots where
  toFun x := (fun k => x.1 ((Fintype.equivFin C).symm k), x.2)
  invFun x := (fun c => x.1 (Fintype.equivFin C c), x.2)
  left_inv x := by
    apply Prod.ext
    · funext c
      simp only [Equiv.symm_apply_apply]
    · rfl
  right_inv x := by
    apply Prod.ext
    · funext k
      simp only [Equiv.apply_symm_apply]
    · rfl
  map_add' x y := rfl
  map_smul' c x := rfl

@[simp] theorem equiv_calls (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (x : Raw (C := C) rows slots) (k : Fin (Fintype.card C)) :
    (equiv rows slots x).1 k = x.1 ((Fintype.equivFin C).symm k) := rfl

@[simp] theorem equiv_arrays (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (x : Raw (C := C) rows slots) : (equiv rows slots x).2 = x.2 := rfl

@[simp] theorem equiv_symm_calls (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (x : ChildBlockCardinality.Raw (Fintype.card C) rows slots) (c : C) :
    ((equiv (C := C) rows slots).symm x).1 c = x.1 (Fintype.equivFin C c) := rfl

@[simp] theorem equiv_symm_arrays (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (x : ChildBlockCardinality.Raw (Fintype.card C) rows slots) :
    ((equiv (C := C) rows slots).symm x).2 = x.2 := rfl

def pullback (rows : Nat → Nat)
    {slots projected : Slots branch n → Fin t → MixedSupport.Slot}
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) :
    Raw (C := C) rows projected →ₗ[F2] Raw (C := C) rows slots where
  toFun x := (fun c => ChildBlockProjection.squarePullback p (x.1 c),
    ChildBlockProjection.arraysPullback rows p x.2)
  map_add' x y := by
    apply Prod.ext
    · funext c
      exact map_add (ChildBlockProjection.squarePullback p) (x.1 c) (y.1 c)
    · exact map_add (ChildBlockProjection.arraysPullback rows p) x.2 y.2
  map_smul' a x := by
    apply Prod.ext
    · funext c
      exact map_smul (ChildBlockProjection.squarePullback p) a (x.1 c)
    · exact map_smul (ChildBlockProjection.arraysPullback rows p) a x.2

omit [Fintype C] in
@[simp] theorem pullback_calls (rows : Nat → Nat)
    {slots projected : Slots branch n → Fin t → MixedSupport.Slot}
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (x : Raw (C := C) rows projected) (c : C) :
    (pullback rows p x).1 c = ChildBlockProjection.squarePullback p (x.1 c) := rfl

omit [Fintype C] in
@[simp] theorem pullback_arrays (rows : Nat → Nat)
    {slots projected : Slots branch n → Fin t → MixedSupport.Slot}
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (x : Raw (C := C) rows projected) :
    (pullback rows p x).2 = ChildBlockProjection.arraysPullback rows p x.2 := rfl

end
end PerfectCompleteness.ChildCallNumbering

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceQuestionCutSplit
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionCutSplit

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {root h t m : Nat}

abbrev OutsideLeaf (p : Path branch root h) :=
  {leaf : Slots branch root // leaf ∉ Set.range p.slotEmbedding}

end
end PerfectCompleteness.SourceQuestionCutSplit

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_SamplerComposition
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.stepFactorFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SamplerComposition

open PointwiseSpaces RecursiveSpaces DescendantSpaces RecursiveSampler

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m k : Nat}

def ExpansionSpace (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m k : Nat} → (p : Path branch n m) → (q : Path branch m k) →
      (A : Slots branch n → Type u) → DrawIndex repeats p → Type (max u w)
  | _, _, _, .refl _, q, A, _ => RecursiveSampler.Tape 𝕜 repeats q A
  | n + 1, _, _, .step i p, q, A, j =>
      match j with
      | Sum.inl j => squareSpace (space 𝕜 branch n (childFamily A j.val))
      | Sum.inr j => ExpansionSpace 𝕜 repeats p q (childFamily A i) j.2

abbrev ExpandedTape (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) (q : Path branch m k) (A : Slots branch n → Type u) :=
  (j : DrawIndex repeats p) → ExpansionSpace 𝕜 repeats p q A j

end
end PerfectCompleteness.SamplerComposition

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OriginalTerminalSplitLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.stepFactorFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalCutCalls.card_refl _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_succ _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_height _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_refl _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_step _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_selected _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutCalls.card_refl _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalTerminalSplit

open RecursiveSpaces DescendantSpaces RecursiveSampler TerminalCalls SamplerComposition
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m k : Nat}

theorem expansionSpace_terminal (𝕜 : Type w) [Field 𝕜]
    (repeats : Nat → Nat) (p : Path branch n m) :
    ∀ (q : Path branch m k) (A : Slots branch n → Type u)
      (terminal : TerminalIndex repeats p),
      ExpansionSpace 𝕜 repeats p q A (drawIndex repeats p terminal) =
        RecursiveSampler.Tape 𝕜 repeats q (p.family A) := by
  induction p with
  | refl n => intro q A terminal; rfl
  | step i p ih =>
      intro q A terminal
      exact ih q (childFamily A i) terminal.2

theorem expansionSpace_exterior (𝕜 : Type w) [Field 𝕜]
    (repeats : Nat → Nat) (p : Path branch n m) :
    ∀ (q : Path branch m k) (A : Slots branch n → Type u)
      (j : DrawIndex repeats p), ¬ IsTerminal repeats p j →
      ExpansionSpace 𝕜 repeats p q A j = DrawSpace 𝕜 repeats p A j := by
  induction p with
  | refl n =>
      intro q A j hj
      exact False.elim (hj True.intro)
  | step i p ih =>
      intro q A j hj
      cases j with
      | inl j => rfl
      | inr j => exact ih q (childFamily A i) j.2 hj

variable (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) (q : Path branch m k) (A : Slots branch n → Type u)

abbrev ExteriorIndex := {j : DrawIndex repeats p // ¬ IsTerminal repeats p j}

abbrev ExteriorTape := (j : ExteriorIndex repeats p) → DrawSpace 𝕜 repeats p A j.val

abbrev TerminalTape :=
  TerminalIndex repeats p → RecursiveSampler.Tape 𝕜 repeats q (p.family A)

def terminalFactorEquiv (terminal : TerminalIndex repeats p) :
    ExpansionSpace 𝕜 repeats p q A (drawIndex repeats p terminal) ≃
      RecursiveSampler.Tape 𝕜 repeats q (p.family A) :=
  Equiv.cast (expansionSpace_terminal 𝕜 repeats p q A terminal)

def exteriorFactorEquiv (j : ExteriorIndex repeats p) :
    ExpansionSpace 𝕜 repeats p q A j.val ≃ DrawSpace 𝕜 repeats p A j.val :=
  Equiv.cast (expansionSpace_exterior 𝕜 repeats p q A j.val j.property)

def terminalTapeEquiv :
    ((j : {j : DrawIndex repeats p // IsTerminal repeats p j}) →
      ExpansionSpace 𝕜 repeats p q A j.val) ≃ TerminalTape 𝕜 repeats p q A :=
  ((Equiv.piCongrLeft
    (fun j : {j : DrawIndex repeats p // IsTerminal repeats p j} =>
      ExpansionSpace 𝕜 repeats p q A j.val)
    (terminalSubtypeEquiv repeats p)).symm).trans
      (Equiv.piCongrRight (terminalFactorEquiv 𝕜 repeats p q A))

def splitExpanded : ExpandedTape 𝕜 repeats p q A ≃
    TerminalTape 𝕜 repeats p q A × ExteriorTape 𝕜 repeats p A :=
  (Equiv.piEquivPiSubtypeProd (IsTerminal repeats p)
    (ExpansionSpace 𝕜 repeats p q A)).trans
      (Equiv.prodCongr (terminalTapeEquiv 𝕜 repeats p q A)
        (Equiv.piCongrRight (exteriorFactorEquiv 𝕜 repeats p q A)))

@[simp] theorem splitExpanded_terminal_apply
    (x : ExpandedTape 𝕜 repeats p q A) (terminal : TerminalIndex repeats p) :
    (splitExpanded 𝕜 repeats p q A x).1 terminal =
      terminalFactorEquiv 𝕜 repeats p q A terminal (x (drawIndex repeats p terminal)) := rfl

@[simp] theorem splitExpanded_exterior_apply
    (x : ExpandedTape 𝕜 repeats p q A) (j : ExteriorIndex repeats p) :
    (splitExpanded 𝕜 repeats p q A x).2 j =
      exteriorFactorEquiv 𝕜 repeats p q A j (x j.val) := rfl

end
end PerfectCompleteness.OriginalTerminalSplit

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanPhysicalCanonicalQuery
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanPhysicalCanonicalQuery

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

noncomputable section

variable {branch : Nat → Nat} {root h t v m : Nat} [NeZero m]
  (rows repeats : Nat → Nat) (p : Path branch root (h + 1))
  (outside : Slots branch root → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)

abbrev Sample := CleanPhysicalReplay.Sample (t := t) rows repeats p clauses designated

def leftSlots (x : Sample (t := t) rows repeats p clauses designated) :
    Slots branch root → Fin t → MixedSupport.Slot :=
  CutSlotAssembly.fill p outside (CleanPhysicalReplay.leftInside rows repeats p clauses designated x)

def rightSlots (x : Sample (t := t) rows repeats p clauses designated) :
    Slots branch root → Fin t → MixedSupport.Slot :=
  CutSlotAssembly.fill p outside (CleanPhysicalReplay.rightInside rows repeats p clauses designated x)

def projection (x : Sample (t := t) rows repeats p clauses designated) :
    ∀ s k, MixedSupport.Projection
      (leftSlots rows repeats p outside clauses designated x s k)
      (rightSlots rows repeats p outside clauses designated x s k) :=
  CutProjectionAssembly.fillProjection p outside _ _
    (SourceChildKernel.parentProjection rows clauses designated
      (fun i => ((x i).1, (x i).2.1)) (fun i => (x i).2.2))

def leftArrays (x : Sample (t := t) rows repeats p clauses designated)
    (external : CleanPhysicalReplay.Exterior rows repeats p outside placeholder) :
    Arrays (leftSlots rows repeats p outside clauses designated x) rows :=
  WholeCutSampler.evaluate rows repeats p _
    (CleanPhysicalReplay.leftTape rows repeats p outside placeholder clauses designated x external)

def rightArrays (x : Sample (t := t) rows repeats p clauses designated)
    (external : CleanPhysicalReplay.Exterior rows repeats p outside placeholder) :
    Arrays (rightSlots rows repeats p outside clauses designated x) rows :=
  WholeCutSampler.evaluate rows repeats p _
    (CleanPhysicalReplay.rightTape rows repeats p outside placeholder clauses designated x external)

end
end PerfectCompleteness.CleanPhysicalCanonicalQuery

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanNativeReplay
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanNativeReplay

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (S : CleanDecoderRate.Setup branch rows repeats n h t v m upper d)

abbrev context (x : CleanDecoderRate.Sample S) := CleanDecoderPairLaw.context S x
abbrev leftOwn (x : CleanDecoderRate.Sample S) := CleanDecoderPairLaw.leftOwn S x
abbrev rightOwn (x : CleanDecoderRate.Sample S) := CleanDecoderPairLaw.rightOwn S x

abbrev leftSlots (x : CleanDecoderRate.Sample S) :=
  CleanPhysicalCanonicalQuery.leftSlots rows repeats (CleanDecoderRate.path S)
    S.outside S.clauses S.designated x

abbrev rightSlots (x : CleanDecoderRate.Sample S) :=
  CleanPhysicalCanonicalQuery.rightSlots rows repeats (CleanDecoderRate.path S)
    S.outside S.clauses S.designated x

abbrev leftTape (x : CleanDecoderRate.Sample S) :=
  CleanPhysicalReplay.leftTape rows repeats (CleanDecoderRate.path S)
    S.outside S.placeholder S.clauses S.designated x S.exterior

abbrev rightTape (x : CleanDecoderRate.Sample S) :=
  CleanPhysicalReplay.rightTape rows repeats (CleanDecoderRate.path S)
    S.outside S.placeholder S.clauses S.designated x S.exterior

theorem leftSlots_eq (x : CleanDecoderRate.Sample S) :
    CleanDecoderContext.leftSlots (context S x) (leftOwn S x) = leftSlots S x :=
  CleanRecordDecoderInput.leftSlots_eq rows repeats upper d S.cut S.outside S.placeholder
    S.clauses S.designated (CleanDecoderRate.observations S x) S.exterior x
    (CleanRecordDecoderInput.event_observe rows repeats upper d S.cut S.clauses S.designated x)

theorem rightSlots_eq (x : CleanDecoderRate.Sample S) :
    CleanDecoderContext.rightSlots (context S x) (rightOwn S x) = rightSlots S x :=
  CleanRecordDecoderInput.rightSlots_eq rows repeats upper d S.cut S.outside S.placeholder
    S.clauses S.designated (CleanDecoderRate.observations S x) S.exterior x
    (CleanRecordDecoderInput.event_observe rows repeats upper d S.cut S.clauses S.designated x)

end
end PerfectCompleteness.CleanNativeReplay

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CleanPhysicalDecoderLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanPhysicalDecoderLaw

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] RightDecoder.scalarFintype

local instance nativeLeftFintype {branch : Nat → Nat} {n t : Nat}
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n) :
    Fintype (Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)

section NativeData

variable {branch rows repeats : Nat → Nat} {n t : Nat}

def inputOfArrays (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (upper lower : Nodes branch n) (W : Submodule F2 (Block rows upper))
    (a : Block rows lower)
    (known : HiddenBucketBias.VisibleDirection W → H (nodeSlots slots upper))
    (arrays : Arrays slots rows) : OwnInputReference.Input slots rows upper lower W a where
  knownBuckets := known
  otherArrays node := arrays node.val
  lowerQuotient x := DirectionQuotient.proj a (fun row => (arrays lower row).val x)

def uncastTape (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (upper lower : Nodes branch n) (cut : OwnInputReference.Cut upper lower)
    {k : Nat} (hk : Nodes.height lower = k)
    (tape : WholeArraySampler.Tape rows repeats
      ((Nodes.path upper).append (hk ▸ cut.path)) slots) :
    WholeArraySampler.Tape rows repeats ((Nodes.path upper).append cut.path) slots := by
  cases hk
  exact tape

def inputFromTape (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (upper lower : Nodes branch n) (cut : OwnInputReference.Cut upper lower)
    {k : Nat} (hk : Nodes.height lower = k)
    (W : Submodule F2 (Block rows upper)) (a : Block rows lower)
    (tape : WholeArraySampler.Tape rows repeats
      ((Nodes.path upper).append (hk ▸ cut.path)) slots) :
    OwnInputReference.Input slots rows upper lower W a :=
  inputOfArrays slots upper lower W a
    (fun v => RecursiveSampler.evaluate F2 repeats (hk ▸ cut.path)
      (LeafDomain (nodeSlots slots upper))
      ((WholeArrayPositiveSplit.split rows repeats (Nodes.path upper) (hk ▸ cut.path)
        (by simpa only [hk] using cut.proper) slots W tape).2.1 v))
    (WholeArraySampler.evaluate rows repeats ((Nodes.path upper).append (hk ▸ cut.path)) slots tape)

variable {Sample : OriginalDecoderMark.SlotFamily branch n t → Type*}
  [∀ slots, Fintype (Sample slots)]
  (F : OriginalDecoderMark.Family branch rows n t Sample)

def adviceLaw (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (upper : Nodes branch n) (level : Nat) (κ : ℝ)
    (arrays : Arrays slots rows)
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r) :
    FiniteDistribution (Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :=
  HierarchicalLeftDecoder.adviceLaw slots upper level
    (HierarchicalMatrixTable.backgroundOf slots upper arrays) σ
    (OriginalDecoderMark.mark F upper level κ slots
      (HierarchicalMatrixTable.backgroundOf slots upper arrays)) r ρ A
    (A.comp (MatrixRowQuotient.projectMatrix
      (HierarchicalFrozenTables.knownRows slots upper level
        (HierarchicalMatrixTable.backgroundOf slots upper arrays))
      (NodeEmbedding.matrix arrays upper)))

abbrev Answers (slots projected : Slots branch n → Fin t → MixedSupport.Slot)
    (upper : Nodes branch n) :=
  Module.Dual F2 (NodeEmbedding.RowSpace slots upper) ×
    Module.Dual F2 (OwnInputReference.UpperSpace projected upper)

instance answersFintype (slots projected : Slots branch n → Fin t → MixedSupport.Slot)
    (upper : Nodes branch n) : Fintype (Answers slots projected upper) := by
  letI := LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)
  letI := RightDecoder.scalarFintype projected upper
  exact inferInstanceAs (Fintype
    (Module.Dual F2 (NodeEmbedding.RowSpace slots upper) ×
      Module.Dual F2 (OwnInputReference.UpperSpace projected upper)))

def answerEquiv (slots projected target other : Slots branch n → Fin t → MixedSupport.Slot)
    (hs : slots = target) (hp : projected = other) (upper : Nodes branch n) :
    Answers slots projected upper ≃ Answers target other upper := by
  cases hs
  cases hp
  exact Equiv.refl _

end NativeData

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (S : CleanDecoderRate.Setup branch rows repeats n h t v m upper d)

abbrev lower (_S : CleanDecoderRate.Setup branch rows repeats n h t v m upper d) :=
  HierarchicalLeftDecoder.LowerNode upper (h + 1) d

abbrev leftArrays (x : CleanDecoderRate.Sample S) :=
  WholeCutSampler.evaluate rows repeats (CleanDecoderRate.path S)
    (CleanNativeReplay.leftSlots S x) (CleanNativeReplay.leftTape S x)

abbrev rightArrays (x : CleanDecoderRate.Sample S) :=
  WholeCutSampler.evaluate rows repeats (CleanDecoderRate.path S)
    (CleanNativeReplay.rightSlots S x) (CleanNativeReplay.rightTape S x)

abbrev rightWholeTape (x : CleanDecoderRate.Sample S) :=
  WholeCutSampler.collapse rows repeats (CleanDecoderRate.path S)
    (CleanNativeReplay.rightSlots S x) (CleanNativeReplay.rightTape S x)

def rightInput (W : Submodule F2 (Block rows upper)) (a : Block rows (lower S))
    (x : CleanDecoderRate.Sample S) :
    OwnInputReference.Input (CleanNativeReplay.rightSlots S x) rows upper (lower S) W a :=
  inputFromTape (CleanNativeReplay.rightSlots S x) upper (lower S) S.cut
    (CleanDecoderContext.lowerHeight upper d) W a (rightWholeTape S x)

variable {Sample : OriginalDecoderMark.SlotFamily branch n t → Type*}
  [∀ slots, Fintype (Sample slots)]
  (F : OriginalDecoderMark.Family branch rows n t Sample) (κ : ℝ)

def useful (record : CleanDecoderRate.Record S) :=
  OriginalDecoderMark.useful F upper (h + 1) κ
    (CleanDecoderContext.leftExposed (CleanDecoderRate.context S record))

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (W : Submodule F2 (Block rows upper)) (a : Block rows (lower S))
  (threshold : ℝ)

def leftLaw (x : CleanDecoderRate.Sample S) :=
  adviceLaw F (CleanNativeReplay.leftSlots S x) upper (h + 1) κ (leftArrays S x) σ r ρ A

def rightLaw (x : CleanDecoderRate.Sample S) :=
  RightDecoder.law (CleanNativeReplay.rightSlots S x) rows upper (lower S) W a
    repeats S.cut σ (rightInput S W a x) threshold

def pairKernel (x : CleanDecoderRate.Sample S) :=
  (leftLaw S F κ σ r ρ A x).product (rightLaw S σ W a threshold x)

variable (cube : Nat) (hcube : 0 < cube)

def physicalAnswerEquiv (x : CleanDecoderRate.Sample S) :
    CleanDecoderPairLaw.Pair S x ≃
      Answers (CleanNativeReplay.leftSlots S x) (CleanNativeReplay.rightSlots S x) upper :=
  answerEquiv _ _ _ _ (CleanNativeReplay.leftSlots_eq S x)
    (CleanNativeReplay.rightSlots_eq S x) upper

abbrev physicalProjection (x : CleanDecoderRate.Sample S) :=
  CleanPhysicalCanonicalQuery.projection rows repeats (CleanDecoderRate.path S)
    S.outside S.clauses S.designated x

end
end PerfectCompleteness.CleanPhysicalDecoderLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_HierarchicalDecoderTables
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalDecoderTables

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)
  (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)

local instance rowSpaceFintype_r70ae7a_2 (node : Nodes branch n) :
    Fintype (NodeEmbedding.RowSpace slots node) := Fintype.ofFinite _
local instance nodeSpaceFintype_r70ae7a_3 (node : Nodes branch n) :
    Fintype (NodeEmbedding.NodeH slots node) := Fintype.ofFinite _
local instance upperDualFintype_r70ae7a_1 :
    Fintype (Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)
abbrev Advice (r : Nat) :=
  ManyGoodRows.RowMap (Block rows upper) r ×
    (Module.Dual F2 (NodeEmbedding.RowSpace slots upper ⧸
      HierarchicalFrozenTables.knownRows slots upper lowerLevel background) →ₗ[F2]
      (Fin r → F2))

variable (hbranch : ∀ k < n, 0 < branch k)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : HierarchicalFrozenTables.QuotientMatrix slots upper lowerLevel background → Prop)

local instance adviceFintype_r70ae7a_1 (r : Nat) :
    Fintype (Advice slots upper lowerLevel background r) := by
  letI : Fintype (Module.Dual F2 (NodeEmbedding.RowSpace slots upper ⧸
      HierarchicalFrozenTables.knownRows slots upper lowerLevel background)) :=
    LeftDecoder.dualFintype
  infer_instance
abbrev LowerH (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :=
  NodeEmbedding.NodeH slots (HierarchicalLeftDecoder.LowerNode upper lowerLevel d)

end
end PerfectCompleteness.HierarchicalDecoderTables

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_HierarchicalAllDecoderTables
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalAllDecoderTables

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)

abbrev Background := HierarchicalMatrixTable.Background (rows := rows) slots upper

abbrev Input (r : Nat) :=
  (background : Background (rows := rows) slots upper) ×
    HierarchicalDecoderTables.Advice slots upper lowerLevel background r

end
end PerfectCompleteness.HierarchicalAllDecoderTables

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutScalar
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.stepFactorFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_refl _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_refl_right _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_step _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_castSucc _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_last _root_.OAI.PerfectCompleteness.HierarchicalArrays.joint_component _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.NodeEmbedding.embed_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.embeddedRows_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.equiv_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.matrix_evaluate _root_.OAI.PerfectCompleteness.NodeEmbedding.rowsEquiv_apply _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalCutCalls.card_refl _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_succ _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_height _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_refl _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_step _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_selected _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutCalls.card_refl _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutScalar

open RecursiveSpaces DescendantSpaces RecursiveSampler TerminalCalls

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m : Nat}

abbrev Values (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (A : Slots branch n → Type u) :=
  TerminalIndex repeats p → space 𝕜 branch (m + 1) (p.family A)

def reconstruct (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) → (A : Slots branch n → Type u) →
      Values 𝕜 repeats p A → CutTerminalSplit.ExteriorTape 𝕜 repeats p A →
        space 𝕜 branch n A
  | _, _, .refl _, _, values, _ => values ()
  | n + 1, _, .step i p, A, values, exterior =>
      RecursiveSampler.combine 𝕜 A i (repeats (n + 1))
        (fun j => exterior ⟨.inl j, not_isTerminal_ordinary repeats i p j⟩)
        (fun h => reconstruct 𝕜 repeats p (childFamily A i)
          (fun terminal => values ((h, false), terminal))
          (CutSamplerReplayGrouping.subExterior 𝕜 repeats i p A (h, false) exterior))
        (fun h => reconstruct 𝕜 repeats p (childFamily A i)
          (fun terminal => values ((h, true), terminal))
          (CutSamplerReplayGrouping.subExterior 𝕜 repeats i p A (h, true) exterior))

@[simp] theorem reconstruct_refl (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (A : Slots branch (m + 1) → Type u)
    (values : Values 𝕜 repeats (.refl (m + 1)) A)
    (exterior : CutTerminalSplit.ExteriorTape 𝕜 repeats (.refl (m + 1)) A) :
    reconstruct 𝕜 repeats (.refl (m + 1)) A values exterior = values () := rfl

end
end PerfectCompleteness.LowerCutScalar

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutRowsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairAgrees_read _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderRankSplit.highAgrees_eq_true _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutRows

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def selectRows (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    CutChildGrouping.Assembled (C := WholeCutCalls.Index rows repeats p)
        (cutSlots p slots) rows →ₗ[F2]
      (Fin (rows (m + 1)) → H (cutSlots p slots)) where
  toFun x row := x.1 (WholeCutCalls.directRow rows repeats p row)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem selectRows_apply (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (x : CutChildGrouping.Assembled (C := WholeCutCalls.Index rows repeats p)
      (cutSlots p slots) rows) (row : Fin (rows (m + 1))) :
    selectRows rows repeats p slots x row =
      x.1 (WholeCutCalls.directRow rows repeats p row) := rfl

end
end PerfectCompleteness.LowerCutRows

end

section

namespace PerfectCompleteness.LowerCutCallSplit

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch n (m + 1))

abbrev OtherCall :=
  {q : WholeCutCalls.Index rows repeats p //
    ∀ row : Fin (rows (m + 1)), q ≠ WholeCutCalls.directRow rows repeats p row}

variable (slots : Slots branch n → Fin t → MixedSupport.Slot)

abbrev ChildArrays :=
  (i : Fin (branch m)) → Arrays (childSlots (cutSlots p slots) i) rows

abbrev Complement :=
  (OtherCall rows repeats p → H (cutSlots p slots)) × ChildArrays rows p slots

abbrev NativeRows := Fin (rows (m + 1)) → H (cutSlots p slots)

abbrev Assembled :=
  CutChildGrouping.Assembled (C := WholeCutCalls.Index rows repeats p) (cutSlots p slots) rows

def complement (x : Assembled rows repeats p slots) : Complement rows repeats p slots :=
  (fun q => x.1 q.val, x.2)

def splitAssembled : Assembled rows repeats p slots →ₗ[F2]
    Complement rows repeats p slots × NativeRows rows p slots where
  toFun x := (complement rows repeats p slots x, LowerCutRows.selectRows rows repeats p slots x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem splitAssembled_complement (x : Assembled rows repeats p slots) :
    (splitAssembled rows repeats p slots x).1 = complement rows repeats p slots x := rfl

@[simp] theorem splitAssembled_rows (x : Assembled rows repeats p slots) :
    (splitAssembled rows repeats p slots x).2 = LowerCutRows.selectRows rows repeats p slots x := rfl

@[simp] theorem complement_call (x : Assembled rows repeats p slots)
    (q : OtherCall rows repeats p) :
    (complement rows repeats p slots x).1 q = x.1 q.val := rfl

@[simp] theorem complement_arrays (x : Assembled rows repeats p slots) :
    (complement rows repeats p slots x).2 = x.2 := rfl

def merge (bg : Complement rows repeats p slots) (fresh : NativeRows rows p slots) :
    Assembled rows repeats p slots :=
  (fun q => if h : ∃ row, q = WholeCutCalls.directRow rows repeats p row then
      fresh (Classical.choose h)
    else bg.1 ⟨q, fun row hq => h ⟨row, hq⟩⟩,
   bg.2)

@[simp] theorem merge_directRow (bg : Complement rows repeats p slots)
    (fresh : NativeRows rows p slots) (row : Fin (rows (m + 1))) :
    (merge rows repeats p slots bg fresh).1 (WholeCutCalls.directRow rows repeats p row) =
      fresh row := by
  have hex : ∃ j, WholeCutCalls.directRow rows repeats p row =
      WholeCutCalls.directRow rows repeats p j := ⟨row, rfl⟩
  change (if h : ∃ j, WholeCutCalls.directRow rows repeats p row =
      WholeCutCalls.directRow rows repeats p j then fresh (Classical.choose h) else _) = fresh row
  rw [dite_eq_left hex]
  apply congrArg fresh
  exact (WholeCutCalls.directRow_injective rows repeats p (Classical.choose_spec hex)).symm

@[simp] theorem merge_otherCall (bg : Complement rows repeats p slots)
    (fresh : NativeRows rows p slots) (q : OtherCall rows repeats p) :
    (merge rows repeats p slots bg fresh).1 q.val = bg.1 q := by
  have hnot : ¬ ∃ row, q.val = WholeCutCalls.directRow rows repeats p row := by
    rintro ⟨row, hrow⟩
    exact q.property row hrow
  simp only [merge, dite_eq_right hnot]

@[simp] theorem merge_arrays (bg : Complement rows repeats p slots)
    (fresh : NativeRows rows p slots) :
    (merge rows repeats p slots bg fresh).2 = bg.2 := rfl

@[simp] theorem split_merge (bg : Complement rows repeats p slots)
    (fresh : NativeRows rows p slots) :
    splitAssembled rows repeats p slots (merge rows repeats p slots bg fresh) = (bg, fresh) := by
  apply Prod.ext
  · apply Prod.ext
    · funext q
      exact merge_otherCall rows repeats p slots bg fresh q
    · rfl
  · funext row
    exact merge_directRow rows repeats p slots bg fresh row

@[simp] theorem merge_split (x : Assembled rows repeats p slots) :
    merge rows repeats p slots (splitAssembled rows repeats p slots x).1
        (splitAssembled rows repeats p slots x).2 = x := by
  apply Prod.ext
  · funext q
    by_cases h : ∃ row, q = WholeCutCalls.directRow rows repeats p row
    · rcases h with ⟨row, rfl⟩
      exact merge_directRow rows repeats p slots _ _ row
    · exact merge_otherCall rows repeats p slots _ _ ⟨q, fun row hq => h ⟨row, hq⟩⟩
  · rfl

def splitEquiv : Assembled rows repeats p slots ≃ₗ[F2]
    Complement rows repeats p slots × NativeRows rows p slots where
  toFun := splitAssembled rows repeats p slots
  invFun z := merge rows repeats p slots z.1 z.2
  left_inv := merge_split rows repeats p slots
  right_inv z := split_merge rows repeats p slots z.1 z.2
  map_add' := (splitAssembled rows repeats p slots).map_add
  map_smul' := (splitAssembled rows repeats p slots).map_smul

@[simp] theorem splitEquiv_apply (x : Assembled rows repeats p slots) :
    splitEquiv rows repeats p slots x = splitAssembled rows repeats p slots x := rfl

@[simp] theorem splitEquiv_symm_apply
    (z : Complement rows repeats p slots × NativeRows rows p slots) :
    (splitEquiv rows repeats p slots).symm z = merge rows repeats p slots z.1 z.2 := rfl

@[simp] theorem complement_merge (bg : Complement rows repeats p slots)
    (fresh : NativeRows rows p slots) :
    complement rows repeats p slots (merge rows repeats p slots bg fresh) = bg :=
  congrArg Prod.fst (split_merge rows repeats p slots bg fresh)

end
end PerfectCompleteness.LowerCutCallSplit

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_CutCallExtension
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairAgrees_read _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderRankSplit.highAgrees_eq_true _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_castSucc _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_last _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.NodeEmbedding.embed_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.embeddedRows_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.equiv_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.matrix_evaluate _root_.OAI.PerfectCompleteness.NodeEmbedding.rowsEquiv_apply _root_.OAI.PerfectCompleteness.OddListExtraction.form_atom_self _root_.OAI.PerfectCompleteness.OddListExtraction.multiplicationForm_apply _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.squareProduct_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_nodePath _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_succ _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_height _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_refl _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_step _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutCallExtension

open scoped Classical
open TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {n t : Nat} {C : Type*} [Fintype C]
  (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat)

abbrev Extended := CutChildGrouping.Raw (C := Option C) slots rows

def original (x : Extended (C := C) slots rows) :
    CutChildGrouping.Raw (C := C) slots rows :=
  fun i => (fun c => (x i).1 (some c), (x i).2)

def fresh (x : Extended (C := C) slots rows) : H slots :=
  UniformChildSum.recursiveSum (LeafDomain slots) (fun i => (x i).1 none)

def observe (x : Extended (C := C) slots rows) :
    CutChildGrouping.Assembled (C := C) slots rows × H slots :=
  (CutChildGrouping.assemble slots rows (original slots rows x), fresh slots rows x)

def splitAssembled : CutChildGrouping.Assembled (C := Option C) slots rows →ₗ[F2]
    CutChildGrouping.Assembled (C := C) slots rows × H slots where
  toFun x := ((fun c => x.1 (some c), x.2), x.1 none)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype C] in
@[simp] theorem split_assemble (x : Extended (C := C) slots rows) :
    splitAssembled slots rows (CutChildGrouping.assemble slots rows x) =
      observe slots rows x := rfl

end
end PerfectCompleteness.CutCallExtension

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_HierarchicalLowerMatrixInput
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairAgrees_read _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderRankSplit.highAgrees_eq_true _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.actualProjection_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_nodePath _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_succ _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_height _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_refl _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_step _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_selected _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalLowerMatrixInput

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)

abbrev Matrix (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :=
  Module.Dual F2 (HierarchicalDecoderTables.LowerH slots upper lowerLevel d) →ₗ[F2]
    Block rows (HierarchicalLeftDecoder.LowerNode upper lowerLevel d)

variable (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)

def updateBackground (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (X : Matrix (rows := rows) slots upper lowerLevel d) :
    HierarchicalMatrixTable.Background (rows := rows) slots upper :=
  Function.update background (HierarchicalFrozenTables.lowerIndex upper lowerLevel d)
    (EvaluationMatrix.rows (HierarchicalDecoderTables.LowerH slots upper lowerLevel d) X)

@[simp] theorem updateBackground_selected
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (X : Matrix (rows := rows) slots upper lowerLevel d) :
    updateBackground slots upper lowerLevel background d X
      (HierarchicalFrozenTables.lowerIndex upper lowerLevel d) =
      EvaluationMatrix.rows (HierarchicalDecoderTables.LowerH slots upper lowerLevel d) X := by
  simp only [updateBackground, Function.update_self]

@[simp] theorem testedMatrix_update
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (X : Matrix (rows := rows) slots upper lowerLevel d) :
    HierarchicalLeftDecoder.testedMatrix slots upper lowerLevel
      (updateBackground slots upper lowerLevel background d X) d = X := by
  unfold HierarchicalLeftDecoder.testedMatrix
  rw [updateBackground_selected, EvaluationMatrix.ofRows_rows]

def advice {r : Nat} (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (upperMatrix : HierarchicalMatrixTable.Matrix (rows := rows) slots upper)
    (A : ManyGoodRows.RowMap (Block rows upper) r)
    (X : Matrix (rows := rows) slots upper lowerLevel d) :
    HierarchicalDecoderTables.Advice slots upper lowerLevel
      (updateBackground slots upper lowerLevel background d X) r :=
  (A, A.comp (MatrixRowQuotient.projectMatrix
    (HierarchicalFrozenTables.knownRows slots upper lowerLevel
      (updateBackground slots upper lowerLevel background d X)) upperMatrix))

def input {r : Nat} (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (upperMatrix : HierarchicalMatrixTable.Matrix (rows := rows) slots upper)
    (A : ManyGoodRows.RowMap (Block rows upper) r)
    (X : Matrix (rows := rows) slots upper lowerLevel d) :
    HierarchicalAllDecoderTables.Input (rows := rows) slots upper lowerLevel r :=
  ⟨updateBackground slots upper lowerLevel background d X,
    advice slots upper lowerLevel background d upperMatrix A X⟩

@[simp] theorem input_background {r : Nat}
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (upperMatrix : HierarchicalMatrixTable.Matrix (rows := rows) slots upper)
    (A : ManyGoodRows.RowMap (Block rows upper) r)
    (X : Matrix (rows := rows) slots upper lowerLevel d) :
    (input slots upper lowerLevel background d upperMatrix A X).1 =
      updateBackground slots upper lowerLevel background d X := rfl

@[simp] theorem input_testedMatrix {r : Nat}
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (upperMatrix : HierarchicalMatrixTable.Matrix (rows := rows) slots upper)
    (A : ManyGoodRows.RowMap (Block rows upper) r)
    (X : Matrix (rows := rows) slots upper lowerLevel d) :
    HierarchicalLeftDecoder.testedMatrix slots upper lowerLevel
      (input slots upper lowerLevel background d upperMatrix A X).1 d = X :=
  testedMatrix_update slots upper lowerLevel background d X

end
end PerfectCompleteness.HierarchicalLowerMatrixInput

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_ChildCallNumberingLaws
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairAgrees_read _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderRankSplit.highAgrees_eq_true _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.squareProduct_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.UniformChildSum.childSum_apply _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_nodePath _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_succ _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_height _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_refl _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_step _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ChildCallNumberingLaws

noncomputable section

open scoped BigOperators Classical
open RecursiveSpaces TreeSourceSpaces
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n t : Nat} {C : Type*} [Fintype C]

def liftedLaw (rows : Nat → Nat)
    {slots projected : Slots branch n → Fin t → MixedSupport.Slot}
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) :
    FiniteDistribution (ChildCallNumbering.Raw (C := C) rows slots) :=
  (FiniteDistribution.uniform (ChildCallNumbering.Raw (C := C) rows projected)).pushforward
    (ChildCallNumbering.pullback rows p)

def mixtureLaw {Z : Type*} [Fintype Z] (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (projected : Z → Slots branch n → Fin t → MixedSupport.Slot)
    (p : ∀ z s k, MixedSupport.Projection (slots s k) (projected z s k))
    (choiceLaw : FiniteDistribution Z) :
    FiniteDistribution (ChildCallNumbering.Raw (C := C) rows slots) :=
  choiceLaw.mixture (fun z => liftedLaw rows (p z))

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Z : I → Type*} [∀ i, Fintype (Z i)]

def replacementLaws (rows : Nat → Nat)
    (slots : I → Slots branch n → Fin t → MixedSupport.Slot)
    (projected : (i : I) → Z i → Slots branch n → Fin t → MixedSupport.Slot)
    (p : ∀ i z s k, MixedSupport.Projection (slots i s k) (projected i z s k))
    (choiceLaw : (i : I) → FiniteDistribution (Z i)) :
    (i : I) → FiniteDistribution (ChildCallNumbering.Raw (C := C) rows (slots i)) :=
  fun i => mixtureLaw rows (slots i) (projected i) (p i) (choiceLaw i)

def number (rows : Nat → Nat)
    (slots : I → Slots branch n → Fin t → MixedSupport.Slot)
    (x : (i : I) → ChildCallNumbering.Raw (C := C) rows (slots i)) :
    (i : I) → ChildBlockCardinality.Raw (Fintype.card C) rows (slots i) :=
  fun i => ChildCallNumbering.equiv rows (slots i) (x i)

def unnumber (rows : Nat → Nat)
    (slots : I → Slots branch n → Fin t → MixedSupport.Slot)
    (x : (i : I) → ChildBlockCardinality.Raw (Fintype.card C) rows (slots i)) :
    (i : I) → ChildCallNumbering.Raw (C := C) rows (slots i) :=
  fun i => (ChildCallNumbering.equiv rows (slots i)).symm (x i)

omit [Fintype I] [DecidableEq I] in
@[simp] theorem unnumber_number (rows : Nat → Nat)
    (slots : I → Slots branch n → Fin t → MixedSupport.Slot)
    (x : (i : I) → ChildCallNumbering.Raw (C := C) rows (slots i)) :
    unnumber rows slots (number rows slots x) = x := by
  funext i
  exact (ChildCallNumbering.equiv rows (slots i)).symm_apply_apply (x i)

omit [Fintype I] [DecidableEq I] in
@[simp] theorem number_unnumber (rows : Nat → Nat)
    (slots : I → Slots branch n → Fin t → MixedSupport.Slot)
    (x : (i : I) → ChildBlockCardinality.Raw (Fintype.card C) rows (slots i)) :
    number rows slots (unnumber (C := C) rows slots x) = x := by
  funext i
  exact (ChildCallNumbering.equiv rows (slots i)).apply_symm_apply (x i)

end
end PerfectCompleteness.ChildCallNumberingLaws

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_FilledUniformSampler
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_refl _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_refl_right _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_step _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_castSucc _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_last _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.NodeEmbedding.embed_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.embeddedRows_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.equiv_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.matrix_evaluate _root_.OAI.PerfectCompleteness.NodeEmbedding.rowsEquiv_apply _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_succ _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_height _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_refl _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_step _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FilledUniformSampler

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (m + 1) → Fin t → MixedSupport.Slot)

theorem cutSlots_fill (inside : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    WholeCutGrouping.cutSlots p (CutSlotAssembly.fill p outside inside) = inside := by
  funext s
  exact CutSlotAssembly.fill_at_cut p outside inside s

def childrenEquiv (inside : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows ≃
      CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
        (WholeCutGrouping.cutSlots p (CutSlotAssembly.fill p outside inside)) rows :=
  Equiv.piCongrRight (fun i => Equiv.cast (congrArg
    (fun slots => CutChildGrouping.Child (C := WholeCutCalls.Index rows repeats p) slots rows i)
    (cutSlots_fill p outside inside).symm))

@[simp] theorem childrenEquiv_apply
    (inside : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows)
    (i : Fin (branch m)) :
    childrenEquiv rows repeats p outside inside children i =
      cast (congrArg
        (fun slots => CutChildGrouping.Child (C := WholeCutCalls.Index rows repeats p) slots rows i)
        (cutSlots_fill p outside inside).symm) (children i) := rfl

end
end PerfectCompleteness.FilledUniformSampler

end

end OAI
end


