-- Prove2me | Definitions.Def_OAIQ252P011
-- name    : OAIQ252P011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T07:42:52.735194+00:00
-- url     : https://prove2.me/theorems/65c6da8e-0412-46a3-a3b4-108cf86c521c
-- title:
--   Definitions bundle OAIQ252P011 of the split of OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 461 declarations of OpenAI's Lean: 257 definitions, 1 inductive type or structure, 17 instances and 186 theorems. The definitions and types are `OAI.PerfectCompleteness.FunctionSpaceLowerRank.matrixForm`, `OAI.PerfectCompleteness.GeometricCutSplit.castPath`, `OAI.PerfectCompleteness.GeometricCutSplit.prefixLaw`, `OAI.PerfectCompleteness.GeometricCutSplit.prefixPath`, `OAI.PerfectCompleteness.GeometricCutSplit.prefixPathDepth`, `OAI.PerfectCompleteness.GeometricPrefixSplit.joinEquiv`, `OAI.PerfectCompleteness.GeometricPrefixSplit.splitEquiv`, `OAI.PerfectCompleteness.GoodAdviceEvents.I`, `OAI.PerfectCompleteness.GoodAdviceEvents.J`, `OAI.PerfectCompleteness.GoodAdviceEvents.law`, `OAI.PerfectCompleteness.GoodAdviceEvents.selectedAgreement`, `OAI.PerfectCompleteness.GoodAdviceEvents.selectedColumn`, `OAI.PerfectCompleteness.GoodAdviceFamily.Sample`, `OAI.PerfectCompleteness.GoodAdviceFamily.law`, `OAI.PerfectCompleteness.HeterogeneousAdviceFamily.I`, `OAI.PerfectCompleteness.HeterogeneousAdviceFamily.J`, `OAI.PerfectCompleteness.HeterogeneousAdviceFamily.Sample`, `OAI.PerfectCompleteness.HeterogeneousAdviceFamily.law`, `OAI.PerfectCompleteness.HeterogeneousPairAdvice.AdviceSample`, `OAI.PerfectCompleteness.HeterogeneousPairAdvice.PairSample`, `OAI.PerfectCompleteness.HeterogeneousPairAdvice.appendLaw`, `OAI.PerfectCompleteness.HeterogeneousPairAdvice.backgroundFintype`, `OAI.PerfectCompleteness.HeterogeneousPairAdvice.referencePairLaw`, `OAI.PerfectCompleteness.HierarchicalAdviceExperiment.Advice`, `OAI.PerfectCompleteness.HierarchicalAdviceExperiment.Background`, `OAI.PerfectCompleteness.HierarchicalAdviceExperiment.Experiment`, `OAI.PerfectCompleteness.HierarchicalAdviceExperiment.Value`, `OAI.PerfectCompleteness.HierarchicalAdviceExperiment.adviceLaw`, `OAI.PerfectCompleteness.HierarchicalAdviceExperiment.backgroundFintype`, `OAI.PerfectCompleteness.HierarchicalAdviceExperiment.matrix`, `OAI.PerfectCompleteness.HierarchicalAdviceExperiment.originalLaw`, `OAI.PerfectCompleteness.HierarchicalAdviceExperiment.valueFintype`, `OAI.PerfectCompleteness.HierarchicalAdviceFamily.Background`, `OAI.PerfectCompleteness.HierarchicalAdviceFamily.OriginalSample`, `OAI.PerfectCompleteness.HierarchicalAdviceFamily.Row`, `OAI.PerfectCompleteness.HierarchicalAdviceFamily.Value`, `OAI.PerfectCompleteness.HierarchicalAdviceFamily.backgroundFiberFintype`, `OAI.PerfectCompleteness.HierarchicalAdviceFamily.backgroundLaw`, `OAI.PerfectCompleteness.HierarchicalAdviceFamily.originalLaw`, `OAI.PerfectCompleteness.HierarchicalAdviceFamily.valueFintype` and 218 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `PerfectCompleteness_Algebra_FunctionSpaceLowerRank`, `PerfectCompleteness_Algebra_HierarchicalMatrixTable`, `PerfectCompleteness_Algebra_LowerAffineSliceRank`, `PerfectCompleteness_Algebra_MatrixTriangularFoldingLemmas`, `PerfectCompleteness_Algebra_TensorBucketEvaluationLemmas`, `PerfectCompleteness_Algebra_TensorRowAdviceLemmas`, `PerfectCompleteness_Construction_HierarchicalAdviceFromBuckets`, `PerfectCompleteness_Construction_HierarchicalBucketFamily`, `PerfectCompleteness_Construction_OriginalChildScalars`, `PerfectCompleteness_Construction_RelativeDescendantProductsLemmas`, `PerfectCompleteness_Construction_TreeCanonical`, `PerfectCompleteness_Construction_TreeSourceSpaces`, `PerfectCompleteness_Decoding_CollisionAveragingLemmas`, `PerfectCompleteness_Decoding_HierarchicalAllDecoderTables`, `PerfectCompleteness_Decoding_HierarchicalLeftDecoder`, `PerfectCompleteness_Decoding_HierarchicalUsefulCollision`, `PerfectCompleteness_Decoding_RepresentativeBucketCollisionLemmas`, `PerfectCompleteness_Decoding_RightDecoderWitness`, `PerfectCompleteness_Decoding_UpperCutTriangle`, `PerfectCompleteness_Foundations_GeometricPrefixSplit`, `PerfectCompleteness_Foundations_GlobalityLemmas`, `PerfectCompleteness_Foundations_GoodAdviceEventsLemmas`, `PerfectCompleteness_Foundations_HeterogeneousAdviceFamily`, `PerfectCompleteness_Foundations_HeterogeneousPairAdvice`, `PerfectCompleteness_Foundations_HierarchicalAdviceExperimentLemmas`, `PerfectCompleteness_Foundations_HierarchicalAgreementMean`, `PerfectCompleteness_Foundations_HierarchicalFrozenTablesLemmas`, `PerfectCompleteness_Foundations_HierarchicalPairCoarse`, `PerfectCompleteness_Foundations_HierarchicalPrediction`, `PerfectCompleteness_Foundations_HierarchicalProjectedSliceLemmas`, `PerfectCompleteness_Foundations_HierarchicalUsefulBackground`, `PerfectCompleteness_Foundations_ManyGoodRowsLemmas`, `PerfectCompleteness_Foundations_MultiplicationFormInjectiveLemmas`, `PerfectCompleteness_Foundations_OccurrenceStochasticLemmas`, `PerfectCompleteness_Foundations_OddListExtraction`, `PerfectCompleteness_Foundations_OddLists`, `PerfectCompleteness_Foundations_OriginalPrefixContinuation`, `PerfectCompleteness_Foundations_ProjectedCutChoices`, `PerfectCompleteness_Foundations_QuotientTableAgreementLemmas`, `PerfectCompleteness_Foundations_RecursiveSpaces`, `PerfectCompleteness_Foundations_SourceClause`, `PerfectCompleteness_Foundations_SourceOddListsLemmas`, `PerfectCompleteness_Foundations_SourceProjectedTag`, `PerfectCompleteness_Foundations_TerminalCalls`, `PerfectCompleteness_Foundations_TupleIndexEmitterLemmas`, `PerfectCompleteness_Machines_InitializationMachine`, `PerfectCompleteness_Machines_OrClosure`, `PerfectCompleteness_Machines_OwnInputAffineSliceLemmas`, `PerfectCompleteness_Machines_OwnInputHeavyBounds`, `PerfectCompleteness_Machines_OwnInputReferenceLemmas`, `PerfectCompleteness_Machines_SourceClauseCountMachine`, `PerfectCompleteness_Machines_SourceOccurrenceLoopMachine`, `PerfectCompleteness_Machines_TargetFinalizeMachine`, `PerfectCompleteness_Machines_TermMachine`, `PerfectCompleteness_Reduction_OccurrenceGame`, `PerfectCompleteness_Reduction_OddListGame`, `PerfectCompleteness_Reduction_SourceGame`, `PerfectCompleteness_Reduction_TargetFinalizeBound`, `PerfectCompleteness_Repetition_RepetitionRateLemmas`, `PerfectCompleteness_Repetition_SourceAmplification`, `PerfectCompleteness_Sampling_BucketUniformLemmas`, `PerfectCompleteness_Sampling_GoodRowSampling`, `PerfectCompleteness_Sampling_HierarchicalBackgroundVariation`, `PerfectCompleteness_Sampling_OwnLawHeavyList`, `PerfectCompleteness_Sampling_RestrictionCrossLaw`, `PerfectCompleteness_Sampling_RestrictionRowsLaw`, `PerfectCompleteness_Sampling_StoppedSharedSampler`, `PerfectCompleteness_Sampling_WholeArrayExteriorLaw`, `PerfectCompleteness_Sampling_WholeArraySampler`, `UniqueGames_Analysis_A13IndexLemmas`, `UniqueGames_Analysis_A5FrequencyTransportLemmas`, `UniqueGames_Analysis_HybridCompositionLemmas`, `UniqueGames_Analysis_RestrictionLemmas`, `UniqueGames_Foundations_Conditioning`, `UniqueGames_Foundations_KernelSampling`, `UniqueGames_Foundations_ValueLemmas`, `UniqueGames_Games_CompletedSamplingLemmas`, `UniqueGames_Games_FactorizationLemmas`, `UniqueGames_Games_MaskedVariation`, `UniqueGames_Games_PartialRevealLemmas`, `UniqueGames_Games_SelectedCommonMarginalLemmas`, `UniqueGames_Games_SelectedInformationLemmas`, `UniqueGames_Machines_MachineExpanderTableProgramLemmas`, `UniqueGames_Machines_MachineInitialHeaders`, `UniqueGames_Machines_PoweringGlobalEnumerationLemmas`, `UniqueGames_Machines_PoweringMachineRelationLemmas`, `UniqueGames_PCP_AlphabetGraphLemmas`, `UniqueGames_PCP_AlphabetReductionLemmas`, `UniqueGames_PCP_AlphabetTableBoundsLemmas`, `UniqueGames_PCP_AssignmentTester`, `UniqueGames_PCP_ClauseVerifierLemmas`, `UniqueGames_PCP_CodeComposition`, `UniqueGames_PCP_FinalBooleanVerifier`, `UniqueGames_PCP_FinalConstantsLemmas`, `UniqueGames_PCP_InitialGraphLemmas`, `UniqueGames_PCP_NameCompaction`, `UniqueGames_PCP_OverlayLemmas`, `UniqueGames_PCP_PoweringPortReindexLemmas`, `UniqueGames_PCP_PoweringTableSemanticsLemmas`, `UniqueGames_PCP_PreprocessingOverlayTables`, `UniqueGames_PCP_PreprocessingPaddingTables`, `UniqueGames_PCP_PreprocessingRegularSoundness`, `UniqueGames_PCP_PreprocessingRegularTablesLemmas`, `UniqueGames_PCP_PreprocessingTablesLemmas`, `UniqueGames_PCP_RawInitialTablesLemmas`, `UniqueGames_PCP_SourceGapLemmas`, `UniqueGames_PCP_SourceNoiseParameterLemmas`, `UniqueGames_PCP_Table`.
--
--   **Imports.** It imports the published bundle `Def_PerfectCompleteness`; the bundles `OAIQ252P003`, `OAIQ252P004`, `OAIQ252P005` and `OAIQ252P006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ252P014` and `OAIQ252P015`; the statements `OAI.PerfectCompleteness.BilinearCollisionTransfer.full_collision_transfer`, `OAI.PerfectCompleteness.ChildBilinearCollisionTransfer.marked_restricted_le_uniform_full`, `OAI.PerfectCompleteness.ChildFiniteCallCollisionTransfer.marked_restricted_le_uniform_full`, `OAI.PerfectCompleteness.HeterogeneousAdviceFamily.J_probability_ge`, `OAI.PerfectCompleteness.LowerAffineSliceRank.slice_probability_le_of_coordinates`, `OAI.PerfectCompleteness.MatrixInverse.noiseEnergy_le_of_global`, `OAI.PerfectCompleteness.OddListGame.repetition_halfRate`, `OAI.PerfectCompleteness.UniformCleanSoundness.source_soundness`, `OAI.UniqueGamesTheorem.Appendix.A13Reduction.degree_reduction_truncated`, `OAI.UniqueGamesTheorem.Appendix.A13Reduction.weakFourthSum_le_positiveTripleSum`, `OAI.UniqueGamesTheorem.Appendix.A13Reduction.weighted_geometric_moment_le`, `OAI.UniqueGamesTheorem.Appendix.A5Induction.boundedTripleSum_le_descendants`, `OAI.UniqueGamesTheorem.Appendix.A5Induction.derivative_inequality`, `OAI.UniqueGamesTheorem.Appendix.A5Induction.postA5Sum_hybrid_average`, `OAI.UniqueGamesTheorem.Appendix.A5Induction.recurrence_closure`, `OAI.UniqueGamesTheorem.Appendix.RankLevelFilter.hybridDerivative_rankLevel_energy_le_strong`, `OAI.UniqueGamesTheorem.Appendix.SelectorEnergy.hybridMomentSum_rankLevel_le`, `OAI.UniqueGamesTheorem.Foundations.Repetition.selectedLeftProfileError_sum`, `OAI.UniqueGamesTheorem.Foundations.Repetition.selectedRightProfileError_sum`, `OAI.UniqueGamesTheorem.Foundations.Repetition.selected_coordinate_probability_le_value_add_error` and `OAI.UniqueGamesTheorem.Foundations.Repetition.selected_rightReveal_error_sum`; the proofs of `OAI.PerfectCompleteness.BilinearCollisionTransfer.full_collision_transfer`, `OAI.PerfectCompleteness.BucketQuotientAgreement.agreement_eq_nonzeroAgreement`, `OAI.PerfectCompleteness.ChildBilinearCollisionTransfer.marked_restricted_le_uniform_full`, `OAI.PerfectCompleteness.ChildFiniteCallCollisionTransfer.marked_restricted_le_uniform_full`, `OAI.PerfectCompleteness.HeterogeneousAdviceFamily.J_probability_ge`, `OAI.PerfectCompleteness.LowerAffineSliceRank.slice_probability_le_of_coordinates`, `OAI.PerfectCompleteness.MatrixInverse.noiseEnergy_le_of_global`, `OAI.PerfectCompleteness.UniformCleanSoundness.source_soundness`, `OAI.UniqueGamesTheorem.Appendix.A13Reduction.degree_reduction_truncated`, `OAI.UniqueGamesTheorem.Appendix.A13Reduction.weakFourthSum_le_positiveTripleSum`, `OAI.UniqueGamesTheorem.Appendix.A13Reduction.weighted_geometric_moment_le`, `OAI.UniqueGamesTheorem.Appendix.A5Induction.boundedTripleSum_le_descendants`, `OAI.UniqueGamesTheorem.Appendix.A5Induction.derivative_inequality`, `OAI.UniqueGamesTheorem.Appendix.A5Induction.postA5Sum_hybrid_average`, `OAI.UniqueGamesTheorem.Appendix.A5Induction.recurrence_closure`, `OAI.UniqueGamesTheorem.Appendix.RankLevelFilter.hybridDerivative_rankLevel_energy_le_strong`, `OAI.UniqueGamesTheorem.Appendix.SelectorEnergy.hybridMomentSum_rankLevel_le`, `OAI.UniqueGamesTheorem.Foundations.Repetition.selectedLeftProfileError_sum`, `OAI.UniqueGamesTheorem.Foundations.Repetition.selectedRightProfileError_sum`, `OAI.UniqueGamesTheorem.Foundations.Repetition.selected_coordinate_probability_le_value_add_error` and `OAI.UniqueGamesTheorem.Foundations.Repetition.selected_rightReveal_error_sum`.
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
import Mathlib.Algebra.Group.Equiv.Basic
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
import Definitions.Def_PerfectCompleteness
import Definitions.Def_OAIQ252P003
import Definitions.Def_OAIQ252P004
import Definitions.Def_OAIQ252P005
import Definitions.Def_OAIQ252P006

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_A13IndexLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The real-valued finite-probability steps at the end of Appendix A.5.

The results here prove normalized Cauchy--Schwarz/Hölder consequences and
Boolean moment identities. They do not introduce Proposition A.5 or Lemma A.6
as axioms, and do not identify a conditional estimate with Theorem 2.3.
-/

noncomputable section

namespace UniqueGamesTheorem.Appendix.LevelInequality

open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier

section ActualLinearMaps

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

variable [Finite E] [Finite F]

def IsRestrictionGlobal (f : (E →ₗ[F2] F) → ℝ) (d : ℕ) (η : ℝ) : Prop :=
  ∀ (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F),
    UniqueGamesTheorem.Fourier.MatrixRestrictions.order A B ≤ d →
      (𝔼 N, UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict f A B T N ^ 2) ≤ η

def Theorem23 : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (ρ : ℝ), 0 < ρ → ρ < 1 →
    ∀ (f : (E →ₗ[F2] F) → ℝ), IsBoolean f →
      (∀ (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F),
        UniqueGamesTheorem.Fourier.MatrixRestrictions.order A B ≤ d →
          (𝔼 N, UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict f A B T N) ≤ ρ) →
      (𝔼 X, rankLevel d f X ^ 2) ≤
        (2 : ℝ) ^ (30 * d * d) * ρ ^ ((1 : ℝ) / 4) * (𝔼 X, f X ^ 2)

end ActualLinearMaps

end UniqueGamesTheorem.Appendix.LevelInequality

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_RestrictionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace UniqueGamesTheorem.Appendix.Derivatives
open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

variable [Finite E] [Finite F]

def hybridMomentSum (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ s : HybridIndex (E := E) (F := F) d,
    𝔼 T, (𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2) ^ 2

end UniqueGamesTheorem.Appendix.Derivatives

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_HybridCompositionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.ReducedPartition.instFinitePart _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier
open UniqueGamesTheorem.Appendix.Derivatives
open UniqueGamesTheorem.Appendix.OperatorPartitions
open UniqueGamesTheorem.Appendix.LinearIdentities

namespace UniqueGamesTheorem.Appendix.A13Reduction

attribute [local instance] Classical.propDecidable

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F]

attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype

/-- The actual averaged fourth moment attached to a raw derivative triple. -/
def tripleMoment (p : A4Index (K := F2) (W := F) (V := E))
    (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  𝔼 T, 𝔼 N, mapDerivative p.2.2 (hybridDerivative p.1 p.2.1 T f) N ^ 4

/-- The weight after relabeling the actual raw derivative triple. -/
def tripleTerm (d : ℕ) (p : A13Index.Triple (E := E) (F := F))
    (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  (2 : ℝ) ^ (24 * d * A13Index.size p) * tripleMoment p f

variable [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)]

/-- The displayed A.13 sum: its original positive total order is retained. -/
def positiveTripleSum (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ p : A13Index.PositiveTriple (E := E) (F := F), tripleTerm d p.val f

/-- The same sum after the genuine degree-support cutoff. -/
def boundedPositiveTripleSum (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ p : A13Index.BoundedPositiveTriple (E := E) (F := F) d, tripleTerm d p.val f

end UniqueGamesTheorem.Appendix.A13Reduction

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_A5FrequencyTransportLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.ReducedPartition.instFinitePart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniqueGamesTheorem

/-! Pointwise identification of the natural frequency transport with the
relative frequency used by the actual reverse compression fibers. -/

/-! Canonical indices for the Appendix A.5 induction passage. The outer
hybrid index is recovered from its actual geometric pair, so forgetting it
does not increase multiplicity. -/

namespace Appendix.A5Passage

open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.Derivatives
attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

variable [Finite E] [Finite F]

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

def descendantSum (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) (e : Nat) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ q : Passage X e,
    𝔼 U, (𝔼 N, mapDerivative
      (NaturalTransport.dualFactor A B q.2.val.1 q.2.val.2
        (LinearIdentities.compress X q.2.val.1 q.2.val.2))
      (hybridDerivative (q.2.val.1.comap A.mkQ) (q.2.val.2.map B.subtype) U f) N ^ 2) ^ 2

end Appendix.A5Passage

/-!
# The actual weighted reversal in Appendix A.5

The forward index records an original positive triple and an actual A.5
passage. Its checked reverse-fiber bound permits finite weighted grouping.
The resulting weights are the moments of the actual transported derivatives.
No degree hypothesis or analytic induction hypothesis is used here.
-/

namespace Appendix.A5ReverseSum

open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Fourier.MatrixRestrictions (order)
open Derivatives
open A5ForwardIndex

attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype
attribute [local instance] SubspaceExtensions.subspaceFintype

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

def actualMoment (f : (E →ₗ[F2] F) → ℝ)
    (r : A13Index.Triple (E := E) (F := F)) : ℝ :=
  𝔼 T, (𝔼 N, mapDerivative r.2.2 (hybridDerivative r.1 r.2.1 T f) N ^ 2) ^ 2

def targetWeight (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (r : A13Index.Triple (E := E) (F := F)) : ℝ :=
  if order r.1 r.2.1 ≤ d then actualMoment f r else 0

end Appendix.A5ReverseSum

/-! Actual norm and induction steps for Proposition A.5. The universal degree
property below is the motive for strong induction on the degree; defining
that property does not assert its truth. -/

namespace Appendix.A5Induction

open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix.Derivatives UniqueGamesTheorem.Appendix.DerivativeDegree
open UniqueGamesTheorem.Appendix.LevelInequality (frequencyRank)
attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype
attribute [local instance] SubspaceExtensions.subspaceFintype

universe u v

/-- The strong-induction motive quantifies over the actual changing domains.
Quotients and subspaces preserve the fixed universe levels. -/
def BoundAtDegree (d : ℕ) : Prop :=
  ∀ {E : Type u} {F : Type v}
    [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
    [FiniteDimensional F2 E] [FiniteDimensional F2 F]
    [Finite E] [Finite F]
    [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
    (f : (E →ₗ[F2] F) → ℝ),
    DegreeAtMost d f →
      (𝔼 M, f M ^ 4) ≤ (2 : ℝ) ^ (100 * d * d) * hybridMomentSum d f

variable {E : Type u} {F : Type v}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Finite E] [Finite F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- The actual weighted map-derivative sum left by the finite reindexing. -/
def dampedMapMoment (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ X : F →ₗ[F2] E,
    (1 / 2 : ℝ) ^ (31 * d * (frequencyRank X + 1) + 4 * d * frequencyRank X) *
      (𝔼 N, mapDerivative X f N ^ 2) ^ 2

def dampedHybridMoment (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ s : HybridIndex (E := E) (F := F) d,
    𝔼 T, dampedMapMoment d (hybridDerivative s.val.1 s.val.2 T f)

/-- Actual A.5 descendants before recombining the first hybrid restriction. -/
def postA5Sum (X : F →ₗ[F2] E) (e : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ q : A5Passage.Passage X e, 𝔼 S : Parameter X.range X.ker,
    (𝔼 N, mapDerivative (LinearIdentities.compress X q.2.val.1 q.2.val.2)
      (hybridDerivative q.2.val.1 q.2.val.2 (embed X.range X.ker S) f) N ^ 2)^2

end Appendix.A5Induction

end UniqueGamesTheorem

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_GlobalityLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped BigOperators

namespace UniqueGamesTheorem.Appendix.Globality

section BinaryLinear

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Fourier.MatrixRestrictions

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F] [Finite E] [Finite F]

def RestrictionGlobal (d : Nat) (η : ℝ) (f : (E →ₗ[F2] F) → ℝ) : Prop :=
  ∀ (A : Submodule F2 E) (B : Submodule F2 F), order A B ≤ d →
    ∀ T : E →ₗ[F2] F, restrictionEnergy f (embed A B) T ≤ η

end BinaryLinear

end UniqueGamesTheorem.Appendix.Globality

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_RecursiveSpaces
attribute [-instance] _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.RecursiveSpaces

open PointwiseSpaces

universe u v w

variable {branch : Nat → Nat} {n : Nat}

variable {𝕜 : Type w} [Field 𝕜]

theorem one_mem_space_square (A : Slots branch n → Type u)
    (hbranch : ∀ k < n, 0 < branch k) :
    (1 : Assignment A → 𝕜) ∈ squareSpace (space 𝕜 branch n A) :=
  one_mem_squareSpace _ (one_mem_space branch n A hbranch)

end PerfectCompleteness.RecursiveSpaces

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_Conditioning
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Conditioning of actual finite distributions and the selected-coordinate chain
rule used in parallel repetition. A normalized conditional distribution is only
constructed when the conditioning event has strictly positive probability.
-/

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators

noncomputable section

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  {n : Nat}

theorem selectedSuccess_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) : 0 ≤ G.selectedSuccess strategy selected :=
  (G.repetition n).questions.probability_nonnegative _

end Game

end

end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_ValueLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators

noncomputable section

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]

/-- A maximum of the finitely many actual deterministic success probabilities. -/
def value (G : Game Q₁ Q₂ A₁ A₂) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty G.success

end Game

end

end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceClause
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceClause

open UniqueGamesTheorem.Foundations.Target

def agreementCount {n : Nat} (c : NormalizedClause n) (label : Triple)
    (assignment : Fin n → Bool) : Nat :=
  (if label.1 = assignment (c.variable 0) then 1 else 0) +
  (if label.2.1 = assignment (c.variable 1) then 1 else 0) +
  (if label.2.2 = assignment (c.variable 2) then 1 else 0)

end PerfectCompleteness.SourceClause

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_FactorizationLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Local embedding to single-game strategy transfer for Holenstein's argument.
The embedding law below is explicitly sampled from a finite shared seed and
the base game's actual joint question law. Its distance from the desired
conditioned law is an explicit total-variation expression. Constructing an
embedding with a sufficiently small distance is a separate proof obligation.
-/

namespace UniqueGamesTheorem.Foundations.Games.Game

noncomputable section

variable {Q₁ Q₂ A₁ A₂ R₁ R₂ B₁ B₂ Seed : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂] [Fintype Seed]
  [Nonempty A₁] [Nonempty A₂]

def localEmbeddingLaw (G : Game Q₁ Q₂ A₁ A₂)
    (seedLaw : FiniteDistribution Seed)
    (left : Seed → Q₁ → R₁) (right : Seed → Q₂ → R₂) :
    FiniteDistribution (R₁ × R₂) :=
  seedLaw.mixture fun seed =>
    G.questions.pushforward fun q => (left seed q.1, right seed q.2)

/-- A single tested coordinate under an arbitrary full-tuple question law. -/
def coordinateGame (G : Game Q₁ Q₂ A₁ A₂) {n : Nat} (coordinate : Fin n)
    (law : FiniteDistribution ((Fin n → Q₁) × (Fin n → Q₂))) :
    Game (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂) where
  questions := law
  accepts x y a b := G.accepts (x coordinate) (y coordinate) (a coordinate) (b coordinate)

end
end UniqueGamesTheorem.Foundations.Games.Game

end

section

/-! The actual single-coordinate dependency-breaking reveal distribution.
The tag records which endpoint of the question pair was revealed. -/

namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem revealLaw_weight (μ : FiniteDistribution (X × Y)) (q : X × Y) (r : X ⊕ Y) :
    (revealLaw μ).weight (q,r) =
      (if r = Sum.inl q.1 then μ.weight q / 2 else 0) +
      (if r = Sum.inr q.2 then μ.weight q / 2 else 0) := by
  classical
  rcases q with ⟨x,y⟩
  simp only [revealLaw, FiniteDistribution.pushforward, FiniteDistribution.product,
    Fintype.sum_prod_type, Prod.mk.injEq, ite_and]
  simp [revealEndpoint, FiniteDistribution.uniform, div_eq_mul_inv, add_comm, eq_comm]

/-- The default row still preserves the displayed endpoint if that endpoint
has zero probability in the base question law. -/
def revealFallback (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) :
    FiniteDistribution (X × Y) :=
  match r with
  | Sum.inl x => μ.pushforward (fun q => (x,q.2))
  | Sum.inr y => μ.pushforward (fun q => (q.1,y))

def revealProfile (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) :
    FiniteDistribution (X × Y) :=
  gameConditionalKernel (revealFirstLaw μ) (revealFallback μ r) r

def revealInputLaw (μ : FiniteDistribution (X × Y)) : FiniteDistribution (X ⊕ Y) :=
  (revealLaw μ).pushforward Prod.snd

theorem revealInputLaw_weight (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) :
    (revealInputLaw μ).weight r = firstMarginal (revealFirstLaw μ).weight r := by
  classical
  cases r <;>
    simp [revealInputLaw, FiniteDistribution.pushforward, firstMarginal, Fintype.sum_prod_type]

/-- The conditional product representation is proved from the sampled law,
including reveal values with zero probability. -/
theorem reveal_profile_recombination (μ : FiniteDistribution (X × Y))
    (r : X ⊕ Y) (q : X × Y) :
    (revealInputLaw μ).weight r * (revealProfile μ r).weight q =
      (revealLaw μ).weight (q,r) := by
  rw [revealInputLaw_weight]
  exact gameConditionalKernel_recombine (revealFirstLaw μ) (revealFallback μ r) r q

theorem revealLaw_sum_left (μ : FiniteDistribution (X × Y)) (q : X × Y) :
    (∑ x, (revealLaw μ).weight (q, Sum.inl x)) = μ.weight q / 2 := by
  classical
  simp [revealLaw_weight]

theorem revealLaw_sum_right (μ : FiniteDistribution (X × Y)) (q : X × Y) :
    (∑ y, (revealLaw μ).weight (q, Sum.inr y)) = μ.weight q / 2 := by
  classical
  simp [revealLaw_weight]

/-- A conditional product of independently revealed coordinates has its
exact point weight. This is the product identity used by the information
bound, derived from the single-coordinate sampled distribution. -/
theorem reveal_product_factorization {ι : Type*} [Fintype ι]
    (μ : FiniteDistribution (X × Y)) (r : ι → X ⊕ Y) (q : ι → X × Y) :
    (∏ i, (revealInputLaw μ).weight (r i)) *
      (∏ i, (revealProfile μ (r i)).weight (q i)) =
        ∏ i, (revealLaw μ).weight (q i,r i) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact reveal_profile_recombination μ (r i) (q i)

theorem reveal_product_forget {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : FiniteDistribution (X × Y)) (q : ι → X × Y) :
    (∑ r : ι → X ⊕ Y,
      (∏ i, (revealInputLaw μ).weight (r i)) *
        (∏ i, (revealProfile μ (r i)).weight (q i))) =
      ∏ i, μ.weight (q i) := by
  classical
  simp_rw [reveal_product_factorization]
  calc
    _ = ∏ i, ∑ r : X ⊕ Y, (revealLaw μ).weight (q i,r) :=
      (Fintype.prod_sum (fun (i : ι) (r : X ⊕ Y) => (revealLaw μ).weight (q i,r))).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Fintype.sum_sum_type, revealLaw_sum_left, revealLaw_sum_right]
      ring

/-- Marginalizing the reveal variables restores the original independent
question law for every observable, including the selected-win likelihood. -/
theorem reveal_product_expectation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : FiniteDistribution (X × Y)) (f : (ι → X × Y) → ℝ) :
    (∑ r : ι → X ⊕ Y,
      (∏ i, (revealInputLaw μ).weight (r i)) *
        ∑ q : ι → X × Y, (∏ i, (revealProfile μ (r i)).weight (q i)) * f q) =
      ∑ q : ι → X × Y, (∏ i, μ.weight (q i)) * f q := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  rw [reveal_product_forget]

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_KernelSampling
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Exact sampling of two conditional kernels from one finite weighted shared seed.
The seed consists of independent full response tables and is independent of the
questions. Supported-coordinate repairs preserve the sampled laws and enforce
the designated coordinate even on seeds of weight zero. The seed is not claimed
to be uniform: the kernel weights may be arbitrary real numbers.
-/

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators
noncomputable section

namespace KernelSampling

/-- The fixed weighted seed law; it does not depend on the sampled questions. -/
def seedLaw {Q₁ Q₂ A B : Type*}
    [Fintype Q₁] [Fintype Q₂] [Fintype A] [Fintype B]
    [DecidableEq Q₁] [DecidableEq Q₂]
    (left : Q₁ → FiniteDistribution A) (right : Q₂ → FiniteDistribution B) :
    FiniteDistribution (Seed Q₁ Q₂ A B) :=
  (FiniteDistribution.table left).product (FiniteDistribution.table right)

end KernelSampling
end
end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_MaskedVariation
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact variation decomposition for the two choices of revealed endpoint.
The support of the actual reveal profiles makes both branch identities valid,
including zero-probability revealed endpoints. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]

def maskedModel (μ : Games.FiniteDistribution (X × Y)) (p : S × (X × Y) → ℝ) :
    (S × (X ⊕ Y)) × (X × Y) → ℝ := fun z =>
  Information.firstMarginal (maskedJoint p) z.1 * (revealProfile μ z.1.2).weight z.2

def leftRevealModel (μ : Games.FiniteDistribution (X × Y)) (p : S × (X × Y) → ℝ) :
    S × (X × Y) → ℝ := fun z =>
  (∑ y, p (z.1, (z.2.1, y))) * (revealProfile μ (Sum.inl z.2.1)).weight z.2

def rightRevealModel (μ : Games.FiniteDistribution (X × Y)) (p : S × (X × Y) → ℝ) :
    S × (X × Y) → ℝ := fun z =>
  (∑ x, p (z.1, (x, z.2.2))) * (revealProfile μ (Sum.inr z.2.2)).weight z.2

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_SelectedInformationLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OccurrenceGame.toGame_success _root_.OAI.PerfectCompleteness.OccurrenceVertexEmbedding.restrict_extend _root_.OAI.PerfectCompleteness.OccurrenceVertexEmbedding.success_restrict _root_.OAI.PerfectCompleteness.OccurrenceVertexEmbedding.wins_restrict _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.PerfectCompleteness.SourceGame.questionGame_success _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Concrete selected-coordinate questions and answer labels for the
side-information inequality. The event is the actual repeated game's selected
success event. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

theorem iid_coordinate_split {Ω : Type*} [Fintype Ω] {n : Nat}
    (μ : FiniteDistribution Ω) (selected : Finset (Fin n)) :
    (μ.iid n).transport (coordinateSplitEquiv selected) =
      (FiniteDistribution.table (fun _ : selected => μ)).product
        (FiniteDistribution.table (fun _ : {i : Fin n // i ∉ selected} => μ)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change (∏ i, μ.weight (mergeCoordinates selected x.1 x.2 i)) =
    (∏ i : selected, μ.weight (x.1 i)) *
      ∏ i : {i : Fin n // i ∉ selected}, μ.weight (x.2 i)
  have h := Fintype.prod_subtype_mul_prod_subtype (fun i : Fin n => i ∈ selected)
    (fun i => μ.weight (mergeCoordinates selected x.1 x.2 i))
  have hi : Subtype.fintype (fun i : Fin n => i ∈ selected) =
      Finset.Subtype.fintype selected := Subsingleton.elim _ _
  rw [hi] at h
  calc
    _ = (∏ i : {i : Fin n // i ∈ selected},
        μ.weight (mergeCoordinates selected x.1 x.2 i.1)) *
        ∏ i : {i : Fin n // i ∉ selected},
          μ.weight (mergeCoordinates selected x.1 x.2 i.1) := h.symm
    _ = _ := by
      congr 1 <;> apply Finset.prod_congr rfl <;> intro i _ <;>
        simp [mergeCoordinates, i.property]

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]
  {n : Nat}

def selectedAnswerLabel
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (questions : (Fin n → Q₁) × (Fin n → Q₂)) :
    SelectedLabels (A₁ := A₁) (A₂ := A₂) selected :=
  (fun i => strategy.1 questions.1 i.1, fun i => strategy.2 questions.2 i.1)

def selectedLikelihood (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (fixed : selected → Q₁ × Q₂)
    (label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) : ℝ := by
  classical
  let questions := selectedQuestionTuple selected fixed remaining
  exact if selectedAnswerLabel strategy selected questions = label then
    (if G.selectedWins strategy selected questions then 1 else 0) else 0

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedLikelihood_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (fixed : selected → Q₁ × Q₂)
    (label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    0 ≤ selectedLikelihood G strategy selected fixed label remaining := by
  classical
  dsimp only [selectedLikelihood]
  split_ifs <;> norm_num

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedLikelihood_sum (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (fixed : selected → Q₁ × Q₂)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    (∑ label, selectedLikelihood G strategy selected fixed label remaining) =
      if G.selectedWins strategy selected (selectedQuestionTuple selected fixed remaining)
      then 1 else 0 := by
  classical
  simp [selectedLikelihood]

def selectedSplitLaw (G : Game Q₁ Q₂ A₁ A₂) (selected : Finset (Fin n)) :
    FiniteDistribution ((selected → Q₁ × Q₂) ×
      ({i : Fin n // i ∉ selected} → Q₁ × Q₂)) :=
  (FiniteDistribution.table (fun _ : selected => G.questions)).product
    (FiniteDistribution.table (fun _ : {i : Fin n // i ∉ selected} => G.questions))

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedSplit_probability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) :
    (selectedSplitLaw G selected).probability
      (fun q => G.selectedWins strategy selected (selectedQuestionTuple selected q.1 q.2)) =
        G.selectedSuccess strategy selected := by
  rw [selectedSplitLaw, ← iid_coordinate_split, FiniteDistribution.probability_transport]
  change (G.questions.iid n).probability _ =
    ((G.questions.iid n).transport (Game.tupleQuestionEquiv n)).probability _
  rw [FiniteDistribution.probability_transport]
  apply congrArg (G.questions.iid n).probability
  funext q
  congr 1
  apply Prod.ext <;> funext i <;>
    simp [selectedQuestionTuple, coordinateSplitEquiv, mergeCoordinates, Game.tupleQuestionEquiv]

def selectedInputLaw (G : Game Q₁ Q₂ A₁ A₂) (selected : Finset (Fin n)) :
    FiniteDistribution (SelectedInput Q₁ Q₂ selected) :=
  (FiniteDistribution.table (fun _ : selected => G.questions)).product
    (FiniteDistribution.table (fun _ : {i : Fin n // i ∉ selected} => revealInputLaw G.questions))

def selectedInputProfile (G : Game Q₁ Q₂ A₁ A₂) (selected : Finset (Fin n))
    (t : SelectedInput Q₁ Q₂ selected) (i : {i : Fin n // i ∉ selected}) :
    FiniteDistribution (Q₁ × Q₂) := revealProfile G.questions (t.2 i)

def selectedSideMass (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (tv : SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ :=
  ∑ u, independentProduct (fun i => (selectedInputProfile G selected tv.1 i).weight) u *
    selectedLikelihood G strategy selected tv.1.1 tv.2 u

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedSideMass_sum (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (t : SelectedInput Q₁ Q₂ selected) :
    (∑ v, selectedSideMass G strategy selected (t,v)) =
      ∑ u, independentProduct (fun i => (selectedInputProfile G selected t i).weight) u *
        (if G.selectedWins strategy selected (selectedQuestionTuple selected t.1 u)
        then 1 else 0) := by
  classical
  simp only [selectedSideMass]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, selectedLikelihood_sum]

/-- The side-information normalizer is the actual selected-win probability
of the repeated strategy. No event-mass hypothesis is required. -/
theorem selectedSideMass_total (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) :
    (∑ tv, (selectedInputLaw G selected).weight tv.1 *
      selectedSideMass G strategy selected tv) = G.selectedSuccess strategy selected := by
  classical
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, selectedSideMass_sum]
  rw [Fintype.sum_prod_type]
  simp only [selectedInputLaw, FiniteDistribution.product, FiniteDistribution.table,
    selectedInputProfile, independentProduct]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  have hforget (fixed : selected → Q₁ × Q₂) :=
    reveal_product_expectation G.questions
      (fun u : {i : Fin n // i ∉ selected} → Q₁ × Q₂ =>
        if G.selectedWins strategy selected (selectedQuestionTuple selected fixed u)
        then (1 : ℝ) else 0)
  simp_rw [hforget]
  have h := selectedSplit_probability G strategy selected
  simpa [selectedSplitLaw, FiniteDistribution.probability, FiniteDistribution.product,
    FiniteDistribution.table, Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_assoc] using h

def selectedSideWeight (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (tv : SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ :=
  (selectedInputLaw G selected).weight tv.1 * selectedSideMass G strategy selected tv /
    G.selectedSuccess strategy selected

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! Conditioning bounds for the actual repeated-game question marginals.
The likelihood and its normalizer are derived from the selected-win event.
The final estimate retains only the unselected coordinates. -/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators
open Games Information

noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]
  {n : Nat}

def selectedTupleLikelihood (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (questions : Fin n → Q₁ × Q₂) : ℝ :=
  if G.selectedWins strategy selected (Game.tupleQuestionEquiv n questions) then 1 else 0

/-- The coordinate pair under the actual repeated question law conditioned on
the selected wins, rather than a separately postulated posterior law. -/
def selectedQuestionMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (i : Fin n) : FiniteDistribution (Q₁ × Q₂) :=
  ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).pushforward
    (fun questions => (questions.1 i, questions.2 i))

end

end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! The actual full selected-answer and reveal law conditioned on success.
Its factorization is derived from the explicit independent question law. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedJointWeight (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (z : (SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
      ({i : Fin n // i ∉ selected} → Q₁ × Q₂)) : ℝ :=
  (selectedInputLaw G selected).weight z.1.1 *
    independentProduct (fun i => (selectedInputProfile G selected z.1.1 i).weight) z.2 *
      selectedLikelihood G strategy selected z.1.1.1 z.1.2 z.2 /
        G.selectedSuccess strategy selected

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedJointWeight_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (z) : 0 ≤ selectedJointWeight G strategy selected z := by
  apply div_nonneg
  · exact mul_nonneg
      (mul_nonneg ((selectedInputLaw G selected).nonnegative _)
        ((independentProduct_isProbability _
          (fun i => gameLaw_isProbability (selectedInputProfile G selected z.1.1 i))).1 z.2))
      (selectedLikelihood_nonnegative G strategy selected z.1.1.1 z.1.2 z.2)
  · exact G.selectedSuccess_nonnegative strategy selected

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedJointWeight_firstMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (tv) :
    firstMarginal (selectedJointWeight G strategy selected) tv =
      selectedSideWeight G strategy selected tv := by
  simp only [firstMarginal, selectedJointWeight, selectedSideWeight, selectedSideMass,
    div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem selectedJointWeight_isProbability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    IsProbability (selectedJointWeight G strategy selected) := by
  constructor
  · exact selectedJointWeight_nonnegative G strategy selected
  · rw [Fintype.sum_prod_type]
    change (∑ tv, firstMarginal (selectedJointWeight G strategy selected) tv) = 1
    simp_rw [selectedJointWeight_firstMarginal, selectedSideWeight, div_eq_mul_inv]
    rw [← Finset.sum_mul, selectedSideMass_total, mul_inv_cancel₀ positive.ne']

def selectedJointLaw (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :=
  toGameLaw (selectedJointWeight G strategy selected)
    (selectedJointWeight_isProbability G strategy selected positive)

/-- Pointwise product formula for the actual conditional joint law. The
selected-answer test depends on the question tuples, and not on any reveal. -/
theorem selectedJointWeight_factorization (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (tv) (u) :
    selectedJointWeight G strategy selected (tv,u) =
      (∏ i : selected, G.questions.weight (tv.1.1 i)) *
        (∏ i : {i : Fin n // i ∉ selected}, (revealLaw G.questions).weight (u i,tv.1.2 i)) *
          selectedLikelihood G strategy selected tv.1.1 tv.2 u /
            G.selectedSuccess strategy selected := by
  unfold selectedJointWeight
  simp only [selectedInputLaw, FiniteDistribution.product, FiniteDistribution.table,
    independentProduct, selectedInputProfile]
  rw [mul_assoc (∏ i : selected, G.questions.weight (tv.1.1 i)), reveal_product_factorization]

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! The selected-success likelihood factors into a fixed verifier check and
two separate tests on the local deterministic answers. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open Games
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedLabelAccepts (G : Game Q₁ Q₂ A₁ A₂) (selected : Finset (Fin n))
    (fixed : selected → Q₁ × Q₂)
    (label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : Bool := by
  classical
  exact decide (∀ i : selected, G.accepts (fixed i).1 (fixed i).2 (label.1 i) (label.2 i) = true)

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_PartialRevealLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OccurrenceGame.toGame_success _root_.OAI.PerfectCompleteness.OccurrenceVertexEmbedding.restrict_extend _root_.OAI.PerfectCompleteness.OccurrenceVertexEmbedding.success_restrict _root_.OAI.PerfectCompleteness.OccurrenceVertexEmbedding.wins_restrict _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.PerfectCompleteness.SourceGame.questionGame_success _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Removing one independent reveal from the explicit product law. The
likelihood can be any function of the questions and outside data. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
noncomputable section
variable {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def partialRevealWeight (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (u : I → X × Y) : ℝ :=
  μ.weight (u j) * ∏ i : {i : I // i ≠ j}, (revealLaw μ).weight (u i.1,rest i)

theorem product_reveal_at (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (r : X ⊕ Y) (rest : {i : I // i ≠ j} → X ⊕ Y) (u : I → X × Y) :
    (∏ i, (revealLaw μ).weight (u i,mergeAt j r rest i)) =
      (if r = Sum.inl (u j).1 then partialRevealWeight μ j rest u / 2 else 0) +
      (if r = Sum.inr (u j).2 then partialRevealWeight μ j rest u / 2 else 0) := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ j]
  simp only [mergeAt_self, mergeAt_other, revealLaw_weight]
  by_cases hl : r = Sum.inl (u j).1 <;> by_cases hr : r = Sum.inr (u j).2 <;>
    simp [hl, hr, partialRevealWeight, revealLaw_weight] <;> ring

def partialRevealMarginal (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    (T × ({i : I // i ≠ j} → X ⊕ Y)) × (X × Y) → ℝ := by
  classical
  exact fun z => ∑ u, if u j = z.2 then
    partialRevealWeight μ j z.1.2 u * likelihood z.1.1 u else 0

def fullRevealMarginal (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    (T × (I → X ⊕ Y)) × (X × Y) → ℝ := by
  classical
  exact fun z => ∑ u, if u j = z.2 then
    (∏ i, (revealLaw μ).weight (u i,z.1.2 i)) * likelihood z.1.1 u else 0

omit [Fintype T] in
theorem fullRevealMarginal_merge (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) (t : T)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (r : X ⊕ Y) (q : X × Y) :
    fullRevealMarginal μ j likelihood ((t,mergeAt j r rest),q) =
      maskedJoint (partialRevealMarginal μ j likelihood) (((t,rest),r),q) := by
  classical
  unfold fullRevealMarginal
  simp_rw [product_reveal_at]
  have hpoint (u : I → X × Y) :
      (if u j = q then
        ((if r = Sum.inl (u j).1 then partialRevealWeight μ j rest u / 2 else 0) +
         (if r = Sum.inr (u j).2 then partialRevealWeight μ j rest u / 2 else 0)) *
          likelihood t u else 0) =
      (if r = Sum.inl q.1 then
        (if u j = q then partialRevealWeight μ j rest u * likelihood t u else 0) / 2 else 0) +
      (if r = Sum.inr q.2 then
        (if u j = q then partialRevealWeight μ j rest u * likelihood t u else 0) / 2 else 0) := by
    by_cases hu : u j = q
    · rw [hu]
      by_cases hl : r = Sum.inl q.1 <;> by_cases hr : r = Sum.inr q.2 <;>
        simp [hl, hr] <;> ring
    · simp [hu]
  simp_rw [hpoint]
  simp [maskedJoint, partialRevealMarginal, Finset.sum_add_distrib,
    Finset.sum_ite_irrel, div_eq_mul_inv, Finset.sum_mul]

def fullRevealModel (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    (T × (I → X ⊕ Y)) × (X × Y) → ℝ := fun z =>
  Information.firstMarginal (fullRevealMarginal μ j likelihood) z.1 *
    (revealProfile μ (z.1.2 j)).weight z.2

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! The actual sum-tagged reveal law separates into local endpoint factors.
The fair reveal probability is retained in those factors. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games
noncomputable section
variable {I X Y : Type*} [Fintype I] [DecidableEq I]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def revealLeftFactor (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) (x : X) : ℝ :=
  match r with
  | Sum.inl u => if x = u then 1 else 0
  | Sum.inr v => μ.weight (x,v) / 2

def revealRightFactor (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) (y : Y) : ℝ :=
  match r with
  | Sum.inl u => μ.weight (u,y) / 2
  | Sum.inr v => if y = v then 1 else 0

omit [DecidableEq Y] in
theorem revealLeftFactor_nonnegative (μ : FiniteDistribution (X × Y))
    (r : X ⊕ Y) (x : X) : 0 ≤ revealLeftFactor μ r x := by
  cases r with
  | inl u => simp only [revealLeftFactor]; split <;> norm_num
  | inr v => exact div_nonneg (μ.nonnegative _) (by norm_num)

omit [DecidableEq X] in
theorem revealRightFactor_nonnegative (μ : FiniteDistribution (X × Y))
    (r : X ⊕ Y) (y : Y) : 0 ≤ revealRightFactor μ r y := by
  cases r with
  | inl u => exact div_nonneg (μ.nonnegative _) (by norm_num)
  | inr v => simp only [revealRightFactor]; split <;> norm_num

def partialLeftFactor (μ : FiniteDistribution (X × Y)) (j : I)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (x : I → X) : ℝ :=
  ∏ i, revealLeftFactor μ (rest i) (x i.1)

def partialRightFactor (μ : FiniteDistribution (X × Y)) (j : I)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (y : I → Y) : ℝ :=
  ∏ i, revealRightFactor μ (rest i) (y i.1)

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! The side-information estimate for the explicit coordinate marginals of
the selected-answer/reveal law, followed by removal of one reveal variable. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedRawMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) :
    (SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
      (Q₁ × Q₂) → ℝ := by
  classical
  exact fun z => ∑ u, if u j = z.2 then selectedJointWeight G strategy selected (z.1,u) else 0

theorem selectedRawMarginal_firstMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) (tv) :
    firstMarginal (selectedRawMarginal G strategy selected j) tv =
      selectedSideWeight G strategy selected tv := by
  classical
  simp only [firstMarginal, selectedRawMarginal]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  exact selectedJointWeight_firstMarginal G strategy selected tv

theorem selectedRawMarginal_isProbability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    IsProbability (selectedRawMarginal G strategy selected j) := by
  classical
  constructor
  · intro z
    apply Finset.sum_nonneg
    intro u _
    split
    · exact selectedJointWeight_nonnegative G strategy selected (z.1,u)
    · exact le_rfl
  · rw [Fintype.sum_prod_type]
    change (∑ tv, firstMarginal (selectedRawMarginal G strategy selected j) tv) = 1
    simp_rw [selectedRawMarginal_firstMarginal, selectedSideWeight, div_eq_mul_inv]
    rw [← Finset.sum_mul, selectedSideMass_total, mul_inv_cancel₀ positive.ne']

def selectedOutsideLikelihood (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (t : (selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected)
    (u : {i : Fin n // i ∉ selected} → Q₁ × Q₂) : ℝ :=
  (∏ i : selected, G.questions.weight (t.1 i)) *
    selectedLikelihood G strategy selected t.1 t.2 u / G.selectedSuccess strategy selected

theorem selectedRawMarginal_fullReveal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) (z) :
    selectedRawMarginal G strategy selected j
        ((selectedObservationEquiv (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected).symm z) =
      fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected) z := by
  classical
  change selectedRawMarginal G strategy selected j
    (((z.1.1.1,z.1.2),z.1.1.2),z.2) = _
  simp only [selectedRawMarginal, fullRevealMarginal]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : u j = z.2
  · simp only [ite_eq_left hu, selectedJointWeight_factorization, selectedOutsideLikelihood]
    ring
  · simp [hu]

def selectedInformationRadius (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) : ℝ :=
  Real.sqrt ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
    (Real.log (Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ) +
      Real.log (1 / G.selectedSuccess strategy selected)))

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! The common data used by the two local simulators is the actual
selected-answer law with only the embedded coordinate's reveal removed. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

theorem partialRevealMarginal_isProbability
    {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (μ : FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ)
    (hp : IsProbability (fullRevealMarginal μ j likelihood)) :
    IsProbability (partialRevealMarginal μ j likelihood) := by
  apply (maskedJoint_isProbability_iff _).mp
  have h := isProbability_comp_equiv (revealSplitEquiv (T := T) j).symm _ hp
  have he : (fun z => fullRevealMarginal μ j likelihood
      ((revealSplitEquiv (T := T) j).symm z)) =
      maskedJoint (partialRevealMarginal μ j likelihood) := by
    funext z
    exact fullRevealMarginal_merge μ j likelihood z.1.1.1 z.1.1.2 z.1.2 z.2
  rw [he] at h
  exact h

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

theorem selected_fullReveal_isProbability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    IsProbability (fullRevealMarginal G.questions j
      (selectedOutsideLikelihood G strategy selected)) := by
  have h := isProbability_comp_equiv
    (selectedObservationEquiv (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected).symm
    _ (selectedRawMarginal_isProbability G strategy selected positive j)
  have he : (fun z => selectedRawMarginal G strategy selected j
      ((selectedObservationEquiv (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected).symm z)) =
      fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected) := by
    funext z
    exact selectedRawMarginal_fullReveal G strategy selected j z
  rw [he] at h
  exact h

def selectedCommonLaw (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j × (Q₁ × Q₂)) :=
  toGameLaw (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
    (partialRevealMarginal_isProbability G.questions j _
      (selected_fullReveal_isProbability G strategy selected positive j))

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_SelectedCommonMarginalLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OccurrenceGame.toGame_success _root_.OAI.PerfectCompleteness.OccurrenceVertexEmbedding.restrict_extend _root_.OAI.PerfectCompleteness.OccurrenceVertexEmbedding.success_restrict _root_.OAI.PerfectCompleteness.OccurrenceVertexEmbedding.wins_restrict _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.PerfectCompleteness.SourceGame.questionGame_success _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Actual local completions of the unused questions, conditioned on common data
and the player's own embedded question. The raw row factors are explicit
finite weights. Their normalization reconstructs the actual selected common
law, including zero rows. The fallback independently samples base marginal
questions and then inserts the local input at the embedded coordinate.
-/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

section LocalNormalization

variable {I X Y : Type*} [Fintype I] [DecidableEq I]
  [Fintype X] [Fintype Y]

def updatedTableFallback (μ : FiniteDistribution X) (j : I) (x : X) :
    FiniteDistribution (I → X) :=
  (FiniteDistribution.table (fun _ : I => μ)).pushforward
    (fun l => Function.update l j x)

end LocalNormalization

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedLeftRaw (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (x : Q₁) (l : {i : Fin n // i ∉ selected} → Q₁) : ℝ :=
  (if l j = x then 1 else 0) * partialLeftFactor G.questions j s.2 l *
    selectedLocalTest strategy.1 selected (fun i => (s.1.1 i).1) s.1.2.1 l

def selectedRightRaw (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (y : Q₂) (r : {i : Fin n // i ∉ selected} → Q₂) : ℝ :=
  (if r j = y then 1 else 0) * partialRightFactor G.questions j s.2 r *
    selectedLocalTest strategy.2 selected (fun i => (s.1.1 i).2) s.1.2.2 r

omit [DecidableEq Q₂] in
theorem selectedLeftRaw_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (x : Q₁) (l : {i : Fin n // i ∉ selected} → Q₁) :
    0 ≤ selectedLeftRaw G strategy selected j s x l := by
  apply mul_nonneg
  · apply mul_nonneg
    · split <;> norm_num
    · exact Finset.prod_nonneg (fun i _ => revealLeftFactor_nonnegative G.questions (s.2 i) (l i.1))
  · exact selectedLocalTest_nonnegative _ _ _ _ _

omit [DecidableEq Q₁] in
theorem selectedRightRaw_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (y : Q₂) (r : {i : Fin n // i ∉ selected} → Q₂) :
    0 ≤ selectedRightRaw G strategy selected j s y r := by
  apply mul_nonneg
  · apply mul_nonneg
    · split <;> norm_num
    · exact Finset.prod_nonneg (fun i _ => revealRightFactor_nonnegative G.questions (s.2 i) (r i.1))
  · exact selectedLocalTest_nonnegative _ _ _ _ _

def selectedLeftCompletion (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (x : Q₁) : FiniteDistribution ({i : Fin n // i ∉ selected} → Q₁) :=
  normalizeOr (selectedLeftRaw G strategy selected j s x)
    (selectedLeftRaw_nonnegative G strategy selected j s x)
    (updatedTableFallback (G.questions.pushforward Prod.fst) j x)

def selectedRightCompletion (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (y : Q₂) : FiniteDistribution ({i : Fin n // i ∉ selected} → Q₂) :=
  normalizeOr (selectedRightRaw G strategy selected j s y)
    (selectedRightRaw_nonnegative G strategy selected j s y)
    (updatedTableFallback (G.questions.pushforward Prod.snd) j y)

def selectedCompletionScale (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (xy : Q₁ × Q₂) : ℝ :=
  G.questions.weight xy * (∏ i : selected, G.questions.weight (s.1.1 i)) *
    (if selectedLabelAccepts G selected s.1.1 s.1.2 then 1 else 0) /
      G.selectedSuccess strategy selected

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! The actual local completion mixture reproduces the repeated question law
conditioned on the selected wins. All hidden coordinates and reveal variables
are explicitly summed out. -/

namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedFullLeftCompletion (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (q : Q₁ × SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j) :
    FiniteDistribution (Fin n → Q₁) :=
  (selectedLeftCompletion G strategy selected j q.2 q.1).pushforward
    (mergeCoordinates selected (fun i => (q.2.1.1 i).1))

def selectedFullRightCompletion (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (q : Q₂ × SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j) :
    FiniteDistribution (Fin n → Q₂) :=
  (selectedRightCompletion G strategy selected j q.2 q.1).pushforward
    (mergeCoordinates selected (fun i => (q.2.1.1 i).2))

def selectedFullCompletionMixture (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    FiniteDistribution ((Fin n → Q₁) × (Fin n → Q₂)) :=
  ((selectedCommonLaw G strategy selected positive j).transport (Equiv.prodComm _ _)).mixture
    (fun z => (selectedFullLeftCompletion G strategy selected j (z.1.1,z.2)).product
      (selectedFullRightCompletion G strategy selected j (z.1.2,z.2)))

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! Actual finite shared seed laws for the bounded correlated sampler. -/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

universe u

def traceSeedLaw {σ : Type*} [Fintype σ] (μ : FiniteDistribution σ) :
    (n : Nat) → FiniteDistribution (TraceSeed σ n)
  | 0 => { weight := fun _ => 1, nonnegative := by intro; norm_num,
           normalized := by simp }
  | n + 1 => μ.product (traceSeedLaw μ n)

/-- The law of the two local outputs, driven by a seed chosen independently
of the question pair. Local maps receive only their own question. -/
def sharedOutputLaw {X Y S Seed : Type*}
    [Fintype X] [Fintype Y] [Fintype S] [Fintype Seed] [DecidableEq S]
    (μ : FiniteDistribution (X × Y)) (seedLaw : FiniteDistribution Seed)
    (left : Seed → X → S) (right : Seed → Y → S) :
    FiniteDistribution ((X × Y) × S × S) :=
  (μ.product seedLaw).pushforward
    (fun z => (z.1, left z.2 z.1.1, right z.2 z.1.2))

section Rectangle

open CorrelatedSampling

variable {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S]
  [Nonempty S] [DecidableEq S]

def samplerLocal (thresholds : List ℝ) (profile : X → FiniteDistribution S)
    (fallback : S) (n : Nat) (seed : TraceSeed (RectangleSeed thresholds S) n)
    (x : X) : S :=
  localSample (rectangleAccept thresholds (profile x).weight) Prod.fst fallback
    (traceList n seed)

def samplerOutputLaw (thresholds : List ℝ) (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (n : Nat) : FiniteDistribution ((X × Y) × S × S) :=
  sharedOutputLaw μ (traceSeedLaw (rectangleDistribution thresholds) n)
    (samplerLocal thresholds L fallback n) (samplerLocal thresholds R fallback n)

end Rectangle

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_CompletedSamplingLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Finite local completion after correlated sampling

One independent seed contains the original shared seed and two full response
tables. Its local reads give exactly the mixture of the requested completion
kernels. Applying those kernels contracts total variation. On a diagonal
target the same construction uses one common selected label.
-/

namespace UniqueGamesTheorem.Foundations.Repetition.CompletedSampling

open scoped BigOperators
open Games

noncomputable section

section Diagonal

variable {Z S : Type*} [Fintype Z] [Fintype S]

def diagonalLaw (σ : FiniteDistribution (Z × S)) : FiniteDistribution (Z × S × S) :=
  Information.toGameLaw (diagonalWeights σ.weight)
    (diagonalWeights_isProbability _ (Information.gameLaw_isProbability σ))

end Diagonal

section Completion

variable {X Y S Γ U V : Type*}
  [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ] [Fintype U] [Fintype V]
  [DecidableEq X] [DecidableEq Y] [DecidableEq S]

def seedLaw (γ : FiniteDistribution Γ)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    FiniteDistribution (Seed Γ X Y S U V) :=
  γ.product (KernelSampling.seedLaw L R)

def completionKernel (L : X × S → FiniteDistribution U)
    (R : Y × S → FiniteDistribution V) (z : (X × Y) × S × S) :
    FiniteDistribution (U × V) :=
  (L (z.1.1, z.2.1)).product (R (z.1.2, z.2.2))

/-- This is the shared-seed mixture used by `Game.localEmbeddingLaw`. -/
def outputLaw (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    FiniteDistribution (U × V) :=
  (seedLaw γ L R).mixture (fun seed =>
    μ.pushforward (fun q => (left sL seed q.1, right sR seed q.2)))

end Completion

section CoordinateCompletion

variable {I X Y S Γ : Type*}
  [Fintype I] [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y] [DecidableEq S]

def coordinateOutputLaw (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (j : I) (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution (I → X))
    (R : Y × S → FiniteDistribution (I → Y)) :
    FiniteDistribution ((I → X) × (I → Y)) :=
  (seedLaw γ L R).mixture (fun seed => μ.pushforward
    (fun q => (coordinateLeft j sL seed q.1, coordinateRight j sR seed q.2)))

end CoordinateCompletion

end

end UniqueGamesTheorem.Foundations.Repetition.CompletedSampling

end

section

/-! The two actual conditional common-data profiles used by the shared
sampler, with explicit normalized default laws on all null inputs. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedProfileFallback (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  (selectedCommonLaw G strategy selected positive j).pushforward Prod.fst

def selectedLeftProfile (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) (x : Q₁) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  toGameLaw
    (leftCommonProfile (selectedCommonLaw G strategy selected positive j).weight
      (selectedProfileFallback G strategy selected positive j).weight x)
    (leftCommonProfile_isProbability _ _
      (gameLaw_isProbability (selectedCommonLaw G strategy selected positive j))
      (gameLaw_isProbability (selectedProfileFallback G strategy selected positive j)) x)

def selectedRightProfile (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) (y : Q₂) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  toGameLaw
    (rightCommonProfile (selectedCommonLaw G strategy selected positive j).weight
      (selectedProfileFallback G strategy selected positive j).weight y)
    (rightCommonProfile_isProbability _ _
      (gameLaw_isProbability (selectedCommonLaw G strategy selected positive j))
      (gameLaw_isProbability (selectedProfileFallback G strategy selected positive j)) y)

def selectedLeftProfileError (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) : ℝ :=
  totalVariation (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedLeftProfile G strategy selected positive j z.2.1).weight z.1)

def selectedRightProfileError (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) : ℝ :=
  totalVariation (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedRightProfile G strategy selected positive j z.2.2).weight z.1)

def selectedSamplingTarget (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    FiniteDistribution ((Q₁ × Q₂) × SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  (selectedCommonLaw G strategy selected positive j).transport (Equiv.prodComm _ _)

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedEmbeddingError (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) : ℝ :=
  2 * selectedLeftProfileError G strategy selected positive j +
    2 * selectedRightProfileError G strategy selected positive j

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_TreeSourceSpaces
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.TreeSourceSpaces

open MixedSupport

variable {branch : Nat → Nat} {n t : Nat}

theorem one_mem_H (slots : RecursiveSpaces.Slots branch n → Fin t → Slot)
    (hbranch : ∀ k < n, 0 < branch k) : (1 : Domain slots → F2) ∈ H slots :=
  RecursiveSpaces.one_mem_space branch n (LeafDomain slots) hbranch

theorem one_mem_squareSpace (slots : RecursiveSpaces.Slots branch n → Fin t → Slot)
    (hbranch : ∀ k < n, 0 < branch k) :
    (1 : Domain slots → F2) ∈ PointwiseSpaces.squareSpace (H slots) :=
  RecursiveSpaces.one_mem_space_square (LeafDomain slots) hbranch

end PerfectCompleteness.TreeSourceSpaces

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_TreeCanonical
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.TreeCanonical

open MixedSupport TreeSourceSpaces

noncomputable section

variable {branch : Nat → Nat} {n t : Nat} {Y : Type*}

def numberedProjection {slots projected : RecursiveSpaces.Slots branch n → Fin t → Slot}
    (p : ∀ s k, Projection (slots s k) (projected s k)) :
    ∀ j, Projection (numberedSlots slots j) (numberedSlots projected j) :=
  fun j => p ((numbering branch n t).symm j).1 ((numbering branch n t).symm j).2

end

end PerfectCompleteness.TreeCanonical

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_OccurrenceGame
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

noncomputable section

namespace OccurrenceGame

variable {E Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype E] [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

def EndpointDetermined (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) : Prop :=
  ∀ e e', G.left e = G.left e' → G.right e = G.right e' →
    ∀ a b, G.accepts e a b = G.accepts e' a b

def chosenEndpointPredicate (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (x : Q₁) (y : Q₂) (a : A₁) (b : A₂) : Bool := by
  classical
  exact if h : ∃ e, G.left e = x ∧ G.right e = y then
    G.accepts (Classical.choose h) a b
  else false

def presentationOfDetermined (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (h : G.EndpointDetermined) : G.EndpointPresentation where
  predicate := chosenEndpointPredicate G
  agrees e a b := by
    have hex : ∃ e', G.left e' = G.left e ∧ G.right e' = G.right e :=
      ⟨e, rfl, rfl⟩
    simp only [chosenEndpointPredicate, dite_eq_left hex]
    exact h e (Classical.choose hex) (Classical.choose_spec hex).1.symm
      (Classical.choose_spec hex).2.symm a b

def repetition (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) (n : Nat) :
    OccurrenceGame (Fin n → E) (Fin n → Q₁) (Fin n → Q₂)
      (Fin n → A₁) (Fin n → A₂) := by
  classical
  exact
    { occurrences := G.occurrences.iid n
      left := fun e i => G.left (e i)
      right := fun e i => G.right (e i)
      accepts := fun e a b => decide (∀ i, G.accepts (e i) (a i) (b i) = true) }

def EndpointPresentation.repetition (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (p : G.EndpointPresentation) (n : Nat) : (G.repetition n).EndpointPresentation := by
  classical
  exact
    { predicate := fun x y a b => decide (∀ i, p.predicate (x i) (y i) (a i) (b i) = true)
      agrees := by
        intro e a b
        simp only [OccurrenceGame.repetition, p.agrees] }

end OccurrenceGame
end
end PerfectCompleteness

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineInitialHeaders
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_archive _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec.decodeWords_encodeWord _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter.counterTapes_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableWords.decode_rotationWords _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
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

/-- The complete raw initial-graph header phase, in an arbitrary caller program.
Only the output tape changes; its old suffix is preserved verbatim. -/
theorem headerTrace (nTape mTape scratch output : K)
    (_hnm : nTape ≠ mTape) (hnt : nTape ≠ scratch) (hno : nTape ≠ output)
    (hmt : mTape ≠ scratch) (hmo : mTape ≠ output) (hto : scratch ≠ output)
    (scanN restoreN scanM1 restoreM1 closeFirst scanM6 restoreM6 closeSecond : Λ)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScanN : program scanN = prefixScan nTape scratch output 1 scanN restoreN)
    (atRestoreN : program restoreN = loopAt scratch nTape id false restoreN (some scanM1))
    (atScanM1 : program scanM1 = prefixScan mTape scratch output 1 scanM1 restoreM1)
    (atRestoreM1 : program restoreM1 = loopAt scratch mTape id false restoreM1 (some closeFirst))
    (atCloseFirst : program closeFirst = pushWord output [true, false]
      (exitAt output (some scanM6)))
    (atScanM6 : program scanM6 = prefixScan mTape scratch output 6 scanM6 restoreM6)
    (atRestoreM6 : program restoreM6 = loopAt scratch mTape id false restoreM6 (some closeSecond))
    (atCloseSecond : program closeSecond = pushWord output [true, false] (exitAt output exit))
    (base : K → List Bool) (n m : ℕ) (nSuffix mSuffix : List Bool)
    (hn : base nTape = encodeWord n ++ nSuffix)
    (hm : base mTape = encodeWord m ++ mSuffix) (ht : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * n + 4 * m + 8]
      (some ⟨some scanN, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), Function.update base output
        ((encodeWords [n + m + 1, 6 * m + 1]).reverse ++ base output)⟩ := by
  let out1 := List.replicate n true ++ base output
  let out2 := List.replicate m true ++ out1
  let out3 := [false, true] ++ out2
  let out4 := List.replicate (6 * m) true ++ out3
  let out5 := [false, true] ++ out4
  let b1 := Function.update base output out1
  let b2 := Function.update base output out2
  let b3 := Function.update base output out3
  let b4 := Function.update base output out4
  let b5 := Function.update base output out5
  have first := prefixTrace nTape scratch output hnt hno hto 1 scanN restoreN
    (some scanM1) program atScanN atRestoreN base n nSuffix hn ht ambient register
  simp only [Nat.one_mul] at first
  change (MachineComposition.advance (TM2.step program))^[2 * n + 2]
    (some ⟨some scanN, (ambient, register), base⟩) =
    some ⟨some scanM1, (ambient, none), b1⟩ at first
  have second := prefixTrace mTape scratch output hmt hmo hto 1 scanM1 restoreM1
    (some closeFirst) program atScanM1 atRestoreM1 b1 m mSuffix
    (by simp [b1, hmo, hm]) (by simp [b1, hto, ht]) ambient none
  simp only [Nat.one_mul, b1, Function.update_self, Function.update_idem] at second
  change (MachineComposition.advance (TM2.step program))^[2 * m + 2]
    (some ⟨some scanM1, (ambient, none), b1⟩) =
    some ⟨some closeFirst, (ambient, none), b2⟩ at second
  have third := literalTrace output [true, false] closeFirst (some scanM6)
    program atCloseFirst b2 ambient none
  simp only [b2, Function.update_self, Function.update_idem] at third
  change (MachineComposition.advance (TM2.step program))^[1]
    (some ⟨some closeFirst, (ambient, none), b2⟩) =
    some ⟨some scanM6, (ambient, none), b3⟩ at third
  have fourth := prefixTrace mTape scratch output hmt hmo hto 6 scanM6 restoreM6
    (some closeSecond) program atScanM6 atRestoreM6 b3 m mSuffix
    (by simp [b3, hmo, hm]) (by simp [b3, hto, ht]) ambient none
  simp only [b3, Function.update_self, Function.update_idem] at fourth
  change (MachineComposition.advance (TM2.step program))^[2 * m + 2]
    (some ⟨some scanM6, (ambient, none), b3⟩) =
    some ⟨some closeSecond, (ambient, none), b4⟩ at fourth
  have fifth := literalTrace output [true, false] closeSecond exit
    program atCloseSecond b4 ambient none
  simp only [b4, Function.update_self, Function.update_idem] at fifth
  change (MachineComposition.advance (TM2.step program))^[1]
    (some ⟨some closeSecond, (ambient, none), b4⟩) =
    some ⟨exit, (ambient, none), b5⟩ at fifth
  have total := trace_trans _ (trace_trans _ (trace_trans _ (trace_trans _ first second)
    third) fourth) fifth
  have hsteps : (((2 * n + 2) + (2 * m + 2)) + 1 + (2 * m + 2)) + 1 =
      2 * n + 4 * m + 8 := by omega
  rw [hsteps] at total
  have hout : out5 = (encodeWords [n + m + 1, 6 * m + 1]).reverse ++ base output := by
    simp only [out5, out4, out3, out2, out1, encodeWords, encodeWord,
      List.reverse_append, List.reverse_replicate, List.reverse_cons, List.reverse_nil,
      List.append_nil, List.nil_append, List.append_assoc, List.singleton_append]
    rw [show n + m + 1 = 1 + m + n by omega,
      show 6 * m + 1 = 1 + 6 * m by omega]
    simp only [List.replicate_add, List.replicate_one, List.cons_append,
      List.nil_append, List.append_assoc]
  simpa only [b5, hout] using total

end UniqueGamesTheorem.Foundations.Complexity.MachineInitialHeaders

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_SourceNoiseParameterLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.EmptyContext.equation_second_eq_third _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.EmptyContext.pairedEquations_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHonest.taggedAssignment_left _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHonest.taggedAssignment_right _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.canonicalInput_half _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.extendRestricted_valid _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.restrictQuery_extendRestricted _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.card_event _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inl_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inr_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_address _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_cube _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_dart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_event _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_localEvent _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_pairCube _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_vertex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.inputCoordinateEquiv_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_edgeAddress_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_vertexAddress_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Queries.mask_idempotent _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Relations.relationAt_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AssignmentTester.cubeXor_right_twice _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AssignmentTester.flipAt_twice _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.averagingOperator_cayleyGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.coefficient_zeroFrequency _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.cubeXor_zeroFrequency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Real Walsh analysis on finite Boolean cubes. The basis and inversion
identities are proved from the explicit coordinate characters. -/

noncomputable section

namespace UniqueGamesTheorem.Foundations.Hastad

open scoped BigOperators
open Finset

theorem walsh_orthogonality {I : Type*} [Fintype I] [DecidableEq I]
    (s t : Cube I) :
    (𝔼 x, walsh s x * walsh t x) = if s = t then 1 else 0 := by
  classical
  rw [Fintype.expect_eq_sum_div_card, walsh_sum_orthogonality]
  split_ifs <;> simp

theorem sign_parseval {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → Bool) :
    (∑ s, coefficient (fun x => bitSign (f x)) s ^ 2) = 1 := by
  rw [walsh_parseval]
  simp

end UniqueGamesTheorem.Foundations.Hastad

end

end

section

noncomputable section

namespace UniqueGamesTheorem.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Walsh autocorrelation, proved by expanding the explicit basis. -/
theorem walsh_autocorrelation (B : Cube J → ℝ) (h : Cube J) :
    (𝔼 g, B g * B (cubeXor g h)) =
      ∑ s, coefficient B s ^ 2 * walsh s h := by
  conv_lhs =>
    enter [2, g, 2]
    rw [← walsh_inversion B (cubeXor g h)]
  simp_rw [Finset.mul_sum, walsh_xor]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have hterm : (fun g => B g * (coefficient B s * (walsh s g * walsh s h))) =
      (fun g => (coefficient B s * walsh s h) * (B g * walsh s g)) := by
    funext g
    ring
  rw [hterm, ← Finset.mul_expect]
  change (coefficient B s * walsh s h) * coefficient B s = _
  ring

end UniqueGamesTheorem.Foundations.Hastad

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_AssignmentTester
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.EmptyContext.equation_second_eq_third _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.EmptyContext.pairedEquations_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHonest.taggedAssignment_left _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHonest.taggedAssignment_right _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.canonicalInput_half _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.extendRestricted_valid _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.restrictQuery_extendRestricted _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.card_event _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inl_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inr_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_address _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_cube _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_dart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_event _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_localEvent _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_pairCube _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_vertex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.inputCoordinateEquiv_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_edgeAddress_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_vertexAddress_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Queries.mask_idempotent _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Relations.relationAt_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.averagingOperator_cayleyGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.coefficient_zeroFrequency _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.cubeXor_zeroFrequency
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

theorem blr_correlation (F : Cube A → Bool) :
    (𝔼 f, 𝔼 g, bitSign (F f) * bitSign (F g) * bitSign (F (cubeXor f g))) =
      ∑ s, coefficient (fun f => bitSign (F f)) s ^ 3 := by
  simp_rw [mul_assoc, ← Finset.mul_expect]
  conv_lhs =>
    enter [2, f, 2, 2, g, 2, 1]
    rw [cubeXor_comm]
  simp_rw [walsh_autocorrelation, Finset.mul_sum]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have heq (f : Cube A) : bitSign (F f) *
      (coefficient (fun f => bitSign (F f)) s ^ 2 * walsh s f) =
    coefficient (fun f => bitSign (F f)) s ^ 2 * (bitSign (F f) * walsh s f) := by ring
  simp_rw [heq, ← Finset.mul_expect]
  change coefficient (fun f => bitSign (F f)) s ^ 2 *
    coefficient (fun f => bitSign (F f)) s = _
  ring

theorem blrReject_fourier (F : Cube A → Bool) :
    blrReject F = (1 - ∑ s, coefficient (fun f => bitSign (F f)) s ^ 3) / 2 := by
  unfold blrReject
  simp_rw [disagree_eq, bitSign_xor, div_eq_mul_inv,
    ← Finset.expect_mul, Finset.expect_sub_distrib]
  simp only [Fintype.expect_const]
  rw [blr_correlation]

/-- The actual BLR test yields a nearby parity, with no stability theorem
or Fourier-structure hypothesis assumed. -/
theorem blr_near_parity (F : Cube A → Bool) :
    ∃ s : Cube A, distance F (parity s) ≤ blrReject F := by
  classical
  let c := coefficient (fun f => bitSign (F f))
  have hmass : (∑ s, c s ^ 2) = 1 := sign_parseval F
  have hlarge : ∃ s, (∑ t, c t ^ 3) ≤ c s := by
    by_contra hn
    push Not at hn
    have hpos : ∃ s, 0 < c s ^ 2 := by
      by_contra hh
      push Not at hh
      have hz := Finset.sum_nonpos (s := Finset.univ) (fun s _ => hh s)
      linarith
    obtain ⟨s₀, hs₀⟩ := hpos
    have hle (s : Cube A) (_ : s ∈ Finset.univ) :
        c s ^ 3 ≤ (∑ t, c t ^ 3) * c s ^ 2 := by
      have h := mul_le_mul_of_nonneg_right (hn s).le (sq_nonneg (c s))
      nlinarith
    have hlt : c s₀ ^ 3 < (∑ t, c t ^ 3) * c s₀ ^ 2 := by
      have h := mul_lt_mul_of_pos_right (hn s₀) hs₀
      nlinarith
    have hsum := Finset.sum_lt_sum hle ⟨s₀, Finset.mem_univ _, hlt⟩
    rw [← Finset.mul_sum, hmass, mul_one] at hsum
    exact (lt_irrefl _ hsum)
  obtain ⟨s, hs⟩ := hlarge
  refine ⟨s, ?_⟩
  rw [distance_parity, blrReject_fourier]
  dsimp [c] at hs
  linarith

variable {K : Type*} [Fintype K] [Nonempty K]

/-- Proximity soundness of the actual four finite tests. The only promise
is the property being tested: the queried input is δ-far from every legal label. -/
theorem tester_proximity_soundness (label : A → K → Bool) (σ : K → Bool)
    (F : Cube A → Bool) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4)
    (hfar : ∀ a, δ ≤ distance σ (label a)) :
    δ / 256 ≤ testerReject label σ F := by
  have hblr := blrReject_nonneg F
  have hand := andReject_nonneg F
  have hunit := unitReject_nonneg F
  have hin := inputReject_nonneg label σ F
  by_cases hb : δ / 64 ≤ blrReject F
  · unfold testerReject
    linarith
  obtain ⟨s, hs⟩ := blr_near_parity F
  by_cases hz : s = fun _ => false
  · subst s
    have hu := unitReject_zero_parity F
    unfold testerReject
    linarith
  have hsome : ∃ i, s i = true := by
    by_contra hh
    push Not at hh
    apply hz
    funext i
    have h := hh i
    cases hi : s i <;> simp_all
  obtain ⟨i, hi⟩ := hsome
  by_cases htwo : ∃ j, i ≠ j ∧ s j = true
  · obtain ⟨j, hij, hj⟩ := htwo
    have ha := parity_and_rejection s i j hi hj hij
    have ht := andReject_transfer F s
    unfold testerReject
    linarith
  · have heq : s = singleMask i := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [singleMask, hi]
      · have hj : s j = false := by
          cases hv : s j
          · rfl
          · exact False.elim (htwo ⟨j, Ne.symm hji, hv⟩)
        simp [singleMask, hji, hj]
    subst s
    have ht := inputReject_transfer label σ F i
    have hf := hfar i
    unfold testerReject
    linarith

section

omit [Fintype A] [DecidableEq A] [Fintype K] [Nonempty K]

theorem eventReject_unit (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventReject label σ F 2 k f g r₀ r₁ r₂ =
      disagree (selfCorrect F (fun _ => true) r₀) true := by
  simp only [eventReject, eventAccepts, eventQueries, oracleAnswer]
  norm_num
  change truth (!(selfCorrect F (fun _ => true) r₀)) =
    disagree (selfCorrect F (fun _ => true) r₀) true
  cases selfCorrect F (fun _ => true) r₀ <;> norm_num [truth, disagree]

theorem eventReject_input (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventReject label σ F 3 k f g r₀ r₁ r₂ =
      disagree (σ k) (selfCorrect F (fun a => label a k) r₀) := by
  simp [eventReject, eventAccepts, eventQueries, oracleAnswer,
    truth_not_decide_eq, selfCorrect]

/-- The honest proof satisfies each explicit event separately, including all
padding slots, so it supplies actual satisfying labels in the incidence graph. -/
theorem event_perfect_completeness (label : A → K → Bool) (a : A)
    (kind : Fin 4) (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventAccepts kind (fun slot => oracleAnswer (label a) (fun x => x a)
      (eventQueries label kind k f g r₀ r₁ r₂ slot)) = true := by
  have hkind : kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by omega
  have hreject : eventReject label (label a) (fun x => x a) kind k f g r₀ r₁ r₂ = 0 := by
    rcases hkind with h | h | h | h <;> subst kind
    · simp [eventReject_blr, cubeXor, disagree]
    · simp [eventReject_and, selfCorrect_dictator, cubeAnd, disagree]
    · simp [eventReject_unit, selfCorrect_dictator, disagree]
    · simp [eventReject_input, selfCorrect_dictator, disagree]
  unfold eventReject at hreject
  cases h : eventAccepts kind (fun slot => oracleAnswer (label a) (fun x => x a)
    (eventQueries label kind k f g r₀ r₁ r₂ slot)) <;> simp_all [truth]

end

theorem explicitTesterReject_eq (label : A → K → Bool) (σ : K → Bool)
    (F : Cube A → Bool) : explicitTesterReject label σ F = testerReject label σ F := by
  unfold explicitTesterReject
  rw [Fintype.expect_eq_sum_div_card]
  simp [Fin.sum_univ_succ, eventReject_blr, eventReject_and, eventReject_unit,
    eventReject_input, testerReject, blrReject, andReject, unitReject, inputReject, add_assoc]

theorem explicit_proximity_soundness (label : A → K → Bool) (σ : K → Bool)
    (F : Cube A → Bool) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4)
    (hfar : ∀ a, δ ≤ distance σ (label a)) :
    δ / 256 ≤ explicitTesterReject label σ F := by
  rw [explicitTesterReject_eq]
  exact tester_proximity_soundness label σ F hδ hδ' hfar

end UniqueGamesTheorem.Foundations.PCP.AssignmentTester

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_CodeComposition
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.EmptyContext.equation_second_eq_third _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.EmptyContext.pairedEquations_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHonest.taggedAssignment_left _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHonest.taggedAssignment_right _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.canonicalInput_half _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.extendRestricted_valid _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.restrictQuery_extendRestricted _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.card_event _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inl_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inr_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_address _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_cube _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_dart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_event _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_localEvent _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_pairCube _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_vertex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.inputCoordinateEquiv_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_edgeAddress_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_vertexAddress_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Queries.mask_idempotent _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Relations.relationAt_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AssignmentTester.cubeXor_right_twice _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AssignmentTester.flipAt_twice _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.averagingOperator_cayleyGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.coefficient_zeroFrequency _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.cubeXor_zeroFrequency
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

theorem codeword_distance {A : Type*} [Fintype A] [DecidableEq A]
    {a b : A} (hab : a ≠ b) :
    relativeDistance (codeword a) (codeword b) = 1 / 2 := by
  rw [relativeDistance_eq_sign]
  have horth := walsh_orthogonality (singletonMask a) (singletonMask b)
  rw [ite_eq_right (singletonMask_ne hab)] at horth
  simp_rw [walsh_singletonMask] at horth
  change (1 - 𝔼 x : Cube A, bitSign (x a) * bitSign (x b)) / 2 = 1 / 2
  rw [horth]
  norm_num

theorem distance_from_other_codeword {A : Type*} [Fintype A] [DecidableEq A]
    [Nonempty A] (f : Cube A → Bool) {a : A} (ha : a ≠ nearest f) :
    1 / 4 ≤ relativeDistance f (codeword a) := by
  have htri := relativeDistance_triangle (codeword (nearest f)) f (codeword a)
  rw [codeword_distance (Ne.symm ha), relativeDistance_comm (codeword (nearest f)) f] at htri
  have hmin := nearest_minimal f a
  linarith

/-- Every satisfying encoded pair is far from a pair whose nearest decoding rejects. -/
theorem rejected_pair_far {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (accepts : A → A → Bool) (left right : Cube A → Bool)
    (hbad : accepts (nearest left) (nearest right) = false)
    (a b : A) (hgood : accepts a b = true) :
    1 / 8 ≤ relativeDistance (pairWord left right)
      (pairWord (codeword a) (codeword b)) := by
  rw [pairWord_distance]
  have hleft := relativeDistance_nonnegative left (codeword a)
  have hright := relativeDistance_nonnegative right (codeword b)
  by_cases ha : a = nearest left
  · have hb : b ≠ nearest right := by
      intro hb
      rw [ha, hb, hbad] at hgood
      cases hgood
    have hsep := distance_from_other_codeword right hb
    linarith
  · have hsep := distance_from_other_codeword left ha
    linarith

end UniqueGamesTheorem.Foundations.PCP.CodeComposition

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_AlphabetReductionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.EmptyContext.equation_second_eq_third _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.EmptyContext.pairedEquations_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHonest.taggedAssignment_left _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHonest.taggedAssignment_right _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.canonicalInput_half _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.extendRestricted_valid _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.restrictQuery_extendRestricted _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.card_event _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inl_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inr_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_address _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_cube _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_dart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_event _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_localEvent _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_pairCube _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_vertex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.inputCoordinateEquiv_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_edgeAddress_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_vertexAddress_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Queries.mask_idempotent _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Relations.relationAt_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.averagingOperator_cayleyGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.coefficient_zeroFrequency _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.cubeXor_zeroFrequency
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

theorem rejected_edge_tester_bound (accepts : A → A → Bool)
    (left right : Cube A → Bool)
    (F : Cube (LegalPair accepts) → Bool)
    (hbad : accepts (nearest left) (nearest right) = false) :
    1 / 2048 ≤ edgeTesterReject accepts left right F := by
  have hfar (p : LegalPair accepts) :
      (1 / 8 : ℝ) ≤ AssignmentTester.distance (pairWord left right) (pairEncoding accepts p) := by
    have h := rejected_pair_far accepts left right hbad p.1.1 p.1.2 p.2
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  have h := AssignmentTester.explicit_proximity_soundness (pairEncoding accepts)
    (pairWord left right) F (δ := 1 / 8) (by norm_num) (by norm_num) hfar
  norm_num at h
  exact h

end UniqueGamesTheorem.Foundations.PCP.AlphabetReduction

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

def acceptedCount (formula : Formula) (alice : AliceStrategy formula)
    (bob : BobStrategy formula) : List (Fin formula.clauses.length) → Nat
  | [] => 0
  | i :: rest => acceptedSlots (clauseAt formula i) (alice i)
      (honestAnswer (clauseAt formula i) bob) + acceptedCount formula alice bob rest

def failureCount (formula : Formula) (bob : BobStrategy formula) :
    List (Fin formula.clauses.length) → Nat
  | [] => 0
  | i :: rest => clauseFailure (clauseAt formula i) bob + failureCount formula bob rest

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

theorem evaluations_allIndices (F : Formula) (A : Fin F.variables → Bool) :
    ((allIndices F).map (fun i => (clauseAt F i).eval A)) = evaluationList F A := by
  calc
    _ = (List.ofFn (fun i : Fin F.clauses.length => F.clauses[i.val])).map
        (fun c => c.eval A) := by
      simp only [allIndices, List.finRange, clauseAt, List.map_ofFn, Function.comp_def]
    _ = _ := by rw [List.ofFn_getElem]; rfl

end UniqueGamesTheorem.Foundations.PCP.NameCompaction

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_InitialGraphLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.clause_eval_extend _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.clause_eval_restrict _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_variable_count _root_.OAI.PerfectCompleteness.SourceClause.localEval_restrict _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_variables _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_current _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_remaining _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialRows.relationWordsFor_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
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

instance vertexNonempty (F : Formula) : Nonempty (Vertex F) := ⟨dummyVertex F⟩

theorem incidenceAccept_true (F : Formula) (event : RandomEvent F) (a b : Label)
    (h : incidenceAccept F event a b = true) :
    localSatisfies (clauseAt F event.1) (toClauseAnswer a) = true ∧
      answerAt (toClauseAnswer a) event.2 = b.1 := by
  simp only [incidenceAccept, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

def honestLabeling (F : Formula) (A : Fin F.variables → Bool) : Vertex F → Label
  | .inl (.inl v) => variableLabel (A v)
  | .inl (.inr i) => fromClauseAnswer (honestAnswer (clauseAt F i) A)
  | .inr _ => variableLabel false

theorem incidence_honest (F : Formula) (A : Fin F.variables → Bool)
    (sat : ∀ c ∈ F.clauses, c.eval A = true) (event : RandomEvent F) :
    incidenceAccept F event (honestLabeling F A (clauseVertex F event.1))
      (honestLabeling F A (variableVertex F (nameAt (clauseAt F event.1) event.2))) = true := by
  have hc : (clauseAt F event.1).eval A = true := sat _ (List.getElem_mem _)
  simp [incidenceAccept, honestLabeling, clauseVertex, variableVertex, variableLabel,
    variableValid, honest_satisfies, honest_answerAt, hc]

theorem raw_completeness (F : Formula) (sat : F.Satisfiable) : (raw F).Satisfiable := by
  rcases sat with ⟨A, hA⟩
  refine ⟨honestLabeling F A, fun d => ?_⟩
  cases d with
  | inl pair =>
    rcases pair with ⟨event, orientation⟩
    cases orientation <;> exact incidence_honest F A hA event
  | inr u => rfl

theorem clauseAnswer_eq_of_slots (a b : ClauseAnswer)
    (h : ∀ s, answerAt a s = answerAt b s) : a = b := by
  rcases a with ⟨a₀, a₁, a₂⟩
  rcases b with ⟨b₀, b₁, b₂⟩
  have h₀ : a₀ = b₀ := h .first
  have h₁ : a₁ = b₁ := h .second
  have h₂ : a₂ = b₂ := h .third
  cases h₀; cases h₁; cases h₂; rfl

theorem raw_reflects (F : Formula) (sat : (raw F).Satisfiable) : F.Satisfiable := by
  rcases sat with ⟨labeling, hlabeling⟩
  let A : Fin F.variables → Bool := fun v => (labeling (variableVertex F v)).1
  have slot_correct (i : Fin F.clauses.length) (s : Slot) :
      localSatisfies (clauseAt F i) (toClauseAnswer (labeling (clauseVertex F i))) = true ∧
        answerAt (toClauseAnswer (labeling (clauseVertex F i))) s =
          A (nameAt (clauseAt F i) s) := by
    exact incidenceAccept_true F (i, s) _ _ (hlabeling (.inl ((i, s), false)))
  have clause_correct (i : Fin F.clauses.length) : (clauseAt F i).eval A = true := by
    have equal : toClauseAnswer (labeling (clauseVertex F i)) = honestAnswer (clauseAt F i) A :=
      clauseAnswer_eq_of_slots _ _ (fun s => by
        simpa only [honest_answerAt] using (slot_correct i s).2)
    have satisfied := (slot_correct i .first).1
    rw [equal, honest_satisfies] at satisfied
    exact satisfied
  refine ⟨A, fun c hc => ?_⟩
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hc
  simpa only [clauseAt, heq] using clause_correct ⟨i, hi⟩

theorem raw_satisfiable_iff (F : Formula) : (raw F).Satisfiable ↔ F.Satisfiable :=
  ⟨raw_reflects F, raw_completeness F⟩

end UniqueGamesTheorem.Foundations.PCP.InitialGraph

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_OverlayLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Executable indexing of the actual outgoing-dart clouds

Clouds are enumerated by filtering the input table's increasing dart-index
list. Ranking searches that list, and selection reads its indexed entry.
The same functions work for empty clouds without selecting a default dart.
Padded cloud indices put all old darts first and the dummy indices afterward.
All data functions below are executable; their proofs establish the connection
to the semantic graph's actual tail fibers.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex

open scoped BigOperators
open GraphTables DegreeReplacement

theorem card_paddedCloud (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) :
    Fintype.card (PaddedCloud t padding v) = cloudSize t v + padding v := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (paddedCloudEquiv t padding v)

end UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_TerminalCalls
attribute [-instance] _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
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

noncomputable instance terminalIndexDecidableEq (repeats : Nat → Nat)
    (p : Path branch n m) : DecidableEq (TerminalIndex repeats p) := by
  induction p with
  | refl n => exact inferInstanceAs (DecidableEq Unit)
  | @step n m i p ih =>
      letI : DecidableEq (TerminalIndex repeats p) := ih
      exact inferInstanceAs (DecidableEq
        ((Fin (repeats (n + 1)) × Bool) × TerminalIndex repeats p))

theorem drawSpace_eq_terminal (𝕜 : Type w) [Field 𝕜]
    (repeats : Nat → Nat) (p : Path branch n m) :
    ∀ (A : Slots branch n → Type u) (terminal : TerminalIndex repeats p),
      DrawSpace 𝕜 repeats p A (drawIndex repeats p terminal) =
        space 𝕜 branch m (p.family A) := by
  induction p with
  | refl n => intro A terminal; rfl
  | step i p ih =>
      intro A terminal
      exact ih (childFamily A i) terminal.2

noncomputable def terminalSpaceEquiv (𝕜 : Type w) [Field 𝕜]
    (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) (terminal : TerminalIndex repeats p) :
    DrawSpace 𝕜 repeats p A (drawIndex repeats p terminal) ≃
      space 𝕜 branch m (p.family A) :=
  Equiv.cast (drawSpace_eq_terminal 𝕜 repeats p A terminal)

end PerfectCompleteness.TerminalCalls

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_QuotientTableAgreementLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.QuotientTableAgreement

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters (F2)
open PartialTableInverse

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

variable {H K Y : Type*} [AddCommGroup H] [Module F2 H]
  [AddCommGroup K] [Module F2 K]
  [FiniteDimensional F2 H] [FiniteDimensional F2 K]
  [Fintype H] [Fintype K] [Fintype Y]

def projectedAgreement (W : Submodule F2 H)
    (f : (Module.Dual F2 (H ⧸ W) →ₗ[F2] K) → Option Y) : ℝ :=
  𝔼 a : {a : K // a ≠ 0}, 𝔼 X : Module.Dual F2 H →ₗ[F2] K, 𝔼 h : H,
    definedEquality f (MatrixRowQuotient.projectMatrix W X)
      (MatrixRowQuotient.projectMatrix W (FiniteRangeInverse.matrixStep X a.val h))

end
end PerfectCompleteness.QuotientTableAgreement

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_RestrictionRowsLaw
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.PerfectCompleteness.OutputAnnihilator.mem_bad _root_.OAI.PerfectCompleteness.TensorProjectedSlice.totalMatrix_apply
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

section Selection

variable {J : Type*} (sel : J → I)

omit [Fintype I] in
@[simp] theorem selectedRowsLinear_apply (A : Parameter W C') (j : J) :
    selectedRowsLinear W C' b sel A j = (b.coord (sel j)).comp A := rfl

end Selection

def affineRow (offset : Module.Dual F2 E) (row : Module.Dual F2 (E ⧸ W)) :
    Module.Dual F2 E := offset + row.comp W.mkQ

end
end PerfectCompleteness.RestrictionRowsLaw

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_RestrictionCrossLaw
attribute [-simp] _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.PerfectCompleteness.OutputAnnihilator.mem_bad _root_.OAI.PerfectCompleteness.TensorProjectedSlice.totalMatrix_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.RestrictionCrossLaw

noncomputable section

open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Foundations.Games
open RestrictionRowsLaw DualQuotientRows

variable {E C I : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup C] [Module F2 C] [Fintype I]
  (W : Submodule F2 E) (C' : Submodule F2 C) (b : Module.Basis I F2 C')

def rowPairEquiv (m : Nat) :
    ((Fin m ⊕ Fin m) → Module.Dual F2 (E ⧸ W)) ≃ₗ[F2]
      ((Fin m → W.dualAnnihilator) × (Fin m → W.dualAnnihilator)) :=
  (LinearEquiv.piCongrRight
    (fun _ : Fin m ⊕ Fin m => quotientRowEquiv W)).trans
      (LinearEquiv.sumArrowLequivProdArrow
        (Fin m) (Fin m) F2 W.dualAnnihilator)

variable {m : Nat} (sel : (Fin m ⊕ Fin m) → I)

def selectedPair : Parameter W C' →ₗ[F2]
    ((Fin m → W.dualAnnihilator) × (Fin m → W.dualAnnihilator)) :=
  (rowPairEquiv W m).toLinearMap.comp (selectedRowsLinear W C' b sel)

omit [Fintype I] in
@[simp] theorem selectedPair_fst (A : Parameter W C') (i : Fin m) :
    (selectedPair W C' b sel A).1 i =
      quotientRowEquiv W (rowsLinear W C' b A (sel (Sum.inl i))) := rfl

omit [Fintype I] in
@[simp] theorem selectedPair_snd (A : Parameter W C') (j : Fin m) :
    (selectedPair W C' b sel A).2 j =
      quotientRowEquiv W (rowsLinear W C' b A (sel (Sum.inr j))) := rfl

end
end PerfectCompleteness.RestrictionCrossLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_LowerAffineSliceRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.LowerAffineSliceRank

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.RankLevelFilter
open BilinearGramCompression

variable {E : Type*} [AddCommGroup E] [Module F2 E]
  [Fintype E] [FiniteDimensional F2 E]
  {ℓ m : Nat}
  [Fintype (Module.Dual F2 E)]

def matrixRows (X : E →ₗ[F2] (Fin ℓ → F2)) : Fin ℓ → Module.Dual F2 E :=
  fun i => (LinearMap.proj i).comp X

def testedGram (F : Module.Dual F2 E →ₗ[F2] Module.Dual F2 (Module.Dual F2 E))
    (X : E →ₗ[F2] (Fin ℓ → F2)) : Matrix (Fin ℓ) (Fin ℓ) F2 :=
  gram F (matrixRows X)


end
end PerfectCompleteness.LowerAffineSliceRank

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_ManyGoodRowsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.ManyGoodRows

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters (F2)
open UniqueGamesTheorem.Fourier.MatrixRestrictions UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.RankLevelFilter
open PerfectCompleteness.PartialTableInverse PerfectCompleteness.MatrixErasure

attribute [local instance] linearMapFintype

variable {E F Y : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype E] [Fintype F] [Fintype Y]

def IsGoodPoint (f : (E →ₗ[F2] F) → Option Y) (r : Nat) (ρ : ℝ)
    (X : E →ₗ[F2] F) : Prop :=
  ∃ A : RowMap F r, GoodRow f r ρ A (A.comp X)

def goodMass (f : (E →ₗ[F2] F) → Option Y) (r : Nat) (ρ : ℝ) : ℝ :=
  uniformMass (IsGoodPoint f r ρ)

def adviceMass (f : (E →ₗ[F2] F) → Option Y) (r : Nat) (ρ : ℝ) : ℝ :=
  𝔼 A : RowMap F r, 𝔼 X : E →ₗ[F2] F,
    if GoodRow f r ρ A (A.comp X) then (1 : ℝ) else 0

end
end PerfectCompleteness.ManyGoodRows



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OddLists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.OddLists

open scoped BigOperators

variable {A B : Type*} {s : Nat}

section Supports

variable [Fintype A]

theorem support_card_cast (f : A → ZMod 2) :
    ((support f).card : ZMod 2) = ∑ a, f a := by
  unfold support
  rw [Finset.natCast_card_filter]
  apply Finset.sum_congr rfl
  intro a _
  rcases binary_cases (f a) with hzero | hone
  · simp only [hzero, zero_ne_one, ite_false, if_false]
  · simp only [hone, ite_true, if_true]

theorem support_odd_of_sum_one (f : A → ZMod 2) (normalized : (∑ a, f a) = 1) :
    Odd (support f).card :=
  ZMod.natCast_eq_one_iff_odd.mp ((support_card_cast f).trans normalized)

end Supports

end PerfectCompleteness.OddLists

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OddListExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.OddListExtraction

open scoped BigOperators Classical
open PointwiseSpaces

variable {X Y A B : Type*}

section Form

variable (H : Submodule F2 (X → F2))

variable (q : X → A) (hmem : ∀ a, indicator q a ∈ H)

theorem form_atom_of_ne (z : Module.Dual F2 (squareSpace H)) {a b : A} (hab : a ≠ b) :
    multiplicationForm H z (atom H q hmem a) (atom H q hmem b) = 0 := by
  have hzero : productElement H (atom H q hmem a) (atom H q hmem b) = 0 := by
    apply Subtype.ext
    exact indicator_mul_of_ne q hab
  simp only [multiplicationForm_apply, hzero, map_zero]

theorem sum_diagonal [Fintype A] (z : Module.Dual F2 (squareSpace H))
    (hone : (1 : X → F2) ∈ squareSpace H) :
    ∑ a, diagonal H q hmem z a = z ⟨1, hone⟩ := by
  classical
  simp only [diagonal, multiplicationForm_apply, ← map_sum]
  congr 1
  apply Subtype.ext
  simp only [Submodule.coe_sum]
  change (∑ a, (indicator q a * indicator q a)) = (1 : X → F2)
  simp only [indicator_mul_self, sum_indicator]

end Form

end PerfectCompleteness.OddListExtraction

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_FunctionSpaceLowerRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.FunctionSpaceLowerRank

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.RankLevelFilter
open PointwiseSpaces

section FunctionSpace

variable {Ω : Type*} (H : Submodule F2 (Ω → F2)) [FiniteDimensional F2 H]
  {ℓ m : Nat}

def matrixForm (F : H →ₗ[F2] Module.Dual F2 H) :
    Module.Dual F2 (Module.Dual F2 H) →ₗ[F2]
      Module.Dual F2 (Module.Dual F2 (Module.Dual F2 H)) :=
  transportForm (Module.evalEquiv F2 H) F

end FunctionSpace


open MixedSupport CanonicalKeys
open ProductEvaluation (displayedJoint )

end
end PerfectCompleteness.FunctionSpaceLowerRank

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_HierarchicalMatrixTable
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
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

def displayed (background : Background (rows := rows) slots node)
    (X : Matrix (rows := rows) slots node) :
    NodeEmbedding.NumberedDomain slots → (Output branch n rows : Type) :=
  TreeCanonical.numberedFunction slots (fullJoint (assemble slots node background X))

end
end PerfectCompleteness.HierarchicalMatrixTable

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_MatrixTriangularFoldingLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
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

def Determined : Prop := ∀ b : W, ∀ x y : Assignment slots,
  other x = other y → b.val.val x = b.val.val y

def representative (X : CanonicalMatrixTable.Matrix (K := K) slots H) :
    CanonicalMatrixTable.Matrix (K := K) slots H :=
  MatrixRowQuotient.liftMatrix W s (MatrixRowQuotient.projectMatrix W X)

def response (X : CanonicalMatrixTable.Matrix (K := K) slots H) : K × Z :=
  CanonicalMatrixTable.response slots H other σ (representative slots H W s X)

end
end PerfectCompleteness.RepresentativeMatrixTable

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_TensorBucketEvaluationLemmas
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

variable (Z : Submodule F2 (Module.Dual F2 H))

def Compatible (X₀ : Module.Dual F2 H →ₗ[F2] K) (v : Z →ₗ[F2] K)
    (T : W ⊗[F2] H') : Prop :=
  (totalMatrix i W X₀ T).domRestrict Z = v

def targetAt (T₀ : W ⊗[F2] H') :
    ProjectedColumnSlice.projectedColumns i Z →ₗ[F2] W :=
  TensorRestriction.restrictionMap (ProjectedColumnSlice.projectedColumns i Z) T₀

def inducedTarget (X₀ : Module.Dual F2 H →ₗ[F2] K) (v : Z →ₗ[F2] K)
    (hne : ∃ T : W ⊗[F2] H', Compatible i W Z X₀ v T) :
    ProjectedColumnSlice.projectedColumns i Z →ₗ[F2] W :=
  targetAt i W Z (Classical.choose hne)

end
end PerfectCompleteness.TensorProjectedSlice



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_TupleIndexEmitterLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.PositiveFiberMass

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {Ω R : Type*} [Fintype Ω] [Fintype R]

def jMass (μ : FiniteDistribution Ω) (record : Ω → R) (J : Ω → Bool) (r : R) : ℝ :=
  UsefulMark.lowerFiberMass μ record J r

def matchMass (μ : FiniteDistribution Ω) (record : Ω → R)
    (J prediction : Ω → Bool) (r : R) : ℝ :=
  UsefulMark.lowerFiberMass μ record (fun x => J x && prediction x) r

def conditionalMatch (μ : FiniteDistribution Ω) (record : Ω → R)
    (J prediction : Ω → Bool) (r : R) : ℝ :=
  matchMass μ record J prediction r / jMass μ record J r

def goodRecord (μ : FiniteDistribution Ω) (record : Ω → R)
    (J prediction : Ω → Bool) (ρ : ℝ) (r : R) : Bool :=
  decide (0 < jMass μ record J r ∧ ρ ≤ conditionalMatch μ record J prediction r)

end
end PerfectCompleteness.PositiveFiberMass



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_GoodRowSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.GoodRowSampling

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters (F2)
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open PerfectCompleteness.ManyGoodRows

attribute [local instance] linearMapFintype

variable {E F Y : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype E] [Fintype F] [Fintype Y]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype Y] in
theorem witness_rowFiber_nonempty {f : (E →ₗ[F2] F) → Option Y}
    {r : Nat} {ρ : ℝ} {A : RowMap F r} {U : E →ₗ[F2] (Fin r → F2)}
    (w : Witness f r ρ A U) : Nonempty (RowFiber A U) :=
  ⟨⟨w.base, w.row_value⟩⟩

end
end PerfectCompleteness.GoodRowSampling

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_GoodAdviceEventsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.GoodAdviceEvents

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters (F2)
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open PerfectCompleteness.ManyGoodRows PerfectCompleteness.GoodRowSampling

attribute [local instance] linearMapFintype

variable {E F Y : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype E] [Fintype F] [Fintype Y]

def selectedColumn (f : (E →ₗ[F2] F) → Option Y) (r : Nat) (ρ : ℝ)
    (A : RowMap F r) (U : E →ₗ[F2] (Fin r → F2)) (X : E →ₗ[F2] F) : Bool :=
  if h : GoodRow f r ρ A U then
    let w := selectWitness f r ρ A U h
    decide (X.domRestrict w.columnSpace = w.base.domRestrict w.columnSpace)
  else false

def selectedAgreement (f : (E →ₗ[F2] F) → Option Y) (r : Nat) (ρ : ℝ)
    (A : RowMap F r) (U : E →ₗ[F2] (Fin r → F2)) (X : E →ₗ[F2] F) : Bool :=
  if h : GoodRow f r ρ A U then
    let w := selectWitness f r ρ A U h
    decide (X.domRestrict w.columnSpace = w.base.domRestrict w.columnSpace ∧
      f X = some w.value)
  else false

def J (f : (E →ₗ[F2] F) → Option Y) (r : Nat) (ρ : ℝ)
    (sample : RowMap F r × (E →ₗ[F2] F)) : Bool :=
  selectedColumn f r ρ sample.1 (sample.1.comp sample.2) sample.2

def I (f : (E →ₗ[F2] F) → Option Y) (r : Nat) (ρ : ℝ)
    (sample : RowMap F r × (E →ₗ[F2] F)) : Bool :=
  selectedAgreement f r ρ sample.1 (sample.1.comp sample.2) sample.2

def law (E F : Type*) [AddCommGroup E] [Module F2 E]
    [AddCommGroup F] [Module F2 F] [Fintype E] [Fintype F] (r : Nat) :
    FiniteDistribution (RowMap F r × (E →ₗ[F2] F)) :=
  (FiniteDistribution.uniform (RowMap F r)).product
    (FiniteDistribution.uniform (E →ₗ[F2] F))

end
end PerfectCompleteness.GoodAdviceEvents



namespace PerfectCompleteness.GoodAdviceFamily

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters (F2)
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.RankLevelFilter
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness.ManyGoodRows

attribute [local instance] linearMapFintype

variable {P : Type*} [Fintype P] {E Y : P → Type*} {F : Type*}
  [AddCommGroup F] [Module F2 F] [FiniteDimensional F2 F] [Fintype F]
  [∀ p, AddCommGroup (E p)] [∀ p, Module F2 (E p)]
  [∀ p, FiniteDimensional F2 (E p)] [∀ p, Fintype (E p)] [∀ p, Fintype (Y p)]

abbrev Sample (r : Nat) := Σ p : P, RowMap F r × (E p →ₗ[F2] F)

def law (μ : FiniteDistribution P) (r : Nat) :
    FiniteDistribution (Sample (E := E) (F := F) r) :=
  CompletionSoundness.sigmaLaw μ (fun p => GoodAdviceEvents.law (E p) F r)

end
end PerfectCompleteness.GoodAdviceFamily

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_RelativeDescendantProductsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.RelativeDescendantProducts

open TreeSourceSpaces HierarchicalArrays

variable {branch : Nat → Nat} {n t : Nat}

noncomputable section

theorem one_mem_rowSpace
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (hbranch : ∀ k < n, 0 < branch k) (upper : Nodes branch n) :
    (1 : NodeEmbedding.NumberedDomain slots → F2) ∈ NodeEmbedding.RowSpace slots upper := by
  have hb : ∀ k < Nodes.height upper, 0 < branch k :=
    fun k hk => hbranch k (Nat.lt_of_lt_of_le hk (Nodes.height_le upper))
  exact Submodule.mem_map_of_mem (TreeSourceSpaces.one_mem_H (nodeSlots slots upper) hb)

end
end PerfectCompleteness.RelativeDescendantProducts



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalFrozenTablesLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawIndexDecidableEq _root_.OAI.PerfectCompleteness.RecursiveSampler.drawIndexFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexDecidableEq _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
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

def prefixPathDepth (cutoff : Nat) : (depth : Nat) →
    PrefixDepth branch cutoff depth → Path branch (cutoff + depth) cutoff
  | 0, _ => .refl cutoff
  | depth + 1, pref => .step pref.1 (prefixPathDepth cutoff depth pref.2)

def castPath {a b cutoff : Nat} (h : a = b) (p : Path branch a cutoff) :
    Path branch b cutoff := h ▸ p

variable {root cutoff : Nat}

def prefixPath (hcut : cutoff ≤ root) (pref : Prefix branch root cutoff) :
    Path branch root cutoff :=
  castPath (Nat.add_sub_of_le hcut) (prefixPathDepth cutoff (root - cutoff) pref)

theorem prefix_nonempty (hcut : cutoff ≤ root)
    (hbranch : ∀ k < root, 0 < branch k) : Nonempty (Prefix branch root cutoff) := by
  obtain ⟨leaf⟩ := GeometricPath.slots_nonempty root hbranch
  exact ⟨(splitEquiv hcut leaf).1⟩

noncomputable section

def prefixLaw (hcut : cutoff ≤ root) (hbranch : ∀ k < root, 0 < branch k) :
    FiniteDistribution (Prefix branch root cutoff) := by
  letI := prefix_nonempty hcut hbranch
  exact FiniteDistribution.uniform _

end
end PerfectCompleteness.GeometricCutSplit



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_RepresentativeBucketCollisionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.RepresentativeBucketCollision

noncomputable section

open scoped Classical
open ClauseSupport MixedSupport CanonicalKeys
open DirectionQuotient (F2)
open TwoResponseCollision
open UniqueGamesTheorem.Foundations.Games

variable {n : Nat} {K Z : Type*} [AddCommGroup K] [Module F2 K]
  (slots : Fin n → Slot) (H : Submodule F2 (Assignment slots → F2))
  (other : Assignment slots → Z) (σ : KeyStrategy.Strategy n)
  (W : Submodule F2 H) (s : (H ⧸ W) →ₗ[F2] H)
  (hs : W.mkQ.comp s = LinearMap.id)

def bucketAccepted (a : K) (X : CanonicalMatrixTable.Matrix (K := K) slots H) (h : H) : Bool :=
  decide (CanonicalMatrixTable.Accepts slots H other σ a (EvaluationMatrix.shift H X a h))

end
end PerfectCompleteness.RepresentativeBucketCollision



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalPrediction
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HierarchicalPrediction

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

section Selection

variable {E K Y : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup K] [Module F2 K] [FiniteDimensional F2 E]
  [FiniteDimensional F2 K] [Fintype E] [Fintype K] [Fintype Y]

def selectedValue (f : (E →ₗ[F2] K) → Option Y) (r : Nat) (ρ : ℝ)
    (A : ManyGoodRows.RowMap K r) (X : E →ₗ[F2] K) : Option Y :=
  if h : ManyGoodRows.GoodRow f r ρ A (A.comp X) then
    some (ManyGoodRows.selectWitness f r ρ A (A.comp X) h).value
  else none

end Selection

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)
  (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

variable (lower : Nodes branch n) (hne : upper ≠ lower) (a : Block rows lower)

def rightUpper (X : HierarchicalMatrixTable.Matrix (rows := rows) slots upper) :
    Block rows upper :=
  (KeyStrategy.response σ .right (TreeCanonical.numberedSlots slots)
    (BlockQuotient.projectBlock lower a ∘
      HierarchicalMatrixTable.displayed slots upper background X)).2.1 ⟨upper, hne⟩

def LowerAccepts (X : HierarchicalMatrixTable.Matrix (rows := rows) slots upper) : Prop :=
  CanonicalEdges.coarsen (TreeCanonical.numberedSlots slots)
    (HierarchicalMatrixTable.displayed slots upper background X)
    (BlockQuotient.projectBlock lower a)
    (KeyStrategy.label σ .left (TreeCanonical.numberedSlots slots)
      (HierarchicalMatrixTable.displayed slots upper background X)) =
    KeyStrategy.label σ .right (TreeCanonical.numberedSlots slots)
      (BlockQuotient.projectBlock lower a ∘
        HierarchicalMatrixTable.displayed slots upper background X)

end
end PerfectCompleteness.HierarchicalPrediction

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_TensorRowAdviceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.TensorRowAdvice

noncomputable section

open scoped Classical TensorProduct
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

section Algebra

variable {K H H' D : Type*} [AddCommGroup K] [Module F2 K]
  [AddCommGroup H] [Module F2 H] [AddCommGroup H'] [Module F2 H']
  [AddCommGroup D] [Module F2 D] [FiniteDimensional F2 H']
  (i : H' →ₗ[F2] H) (W : Submodule F2 K)

theorem rowAdvice_totalMatrix (A : K →ₗ[F2] D) (hW : W ≤ LinearMap.ker A)
    (X₀ : Module.Dual F2 H →ₗ[F2] K) (T : W ⊗[F2] H') :
    A.comp (TensorProjectedSlice.totalMatrix i W X₀ T) = A.comp X₀ := by
  apply LinearMap.ext
  intro z
  change A (X₀ z + (TensorRestriction.tensorEquivHom T (i.dualMap z) : K)) = A (X₀ z)
  rw [map_add]
  have hzero : A (TensorRestriction.tensorEquivHom T (i.dualMap z) : K) = 0 :=
    LinearMap.mem_ker.mp (hW (TensorRestriction.tensorEquivHom T (i.dualMap z)).property)
  rw [hzero, add_zero]

theorem rowAdvice_projectMatrix (A : K →ₗ[F2] D) (hW : W ≤ LinearMap.ker A)
    (B : Submodule F2 H) (X₀ : Module.Dual F2 H →ₗ[F2] K)
    (T : W ⊗[F2] H') :
    A.comp (MatrixRowQuotient.projectMatrix B (TensorProjectedSlice.totalMatrix i W X₀ T)) =
      A.comp (MatrixRowQuotient.projectMatrix B X₀) := by
  apply LinearMap.ext
  intro q
  exact LinearMap.congr_fun (rowAdvice_totalMatrix i W A hW X₀ T) (B.mkQ.dualMap q)

end Algebra

end
end PerfectCompleteness.TensorRowAdvice



namespace PerfectCompleteness.TensorSelectedSlice

noncomputable section

open scoped Classical TensorProduct
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {K H H' Y : Type*} [AddCommGroup K] [Module F2 K]
  [AddCommGroup H] [Module F2 H] [AddCommGroup H'] [Module F2 H']
  [FiniteDimensional F2 H'] [FiniteDimensional F2 H] [FiniteDimensional F2 K]
  [Fintype H] [Fintype K] [Fintype Y]
  (i : H' →ₗ[F2] H) (W : Submodule F2 K) (B : Submodule F2 H)

abbrev projectedMatrix (X₀ : Module.Dual F2 H →ₗ[F2] K) (T : W ⊗[F2] H') :=
  MatrixRowQuotient.projectMatrix B (TensorProjectedSlice.totalMatrix i W X₀ T)

omit [FiniteDimensional F2 H] [FiniteDimensional F2 K] [Fintype H] [Fintype K] in
theorem projectedMatrix_eq_totalMatrix
    (X₀ : Module.Dual F2 H →ₗ[F2] K) (T : W ⊗[F2] H') :
    projectedMatrix i W B X₀ T =
      TensorProjectedSlice.totalMatrix (B.mkQ.comp i) W
        (MatrixRowQuotient.projectMatrix B X₀) T := by
  apply LinearMap.ext
  intro q
  rfl

variable (f : (Module.Dual F2 (H ⧸ B) →ₗ[F2] K) → Option Y)
  (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap K r)
  (X₀ : Module.Dual F2 H →ₗ[F2] K)

def witness
    (hgood : ManyGoodRows.GoodRow f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀))) :
    ManyGoodRows.Witness f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀)) :=
  ManyGoodRows.selectWitness f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀)) hgood

def columnSpace
    (hgood : ManyGoodRows.GoodRow f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀))) :
    Submodule F2 (Module.Dual F2 H') :=
  ProjectedColumnSlice.projectedColumns (B.mkQ.comp i)
    (witness B f r ρ A X₀ hgood).columnSpace

variable (hW : W ≤ LinearMap.ker A)

include hW

omit [FiniteDimensional F2 H] [FiniteDimensional F2 K] [Fintype Y] in
theorem J_eq_decide_columns
    (hgood : ManyGoodRows.GoodRow f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀)))
    (T : W ⊗[F2] H') :
    GoodAdviceEvents.J f r ρ (A, projectedMatrix i W B X₀ T) =
      decide ((projectedMatrix i W B X₀ T).domRestrict
          (witness B f r ρ A X₀ hgood).columnSpace =
        (witness B f r ρ A X₀ hgood).base.domRestrict
          (witness B f r ρ A X₀ hgood).columnSpace) := by
  change GoodAdviceEvents.selectedColumn f r ρ A
    (A.comp (projectedMatrix i W B X₀ T)) (projectedMatrix i W B X₀ T) = _
  unfold GoodAdviceEvents.selectedColumn
  have hrow : A.comp (projectedMatrix i W B X₀ T) =
      A.comp (MatrixRowQuotient.projectMatrix B X₀) :=
    TensorRowAdvice.rowAdvice_projectMatrix i W A hW B X₀ T
  rw [hrow]
  simp only [dite_eq_left hgood, witness]
  exact decide_eq_decide.mpr Iff.rfl

omit [FiniteDimensional F2 H] [FiniteDimensional F2 K] [Fintype Y] in
theorem J_iff_compatible
    (hgood : ManyGoodRows.GoodRow f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀)))
    (T : W ⊗[F2] H') :
    GoodAdviceEvents.J f r ρ (A, projectedMatrix i W B X₀ T) = true ↔
      TensorProjectedSlice.Compatible (B.mkQ.comp i) W
        (witness B f r ρ A X₀ hgood).columnSpace
        (MatrixRowQuotient.projectMatrix B X₀)
        ((witness B f r ρ A X₀ hgood).base.domRestrict
          (witness B f r ρ A X₀ hgood).columnSpace) T := by
  calc
    _ ↔ (projectedMatrix i W B X₀ T).domRestrict
        (witness B f r ρ A X₀ hgood).columnSpace =
      (witness B f r ρ A X₀ hgood).base.domRestrict
        (witness B f r ρ A X₀ hgood).columnSpace := by
      rw [J_eq_decide_columns i W B f r ρ A X₀ hW hgood T, decide_eq_true_eq]
    _ ↔ _ := Iff.of_eq (congrArg
      (fun X : Module.Dual F2 (H ⧸ B) →ₗ[F2] K =>
        X.domRestrict (witness B f r ρ A X₀ hgood).columnSpace =
          (witness B f r ρ A X₀ hgood).base.domRestrict
            (witness B f r ρ A X₀ hgood).columnSpace)
      (projectedMatrix_eq_totalMatrix i W B X₀ T))

omit [FiniteDimensional F2 H] [FiniteDimensional F2 K] [Fintype Y] in
theorem exists_compatible
    (hgood : ManyGoodRows.GoodRow f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀)))
    (hne : ∃ T : W ⊗[F2] H', GoodAdviceEvents.J f r ρ (A, projectedMatrix i W B X₀ T) = true) :
    ∃ T : W ⊗[F2] H', TensorProjectedSlice.Compatible (B.mkQ.comp i) W
      (witness B f r ρ A X₀ hgood).columnSpace
      (MatrixRowQuotient.projectMatrix B X₀)
      ((witness B f r ρ A X₀ hgood).base.domRestrict
        (witness B f r ρ A X₀ hgood).columnSpace) T := by
  obtain ⟨T, hT⟩ := hne
  exact ⟨T, (J_iff_compatible i W B f r ρ A X₀ hW hgood T).mp hT⟩

def target
    (hgood : ManyGoodRows.GoodRow f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀)))
    (hne : ∃ T : W ⊗[F2] H', GoodAdviceEvents.J f r ρ (A, projectedMatrix i W B X₀ T) = true) :
    columnSpace i B f r ρ A X₀ hgood →ₗ[F2] W :=
  TensorProjectedSlice.inducedTarget (B.mkQ.comp i) W
    (witness B f r ρ A X₀ hgood).columnSpace
    (MatrixRowQuotient.projectMatrix B X₀)
    ((witness B f r ρ A X₀ hgood).base.domRestrict
      (witness B f r ρ A X₀ hgood).columnSpace)
    (exists_compatible i W B f r ρ A X₀ hW hgood hne)

end
end PerfectCompleteness.TensorSelectedSlice



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_BucketUniformLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexDecidableEq _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.stepFactorFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.RecursiveSampler

open PointwiseSpaces RecursiveSpaces DescendantSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

universe u w

variable {branch : Nat → Nat} {n m : Nat}

variable (𝕜 : Type w) [Field 𝕜]

noncomputable def stepCombine (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    (z : OrdinaryTape 𝕜 repeats i p A ×
      (CallIndex repeats n → space 𝕜 branch n (childFamily A i))) :
    space 𝕜 branch (n + 1) A :=
  combine 𝕜 A i (repeats (n + 1)) z.1
    (fun h => z.2 (h, false)) (fun h => z.2 (h, true))

noncomputable section

variable [Finite 𝕜]

instance childFamilyFinite (A : Slots branch (n + 1) → Type u)
    [hA : ∀ s, Finite (A s)] (i : Fin (branch n)) :
    ∀ s, Finite (childFamily A i s) := fun s => hA (i, s)

instance childSquareFintype (A : Slots branch (n + 1) → Type u)
    [hA : ∀ s, Finite (A s)] (i : Fin (branch n)) :
    Fintype (squareSpace (space 𝕜 branch n (childFamily A i))) := by
  letI : ∀ s, Finite (childFamily A i s) := fun s => hA (i, s)
  exact Fintype.ofFinite _

instance ordinaryDrawFintype (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    [∀ s, Finite (A s)] (j : OffPath i) :
    Fintype (DrawSpace 𝕜 repeats (.step i p) A (.inl j)) :=
  drawSpaceFintype 𝕜 repeats (.step i p) A (.inl j)

instance ordinaryTapeFintype (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    [∀ s, Finite (A s)] : Fintype (OrdinaryTape 𝕜 repeats i p A) := by
  letI : ∀ j : OffPath i, Fintype (DrawSpace 𝕜 repeats (.step i p) A (.inl j)) :=
    fun j => drawSpaceFintype 𝕜 repeats (.step i p) A (.inl j)
  exact Pi.instFintype

instance callTapesFintype (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    [hA : ∀ s, Finite (A s)] : Fintype (CallTapes 𝕜 repeats i p A) := by
  letI : ∀ s, Finite (childFamily A i s) := fun s => hA (i, s)
  letI : Fintype (Tape 𝕜 repeats p (childFamily A i)) :=
    @Pi.instFintype (DrawIndex repeats p)
      (DrawSpace 𝕜 repeats p (childFamily A i))
      (drawIndexDecidableEq repeats p) (drawIndexFintype repeats p)
      (fun j => drawSpaceFintype 𝕜 repeats p (childFamily A i) j)
  exact Pi.instFintype

def ordinaryLaw (𝕜 : Type w) [Field 𝕜] [Finite 𝕜]
    (repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (A : Slots branch (n + 1) → Type u) [∀ s, Finite (A s)] :
    FiniteDistribution (OrdinaryTape 𝕜 repeats i p A) := by
  letI : ∀ j : OffPath i, Fintype (DrawSpace 𝕜 repeats (.step i p) A (.inl j)) :=
    fun j => drawSpaceFintype 𝕜 repeats (.step i p) A (.inl j)
  letI : ∀ j : OffPath i, Nonempty (DrawSpace 𝕜 repeats (.step i p) A (.inl j)) :=
    fun j => ⟨zeroDraw 𝕜 repeats (.step i p) A (.inl j)⟩
  exact FiniteProduct.law (fun j : OffPath i =>
    FiniteDistribution.uniform (DrawSpace 𝕜 repeats (.step i p) A (.inl j)))

def callTapeLaw (𝕜 : Type w) [Field 𝕜] [Finite 𝕜]
    (repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (A : Slots branch (n + 1) → Type u) [hA : ∀ s, Finite (A s)] :
    FiniteDistribution (CallTapes 𝕜 repeats i p A) := by
  letI : ∀ s, Finite (childFamily A i s) := fun s => hA (i, s)
  exact FiniteProduct.law (fun _ : CallIndex repeats n =>
    tapeLaw 𝕜 repeats p (childFamily A i))

end
end PerfectCompleteness.RecursiveSampler

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CollisionAveragingLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SparseProjection

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness SmallBias DensityVariation

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

def projectedLaw (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
    (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) : FiniteDistribution ((i : I) → Ω i) :=
  FiniteProduct.law (fun i => reweight (P i) (localDensity β q i)
    (fun x => add_nonneg (sub_nonneg.mpr hβ') (mul_nonneg hβ (nonnegative i x)))
    (local_mean P q mean β i))

end
end PerfectCompleteness.SparseProjection


namespace PerfectCompleteness.ProjectionPosterior

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness SmallBias DensityVariation SparseProjection CleanConditioning

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

def posteriorMask (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
    (x : (i : I) → Ω i) : FiniteDistribution (I → Bool) :=
  FiniteProduct.law fun i => bernoulli (posterior β q i (x i))
    (posterior_nonnegative β hβ hβ' q nonnegative i (x i))
    (posterior_le_one β hβ hβ' q nonnegative i (x i))

def forward (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
    (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1) :
    FiniteDistribution ((I → Bool) × ((i : I) → Ω i)) :=
  kernelJoint (FiniteProduct.law fun _ : I => bernoulli β hβ hβ'.le)
    (fun mask => FiniteProduct.law fun i =>
      if mask i then reweight (P i) (q i) (nonnegative i) (mean i) else P i)

def reverse (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
    (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1) :
    FiniteDistribution (((i : I) → Ω i) × (I → Bool)) :=
  kernelJoint (projectedLaw P q nonnegative mean β hβ hβ'.le)
    (posteriorMask β hβ hβ' q nonnegative)

end
end PerfectCompleteness.ProjectionPosterior


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalAgreementMean
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalAgreementMean

noncomputable section

open scoped BigOperators Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n)

abbrev Matrix := HierarchicalMatrixTable.Matrix (rows := rows) slots upper

local instance backgroundFintype : Fintype (Background (rows := rows) slots upper) :=
  Fintype.ofFinite _

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _

local instance valueFintype :
    Fintype (Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :=
  Fintype.ofFinite _

abbrev PairRecord :=
  Background (rows := rows) slots upper ×
    (Matrix (rows := rows) slots upper × Matrix (rows := rows) slots upper)

abbrev BucketSample :=
  BucketSampler.Direction (rows (Nodes.height upper)) ×
    (BucketSampler.Tape (rows (Nodes.height upper)) (NodeEmbedding.RowSpace slots upper) ×
      NodeEmbedding.RowSpace slots upper)

def bucketLaw (hrows : 0 < rows (Nodes.height upper)) :
    FiniteDistribution (BucketSample (rows := rows) slots upper) := by
  letI : Nonempty (BucketSampler.Direction (rows (Nodes.height upper))) :=
    ⟨BucketUniform.coordinateDirection ⟨0, hrows⟩⟩
  exact (FiniteDistribution.uniform (BucketSampler.Direction (rows (Nodes.height upper)))).product
    ((BucketSampler.tapeLaw (rows (Nodes.height upper))
      (FiniteDistribution.uniform (NodeEmbedding.RowSpace slots upper))).product
        (FiniteDistribution.uniform (NodeEmbedding.RowSpace slots upper)))

def pairRecord
    (sample : Background (rows := rows) slots upper × BucketSample (rows := rows) slots upper) :
    PairRecord (rows := rows) slots upper :=
  (sample.1,
    (BucketMatrixResampling.assembledMatrix (NodeEmbedding.RowSpace slots upper)
      (rows (Nodes.height upper)) sample.2.2.1,
    BucketMatrixResampling.assembledMatrix (NodeEmbedding.RowSpace slots upper)
      (rows (Nodes.height upper)) (Function.update sample.2.2.1 sample.2.1 sample.2.2.2)))

def referenceLaw
    (backgroundLaw : FiniteDistribution (Background (rows := rows) slots upper))
    (hrows : 0 < rows (Nodes.height upper)) :
    FiniteDistribution (PairRecord (rows := rows) slots upper) :=
  (backgroundLaw.product (bucketLaw slots upper hrows)).pushforward (pairRecord slots upper)

end
end PerfectCompleteness.HierarchicalAgreementMean

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_HierarchicalUsefulCollision
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalUsefulCollision

noncomputable section

open scoped BigOperators Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n)

abbrev Direction := BucketSampler.Direction (rows (Nodes.height upper))
abbrev Tape := BucketSampler.Tape (rows (Nodes.height upper)) (NodeEmbedding.RowSpace slots upper)

attribute [local instance] OAI.PerfectCompleteness.HierarchicalUsefulCollision.backgroundFintype
attribute [local instance] OAI.PerfectCompleteness.HierarchicalUsefulCollision.rowSpaceFintype
local instance valueFintype_rd52179_1 :
    Fintype (Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :=
  Fintype.ofFinite _
def directionLaw (hrows : 0 < rows (Nodes.height upper)) :
    FiniteDistribution (Direction (rows := rows) upper) := by
  letI : Nonempty (Direction (rows := rows) upper) :=
    ⟨BucketUniform.coordinateDirection ⟨0, hrows⟩⟩
  exact FiniteDistribution.uniform _

def bucketLaw (ν : FiniteDistribution (NodeEmbedding.RowSpace slots upper))
    (hrows : 0 < rows (Nodes.height upper)) :
    FiniteDistribution (HierarchicalAgreementMean.BucketSample (rows := rows) slots upper) :=
  (directionLaw upper hrows).product
    ((BucketSampler.tapeLaw (rows (Nodes.height upper)) ν).product ν)

variable {P : Type*} [Fintype P]

abbrev Sample := (_ : P) × HierarchicalAgreementMean.BucketSample (rows := rows) slots upper

def law (externalLaw : FiniteDistribution P)
    (scalarLaw : P → FiniteDistribution (NodeEmbedding.RowSpace slots upper))
    (hrows : 0 < rows (Nodes.height upper)) :
    FiniteDistribution (Sample (P := P) (rows := rows) slots upper) :=
  CompletionSoundness.sigmaLaw externalLaw (fun p => bucketLaw slots upper (scalarLaw p) hrows)

def pairRecord (background : P → Background (rows := rows) slots upper)
    (sample : Sample (P := P) (rows := rows) slots upper) :
    HierarchicalAgreementMean.PairRecord (rows := rows) slots upper :=
  HierarchicalAgreementMean.pairRecord slots upper (background sample.1, sample.2)

def pairLaw (externalLaw : FiniteDistribution P)
    (background : P → Background (rows := rows) slots upper)
    (scalarLaw : P → FiniteDistribution (NodeEmbedding.RowSpace slots upper))
    (hrows : 0 < rows (Nodes.height upper)) :
    FiniteDistribution (HierarchicalAgreementMean.PairRecord (rows := rows) slots upper) :=
  (law slots upper externalLaw scalarLaw hrows).pushforward (pairRecord slots upper background)

end
end PerfectCompleteness.HierarchicalUsefulCollision

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HeterogeneousAdviceFamily
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HeterogeneousAdviceFamily

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters (F2)
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.RankLevelFilter
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness.ManyGoodRows

attribute [local instance] linearMapFintype

variable {P : Type*} [Fintype P] {E F Y : P → Type*}
  [∀ p, AddCommGroup (E p)] [∀ p, Module F2 (E p)]
  [∀ p, FiniteDimensional F2 (E p)] [∀ p, Fintype (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module F2 (F p)]
  [∀ p, FiniteDimensional F2 (F p)] [∀ p, Fintype (F p)]
  [∀ p, Fintype (Y p)]

abbrev Sample (r : Nat) := Σ p : P, RowMap (F p) r × (E p →ₗ[F2] F p)

def law (μ : FiniteDistribution P) (r : Nat) :
    FiniteDistribution (Sample (E := E) (F := F) r) :=
  CompletionSoundness.sigmaLaw μ (fun p => GoodAdviceEvents.law (E p) (F p) r)

def J (f : (p : P) → (E p →ₗ[F2] F p) → Option (Y p))
    (r : Nat) (ρ : ℝ) (sample : Sample (E := E) (F := F) r) : Bool :=
  GoodAdviceEvents.J (f sample.1) r ρ sample.2

def I (f : (p : P) → (E p →ₗ[F2] F p) → Option (Y p))
    (r : Nat) (ρ : ℝ) (sample : Sample (E := E) (F := F) r) : Bool :=
  GoodAdviceEvents.I (f sample.1) r ρ sample.2

end
end PerfectCompleteness.HeterogeneousAdviceFamily

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_OwnInputReferenceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
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

theorem Cut.upper_ne_lower (cut : Cut upper lower) : upper ≠ lower := by
  intro h
  have hlt := cut.proper
  rw [h] at hlt
  exact (Nat.lt_irrefl _) hlt

instance exteriorFinite : Finite (Exterior slots rows upper lower) := by
  let f : Exterior slots rows upper lower →
      OtherArrays slots rows upper lower ×
        (Fin (rows (Nodes.height lower)) → H (nodeSlots slots lower)) :=
    fun x => (x.otherArrays, x.lowerRows)
  exact Finite.of_injective f (by intro x y h; cases x; cases y; cases h; rfl)

instance exteriorFintype : Fintype (Exterior slots rows upper lower) := Fintype.ofFinite _

end
end PerfectCompleteness.OwnInputReference



namespace PerfectCompleteness.OwnInputCanonicalQuery

open scoped Classical
open TreeSourceSpaces HierarchicalArrays

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat) (upper lower : Nodes branch n)

abbrev CanonicalOutput (a : Block rows lower) :=
  DirectionQuotient.Space a ×
    (BlockQuotient.OtherBlocks (fun node : Nodes branch n => Block rows node) lower × PUnit.{1})

def canonicalQuery (a : Block rows lower) (arrays : Arrays slots rows) :=
  BlockQuotient.projectBlock lower a ∘ TreeCanonical.numberedFunction slots (fullJoint arrays)

end
end PerfectCompleteness.OwnInputCanonicalQuery

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalAdviceExperimentLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HierarchicalAdviceExperiment

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.RankLevelFilter

attribute [local instance] linearMapFintype

structure Experiment (branch rows : Nat → Nat) (n t : Nat) (Ω : Type*) [Fintype Ω] where
  slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot
  upper : Nodes branch n
  lowerLevel : Nat
  arrays : Ω → Arrays slots rows
  lowerNode : Ω → Nodes branch n
  separate : ∀ x, upper ≠ lowerNode x
  direction : ∀ x, Block rows (lowerNode x)
  original : FiniteDistribution Ω
  strategy : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t)

variable {branch rows : Nat → Nat} {n t : Nat} {Ω : Type*} [Fintype Ω]
  (S : Experiment branch rows n t Ω)

abbrev Background := HierarchicalMatrixTable.Background (rows := rows) S.slots S.upper

local instance backgroundFintype : Fintype (Background S) := Fintype.ofFinite _

abbrev Value := Block rows S.upper × HierarchicalMatrixTable.SideOutput (rows := rows) S.upper

local instance valueFintype : Fintype (Value S) := Fintype.ofFinite _

abbrev Advice (r : Nat) := ManyGoodRows.RowMap (Block rows S.upper) r

def matrix (x : Ω) : HierarchicalMatrixTable.Matrix (rows := rows) S.slots S.upper :=
  NodeEmbedding.matrix (S.arrays x) S.upper

def adviceLaw (r : Nat) : FiniteDistribution (Advice S r) :=
  FiniteDistribution.uniform _

def originalLaw (r : Nat) : FiniteDistribution (Ω × Advice S r) :=
  S.original.product (adviceLaw S r)

end
end PerfectCompleteness.HierarchicalAdviceExperiment


namespace PerfectCompleteness.HierarchicalAdviceFamily

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter
open UniqueGamesTheorem.Fourier.MatrixLevelBridge

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat} {O : Type*} [Fintype O]
  {Ω : O → Type*} [∀ o, Fintype (Ω o)]
  (S : (o : O) → HierarchicalAdviceExperiment.Experiment branch rows n t (Ω o))

abbrev Background := (o : O) × HierarchicalAdviceExperiment.Background (S o)

local instance backgroundFiberFintype (o : O) :
    Fintype (HierarchicalAdviceExperiment.Background (S o)) :=
  HierarchicalAdviceExperiment.backgroundFintype (S o)

abbrev Row (b : Background S) := Block rows (S b.1).upper
abbrev Value (b : Background S) := HierarchicalAdviceExperiment.Value (S b.1)

local instance valueFintype (b : Background S) : Fintype (Value S b) :=
  HierarchicalAdviceExperiment.valueFintype (S b.1)

abbrev OriginalSample (r : Nat) :=
  (o : O) × (Ω o × HierarchicalAdviceExperiment.Advice (S o) r)

def originalLaw (outer : FiniteDistribution O) (r : Nat) :
    FiniteDistribution (OriginalSample S r) :=
  CompletionSoundness.sigmaLaw outer (fun o => HierarchicalAdviceExperiment.originalLaw (S o) r)

def backgroundLaw (outer : FiniteDistribution O)
    (backgrounds : (o : O) → FiniteDistribution (HierarchicalAdviceExperiment.Background (S o))) :
    FiniteDistribution (Background S) :=
  CompletionSoundness.sigmaLaw outer backgrounds

end
end PerfectCompleteness.HierarchicalAdviceFamily


namespace PerfectCompleteness.HierarchicalUsefulFamily

noncomputable section

open scoped BigOperators Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch rows : Nat → Nat} {n t : Nat} {O : Type*} [Fintype O]
  {Ω : O → Type*} [∀ o, Fintype (Ω o)]
  (S : (o : O) → HierarchicalAdviceExperiment.Experiment branch rows n t (Ω o))

def originalLaw (outer : FiniteDistribution O) : FiniteDistribution (Sample Ω) :=
  CompletionSoundness.sigmaLaw outer (fun o => (S o).original)

end
end PerfectCompleteness.HierarchicalUsefulFamily

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_HierarchicalAdviceFromBuckets
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalAdviceFromBuckets

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.RankLevelFilter

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat} {Ω P : Type*}
  [Fintype Ω] [Fintype P]
  (S : HierarchicalAdviceExperiment.Experiment branch rows n t Ω)

local instance backgroundFintype : Fintype (HierarchicalAdviceExperiment.Background S) :=
  Fintype.ofFinite _

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace S.slots S.upper) :=
  Fintype.ofFinite _

def backgroundLaw (externalLaw : FiniteDistribution P)
    (background : P → HierarchicalAdviceExperiment.Background S) :
    FiniteDistribution (HierarchicalAdviceExperiment.Background S) :=
  externalLaw.pushforward background

def pairedLaw (externalLaw : FiniteDistribution P)
    (background : P → HierarchicalAdviceExperiment.Background S)
    (scalarLaw : P → FiniteDistribution (NodeEmbedding.RowSpace S.slots S.upper))
    (hrows : 0 < rows (Nodes.height S.upper)) :=
  HierarchicalUsefulCollision.pairLaw S.slots S.upper externalLaw background scalarLaw hrows

end
end PerfectCompleteness.HierarchicalAdviceFromBuckets

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_SourceGame
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceGame

open SourceClause UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

noncomputable section

def winCount {n m : Nat} (clauses : Fin m → NormalizedClause n)
    (strategy : Strategy (Fin m) (Fin n) (Fin 7) Bool) : Nat :=
  ∑ c, agreementCount (clauses c) (decodeLabel (clauses c).signs (strategy.1 c)) strategy.2

def violatedCount {n m : Nat} (clauses : Fin m → NormalizedClause n)
    (assignment : Fin n → Bool) : Nat :=
  ∑ c, if (clauses c).clause.eval assignment then 0 else 1

end
end PerfectCompleteness.SourceGame

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_WholeArraySampler
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexDecidableEq _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeArraySampler

open TreeSourceSpaces HierarchicalArrays DescendantSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def zeroTape (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) →
      (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) →
        Tape rows repeats p slots
  | _, _, .refl _, _ => fun _ _ => 0
  | _, _, .step i p, slots => fun k =>
      match k with
      | .inl _ => fun _ =>
          RecursiveSampler.zeroTape F2 repeats (.step i p) (LeafDomain slots)
      | .inr (.inl _) => zeroTape rows repeats p (childSlots slots i)
      | .inr (.inr _) => fun _ _ => 0

instance tapeNonempty (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    Nonempty (Tape rows repeats p slots) := ⟨zeroTape rows repeats p slots⟩

end

end PerfectCompleteness.WholeArraySampler

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_HierarchicalBucketFamily
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalBucketFamily

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat} {O : Type*} [Fintype O]
  {Ω : O → Type*} [∀ o, Fintype (Ω o)]
  (S : (o : O) → HierarchicalAdviceExperiment.Experiment branch rows n t (Ω o))

local instance backgroundFiberFintype (o : O) :
    Fintype (HierarchicalAdviceExperiment.Background (S o)) :=
  HierarchicalAdviceExperiment.backgroundFintype (S o)

local instance rowSpaceFintype (o : O) :
    Fintype (NodeEmbedding.RowSpace (S o).slots (S o).upper) := Fintype.ofFinite _

local instance valueFintype_rd52179_2 (b : HierarchicalAdviceFamily.Background S) :
    Fintype (HierarchicalAdviceFamily.Value S b) :=
  HierarchicalAdviceFamily.valueFintype S b
abbrev PairRecord :=
  (o : O) × HierarchicalAgreementMean.PairRecord (rows := rows) (S o).slots (S o).upper

def referencePairLaw (outer : FiniteDistribution O)
    (backgrounds : (o : O) → FiniteDistribution (HierarchicalAdviceExperiment.Background (S o)))
    (hrows : ∀ o, 0 < rows (Nodes.height (S o).upper)) :
    FiniteDistribution (PairRecord S) :=
  CompletionSoundness.sigmaLaw outer (fun o =>
    HierarchicalAgreementMean.referenceLaw (S o).slots (S o).upper (backgrounds o) (hrows o))

variable {P : O → Type*} [∀ o, Fintype (P o)]

def actualBackgrounds (externalLaw : (o : O) → FiniteDistribution (P o))
    (background : (o : O) → P o → HierarchicalAdviceExperiment.Background (S o))
    (o : O) : FiniteDistribution (HierarchicalAdviceExperiment.Background (S o)) :=
  HierarchicalAdviceFromBuckets.backgroundLaw (S o) (externalLaw o) (background o)

def actualPairLaw (outer : FiniteDistribution O)
    (externalLaw : (o : O) → FiniteDistribution (P o))
    (background : (o : O) → P o → HierarchicalAdviceExperiment.Background (S o))
    (scalarLaw : (o : O) → P o →
      FiniteDistribution (NodeEmbedding.RowSpace (S o).slots (S o).upper))
    (hrows : ∀ o, 0 < rows (Nodes.height (S o).upper)) :
    FiniteDistribution (PairRecord S) :=
  CompletionSoundness.sigmaLaw outer (fun o =>
    HierarchicalAdviceFromBuckets.pairedLaw (S o) (externalLaw o) (background o) (scalarLaw o) (hrows o))

end
end PerfectCompleteness.HierarchicalBucketFamily

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_OriginalChildScalars
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexDecidableEq _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype
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

def callComponent (calls : Nat) (repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (child : Fin (branch n)) : FiniteDistribution (Fin calls → Square slots child) :=
  FiniteProduct.law (fun _ : Fin calls => squareComponent repeats q slots chosen child)

end
end PerfectCompleteness.OriginalChildScalars

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OccurrenceStochasticLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.OccurrenceGame

open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {E Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype E] [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]

def stochasticSuccess (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (responses₁ : Q₁ → FiniteDistribution A₁)
    (responses₂ : Q₂ → FiniteDistribution A₂) : ℝ :=
  G.occurrences.expectation (fun e =>
    (responses₁ (G.left e)).expectation (fun a =>
      (responses₂ (G.right e)).expectation
        (fun b => if G.accepts e a b then 1 else 0)))

end
end PerfectCompleteness.OccurrenceGame



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_HierarchicalLeftDecoder
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty
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

variable (hbranch : ∀ k < n, 0 < branch k)

local instance rowSpaceFintype_rd52179_1 (node : Nodes branch n) :
    Fintype (NodeEmbedding.RowSpace slots node) := Fintype.ofFinite _
local instance nodeSpaceFintype_rd52179_1 (node : Nodes branch n) :
    Fintype (NodeEmbedding.NodeH slots node) := Fintype.ofFinite _
local instance upperDualFintype_rd52179_1 : Fintype (Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)
def lowerOne (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :
    squareSpace (NodeEmbedding.NodeH slots (LowerNode upper lowerLevel d)) :=
  ⟨1, TreeSourceSpaces.one_mem_squareSpace
    (nodeSlots slots (LowerNode upper lowerLevel d))
    (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk
      (Nodes.height_le (LowerNode upper lowerLevel d))))⟩

end
end PerfectCompleteness.HierarchicalLeftDecoder

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_RepetitionRateLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.IndexedRepetition

open UniqueGamesTheorem.Foundations.Games
open FiniteProduct

noncomputable section

variable {E Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype E] [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

def game (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) (I : Type*)
    [Fintype I] [DecidableEq I] :
    OccurrenceGame (I → E) (I → Q₁) (I → Q₂) (I → A₁) (I → A₂) := by
  classical
  exact
    { occurrences := law (fun _ : I => G.occurrences)
      left := fun x i => G.left (x i)
      right := fun x i => G.right (x i)
      accepts := fun x a b => decide (∀ i, G.accepts (x i) (a i) (b i) = true) }

def reindexStrategy {I J : Type*} (e : J ≃ I)
    (s : Strategy (I → Q₁) (I → Q₂) (I → A₁) (I → A₂)) :
    Strategy (J → Q₁) (J → Q₂) (J → A₁) (J → A₂) :=
  (fun x j => s.1 (x ∘ e.symm) (e j),
   fun y j => s.2 (y ∘ e.symm) (e j))

end
end PerfectCompleteness.IndexedRepetition

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_MultiplicationFormInjectiveLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SparseReplacement

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

def row (P Q : (i : I) → FiniteDistribution (Ω i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (i : I) :
    FiniteDistribution (Ω i) :=
  (ProjectionPosterior.bernoulli β hβ hβ').mixture
    (fun marked => if marked then Q i else P i)

def law (P Q : (i : I) → FiniteDistribution (Ω i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution ((i : I) → Ω i) :=
  FiniteProduct.law (row P Q β hβ hβ')

def markedLaw (P Q : (i : I) → FiniteDistribution (Ω i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution ((I → Bool) × ((i : I) → Ω i)) :=
  CleanConditioning.kernelJoint
    (FiniteProduct.law fun _ : I => ProjectionPosterior.bernoulli β hβ hβ')
    (fun mask => FiniteProduct.law fun i => if mask i then Q i else P i)


end
end PerfectCompleteness.SparseReplacement


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_HierarchicalAllDecoderTables
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty
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

local instance rowSpaceFintype (node : Nodes branch n) :
    Fintype (NodeEmbedding.RowSpace slots node) := Fintype.ofFinite _

end
end PerfectCompleteness.HierarchicalAllDecoderTables

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_OddListGame
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OddListGame

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open OddLists FiniteListSampling

noncomputable section

variable {E Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype E] [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] [DecidableEq A₁] [DecidableEq A₂]

def base (μ : FiniteDistribution E) (left : E → Q₁) (right : E → Q₂)
    (projection : E → A₁ → A₂) : OccurrenceGame E Q₁ Q₂ A₁ A₂ :=
  OccurrenceGame.ofProjection μ left right projection

def game (s : Nat) (μ : FiniteDistribution E) (left : E → Q₁) (right : E → Q₂)
    (projection : E → A₁ → A₂) :
    OccurrenceGame E Q₁ Q₂ (OddList s A₁) (OddList s A₂) :=
  OccurrenceGame.ofProjection μ left right (fun e => OddList.map (projection e))

def responses {Q A : Type*} [Fintype A] [DecidableEq A] {s : Nat}
    (lists : Q → OddList s A) (q : Q) : FiniteDistribution A :=
  uniformList (lists q).val (lists q).nonempty

end
end PerfectCompleteness.OddListGame

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_SourceAmplification
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceAmplification

open SourceClause UniqueGamesTheorem.Foundations Games
open UniqueGamesTheorem.Integration

def ClauseGap {n m : Nat} (clauses : Fin m → NormalizedClause n) (γ : ℚ) : Prop :=
  ∀ assignment : Fin n → Bool,
    γ * (m : ℚ) ≤ (SourceGame.violatedCount clauses assignment : ℚ)

end PerfectCompleteness.SourceAmplification

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceOddListsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceOddLists

open SourceClause OddLists
open UniqueGamesTheorem.Foundations.Games

noncomputable section

def projection {n m t : Nat} (clauses : Fin m → NormalizedClause n)
    (e : Occurrences m t) (a : LeftLabels t) : RightLabels t :=
  fun i => SourceGame.projection clauses (e i) (a i)

end
end PerfectCompleteness.SourceOddLists



namespace PerfectCompleteness.SourceAnswerEquiv

open SourceClause

variable {v m t : Nat}

instance rightDomainDecidableEq (clauses : Fin m → NormalizedClause v)
    (question : Fin t → Fin v) : DecidableEq (RightDomain clauses question) :=
  inferInstanceAs (DecidableEq (Fin t → Bool))


end PerfectCompleteness.SourceAnswerEquiv

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_OwnLawHeavyList
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OwnLawHeavyList

open QuarterBalance
open UniqueGamesTheorem.Foundations.Games
open scoped TensorProduct Classical

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module F2 V] [Fintype V]

attribute [local instance] OAI.PerfectCompleteness.OwnLawHeavyList.dualFintype
def heavyList (μ : FiniteDistribution V) (target : V → ℝ) (threshold : ℝ) :
    Finset (Module.Dual F2 V) :=
  SmallBias.heavySet μ character target threshold

universe u

end
end PerfectCompleteness.OwnLawHeavyList

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_OwnInputHeavyBounds
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OwnInputHeavyBounds

open scoped TensorProduct Classical
open TreeSourceSpaces HierarchicalArrays OwnInputReference

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat) (upper lower : Nodes branch n)
  (W : Submodule F2 (UpperVector rows upper))

local instance upperSpaceFintype : Fintype (UpperSpace slots upper) :=
  Fintype.ofFinite _

end

end PerfectCompleteness.OwnInputHeavyBounds

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_RightDecoderWitness
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.RightDecoderWitness

open scoped TensorProduct Classical
open UniqueGamesTheorem.Foundations.Games
open TensorCosetEvaluation
open TreeSourceSpaces HierarchicalArrays OwnInputReference

noncomputable section

variable {branch : Nat → Nat}
  {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat)
  (upper lower : Nodes branch n)
  (W : Submodule F2 (UpperVector rows upper))
  (a : LowerVector rows lower)
  (repeats : Nat → Nat)
  (cut : Cut upper lower)
  (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

local instance upperSpaceFintype : Fintype (UpperSpace slots upper) := Fintype.ofFinite _

end
end PerfectCompleteness.RightDecoderWitness

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PoweringTableSemanticsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTables.graph_ofGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTables.graph_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTables.lookup_ofGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTableLayout.vertexRows_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_new _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_old _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs.square_next _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs.square_rot_apply _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs.zigzag_rot_apply
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

abbrev EncodedLabeling (vertices d n : Nat) :=
  Fin vertices → Fin (labelCount d n)

def encodeLabeling {vertices : Nat} (d n : Nat) (labels : RawLabeling vertices d n) :
    EncodedLabeling vertices d n :=
  fun v => encodeLabel d (n + 1) 64 (labels v)

def decodeLabeling {vertices : Nat} (d n : Nat) (labels : EncodedLabeling vertices d n) :
    RawLabeling vertices d n :=
  fun v => decodeLabel d (n + 1) 64 (labels v)

@[simp] theorem decodeLabeling_encodeLabeling {vertices : Nat} (d n : Nat)
    (labels : RawLabeling vertices d n) :
    decodeLabeling d n (encodeLabeling d n labels) = labels := by
  funext v
  exact decodeLabel_encodeLabel d (n + 1) 64 (labels v)

@[simp] theorem encodeLabeling_decodeLabeling {vertices : Nat} (d n : Nat)
    (labels : EncodedLabeling vertices d n) :
    encodeLabeling d n (decodeLabeling d n labels) = labels := by
  funext v
  exact encodeLabel_decodeLabel d (n + 1) 64 (labels v)

/-- The denominator equality comes from the same explicit dart bijection. -/
theorem card_darts_eq_table {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) :
    Fintype.card (PoweringTest.Dart (Fin vertices) (Fin d) n) = (table input n).darts := by
  change Fintype.card (PoweringTest.Dart (Fin vertices) (Fin d) n) =
    2 * vertices * d ^ (n + 1)
  simpa only [Fintype.card_fin] using Fintype.card_congr (dartEquiv vertices d n)

end UniqueGamesTheorem.Foundations.PCP.PoweringTableSemantics

/-!
# The actual first moment of an endpoint-opinion witness

The pivot factorization is applied to actual finite walks. Its two endpoint
operator bounds are obtained from the proved lazy-graph mixture and smoothing
theorem. No witness-event probability law is assumed.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringWitness

open PoweringWalks SpectralReturn PoweringReturn PoweringLazy
open PoweringMoment (bit)

variable {V D : Type*}

/-- A constant scalar passes through every iterate of the actual graph mean. -/
theorem iterate_mul_const [Fintype D] (G : PortGraph V D)
    (n : Nat) (c : ℝ) (h : V → ℝ) :
    iterateOperator G n (fun x => c * h x) =
      fun x => c * iterateOperator G n h x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change averagingOperator G (iterateOperator G n (fun x => c * h x)) =
      fun x => c * averagingOperator G (iterateOperator G n h) x
    rw [ih]
    funext v
    exact mean_mul_left c (fun d => iterateOperator G n h (G.rot (v, d)).1)

/-- The actual pivot dart is marked and both endpoint opinions pass their
tests. For indicator opinions this is the indicator of their conjunction. -/
noncomputable def endpointWitness (G : PortGraph V D) (bad : Edge V D → Bool)
    (φ ψ : Edge V D → V → ℝ) (n : Nat) (k : Fin (n + 1))
    (w : Walk V D (n + 1)) : ℝ :=
  bit (bad (edgeAt G n w k) = true) *
    φ (edgeAt G n w k) w.1 * ψ (edgeAt G n w k) (endpoint G w)

/-- Vertex-indexed opinions are tested at the two endpoints of the pivot dart. -/
noncomputable def vertexWitness (G : PortGraph V D) (bad : Edge V D → Bool)
    (f : V → V → ℝ) (n : Nat) (k : Fin (n + 1)) :
    Walk V D (n + 1) → ℝ :=
  endpointWitness G bad (fun e => f e.1) (fun e => f (next G e.1 e.2)) n k

/-- Pointwise bounds on the two genuine earlier-length graph iterates give
the witness first moment. The hypotheses are only needed on marked darts. -/
theorem endpoint_lower_bound [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (n : Nat) (k : Fin (n + 1)) (bad : Edge V D → Bool)
    (φ ψ : Edge V D → V → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hL : ∀ e, bad e = true → a ≤ iterateOperator G k.val (φ e) e.1)
    (hR : ∀ e, bad e = true →
      a ≤ iterateOperator G (n - k.val) (ψ e) (next G e.1 e.2)) :
    edgeDensity bad * a ^ 2 ≤ mean (endpointWitness G bad φ ψ n k) := by
  have hfactor : mean (endpointWitness G bad φ ψ n k) =
      mean (fun e : Edge V D =>
        (bit (bad e = true) * iterateOperator G k.val (φ e) e.1) *
          iterateOperator G (n - k.val) (ψ e) (next G e.1 e.2)) := by
    unfold endpointWitness
    rw [mean_edge_endpoints G n k (fun e x => bit (bad e = true) * φ e x) ψ]
    simp_rw [iterate_mul_const]
  have hbitMean : mean (fun e : Edge V D => bit (bad e = true)) = edgeDensity bad := by
    calc
      _ = mean (fun v : V => mean (fun d : D => bit (bad (v, d) = true))) :=
        mean_prod (A := V) (B := D) (fun e => bit (bad e = true))
      _ = edgeDensity bad := by simp only [mean_edge_bit, edgeDensity]
  calc
    edgeDensity bad * a ^ 2 =
        mean (fun e : Edge V D => bit (bad e = true) * a ^ 2) := by
      rw [mean_mul_right, hbitMean]
    _ ≤ mean (fun e : Edge V D =>
        (bit (bad e = true) * iterateOperator G k.val (φ e) e.1) *
          iterateOperator G (n - k.val) (ψ e) (next G e.1 e.2)) := by
      apply mean_mono
      intro e
      cases hb : bad e with
      | false => simp [bit]
      | true =>
        have hprod := mul_le_mul (hL e hb) (hR e hb) ha (ha.trans (hL e hb))
        simpa [bit, hb, pow_two] using hprod
    _ = mean (endpointWitness G bad φ ψ n k) := hfactor.symm

/-- The two endpoint-opinion tests each retain probability at least `1/(2q)`
at every middle pivot. The walk has `2N+1` edges, with `N=(4qM)^2`, so the
prefix and suffix lengths are exactly `k` and `2N-k`.

The only modal input is the actual centered lazy iterate at each vertex. It
will be supplied by the finite modal-opinion decoder, not by a witness law.
-/
theorem lazy_middle_witness_mean [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (q M : Nat) (hq : 1 ≤ q) (hM : 1 ≤ M)
    (k : Fin (2 * (4 * q * M) ^ 2 + 1))
    (hlo : (4 * q * M) ^ 2 - M ≤ k.val)
    (hhi : k.val ≤ (4 * q * M) ^ 2 + M)
    (bad : Edge V (Bool × D) → Bool) (f : V → V → ℝ)
    (hf : ∀ u w, f u w ∈ Set.Icc (0 : ℝ) 1)
    (hmodal : ∀ u, 1 / (q : ℝ) ≤
      iterateOperator (lazyGraph G) ((4 * q * M) ^ 2) (f u) u) :
    edgeDensity bad / (4 * (q : ℝ) ^ 2) ≤
      mean (vertexWitness (lazyGraph G) bad f (2 * (4 * q * M) ^ 2) k) := by
  have hk : k.val ≤ 2 * (4 * q * M) ^ 2 := Nat.le_of_lt_succ k.isLt
  have hslo : (4 * q * M) ^ 2 - M ≤ 2 * (4 * q * M) ^ 2 - k.val := by omega
  have hshi : 2 * (4 * q * M) ^ 2 - k.val ≤ (4 * q * M) ^ 2 + M := by omega
  have ha : (0 : ℝ) ≤ 1 / (2 * (q : ℝ)) := by positivity
  have hbound := endpoint_lower_bound (lazyGraph G) (2 * (4 * q * M) ^ 2) k bad
    (fun e => f e.1) (fun e => f (next (lazyGraph G) e.1 e.2))
    (1 / (2 * (q : ℝ))) ha
    (by
      intro e _
      exact lazy_endpoint_modal_transfer G q M k.val hq hM hlo hhi
        (f e.1) (hf e.1) e.1 (hmodal e.1))
    (by
      intro e _
      exact lazy_endpoint_modal_transfer G q M (2 * (4 * q * M) ^ 2 - k.val)
        hq hM hslo hshi (f (next (lazyGraph G) e.1 e.2))
        (hf (next (lazyGraph G) e.1 e.2)) (next (lazyGraph G) e.1 e.2)
        (hmodal (next (lazyGraph G) e.1 e.2)))
  have hscale : edgeDensity bad * (1 / (2 * (q : ℝ))) ^ 2 =
      edgeDensity bad / (4 * (q : ℝ) ^ 2) := by ring
  simpa only [vertexWitness, hscale] using hbound

end UniqueGamesTheorem.Foundations.PCP.PoweringWitness

/-! The actual graph-powering soundness bound. Modal endpoint opinions give
the first moment, spectral return gives the second moment, and an actual
checked path constraint turns each witness into rejection. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringSoundness

open scoped BigOperators
open PoweringWalks PoweringLabels PoweringOpinions PoweringTest
open SpectralReturn PoweringWitness PoweringMomentBound
open PoweringMoment (bit hits)

variable {V D A : Type*}

variable [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
  [Fintype A] [Nonempty A]

def decodedError (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n N : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A) : ℝ :=
  edgeDensity (decodedBad G accepts (decoded G (n + 1) N selectors labels fallback))

def poweredRejection (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) : ℝ :=
  mean (fun d : Dart V D n => bit ((poweredGraph G accepts n selectors).edgeSatisfied labels d = false))

omit [Fintype V] [Nonempty V] [Nonempty D] in
theorem witness_bit_eq (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n N : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A)
    (w : Walk V D (n + 1)) (k : Fin (n + 1)) :
    bit (witness G accepts n selectors labels fallback
      (decoded G (n + 1) N selectors labels fallback) w k) =
      vertexWitness G
        (decodedBad G accepts (decoded G (n + 1) N selectors labels fallback))
        (matchFn G (n + 1) N selectors labels fallback) n k w := by
  simp only [witness, vertexWitness, endpointWitness, matchFn,
    PoweringMoment.bit_mul, next, and_assoc]

omit [Nonempty V] in
theorem modal_witness_mean (G : PortGraph V D) (M : Nat) (hM : 1 ≤ M)
    (accepts : Edge V (Bool × D) → A → A → Bool)
    (selectors : ∀ v, AddressSelector (lazyGraph G) (2 * center (Fintype.card A) M + 1) v)
    (labels : V → PaddedLabel (Bool × D) (2 * center (Fintype.card A) M + 1) A)
    (fallback : A) (k : Fin (2 * center (Fintype.card A) M + 1))
    (hlo : center (Fintype.card A) M - M ≤ k.val)
    (hhi : k.val ≤ center (Fintype.card A) M + M) :
    decodedError (lazyGraph G) accepts (2 * center (Fintype.card A) M)
      (center (Fintype.card A) M) selectors labels fallback / (4 * (Fintype.card A : ℝ) ^ 2) ≤
      mean (fun w => bit (witness (lazyGraph G) accepts (2 * center (Fintype.card A) M)
        selectors labels fallback (decoded (lazyGraph G) (2 * center (Fintype.card A) M + 1)
          (center (Fintype.card A) M) selectors labels fallback) w k)) := by
  have h := lazy_middle_witness_mean G (Fintype.card A) M Fintype.card_pos hM k hlo hhi
    (decodedBad (lazyGraph G) accepts
      (decoded (lazyGraph G) (2 * center (Fintype.card A) M + 1)
        (center (Fintype.card A) M) selectors labels fallback))
    (matchFn (lazyGraph G) (2 * center (Fintype.card A) M + 1)
      (center (Fintype.card A) M) selectors labels fallback)
    (matchFn_mem_Icc (lazyGraph G) (2 * center (Fintype.card A) M + 1)
      (center (Fintype.card A) M) selectors labels fallback)
    (decoded_modal_baseline (lazyGraph G) (2 * center (Fintype.card A) M + 1)
      (center (Fintype.card A) M) selectors labels fallback)
  simp_rw [witness_bit_eq]
  convert h using 1 <;> rfl

/-- Positive decoded error forces rejection of the actual powered graph.
The cap and amplification coefficient are explicit constants. -/
theorem rejection_lower_bound (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate (lazyGraph G) lambda)
    (accepts : Edge V (Bool × D) → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts ((lazyGraph G).rot e) b a = accepts e a b)
    (M : Nat) (hM : 1 ≤ M)
    (selectors : ∀ v, AddressSelector (lazyGraph G) (2 * center (Fintype.card A) M + 1) v)
    (labels : V → PaddedLabel (Bool × D) (2 * center (Fintype.card A) M + 1) A)
    (fallback : A)
    (hε : 0 < decodedError (lazyGraph G) accepts (2 * center (Fintype.card A) M)
      (center (Fintype.card A) M) selectors labels fallback) :
    gain (Fintype.card A) M lambda *
        min (decodedError (lazyGraph G) accepts (2 * center (Fintype.card A) M)
          (center (Fintype.card A) M) selectors labels fallback)
          (1 / ((2 * center (Fintype.card A) M + 1 : Nat) : ℝ)) ≤
      poweredRejection (lazyGraph G) accepts (2 * center (Fintype.card A) M) selectors labels := by
  let q := Fintype.card A
  let N := center q M
  let n := 2 * N
  let m := 2 * M + 1
  let start := N - M
  let L := lazyGraph G
  let assignment := decoded L (n + 1) N selectors labels fallback
  let bad := decodedBad L accepts assignment
  let ε := edgeDensity bad
  let α : ℝ := 1 / (2 * (q : ℝ))
  let C : ℝ := 1 + 2 / (1 - lambda)
  have hNM : M ≤ N := le_center q M Fintype.card_pos hM
  have hw : start + m ≤ n + 1 := by dsimp [start, m, n]; omega
  let E := windowEvent L bad n start m hw
  let W : Fin m → Walk V (Bool × D) (n + 1) → Prop := fun i w =>
    witness L accepts n selectors labels fallback assignment w (windowIndex n start m hw i)
  let R : Walk V (Bool × D) (n + 1) → Prop := fun w =>
    pathAccepts L accepts n selectors w (labels w.1) (labels (endpoint L w)) = false
  have hWE : ∀ i w, W i w → E i w := by
    intro i w h
    exact h.1
  have hWR : ∀ i w, W i w → R w := by
    intro i w h
    exact witness_implies_path_rejection L accepts n selectors labels fallback assignment w
      (windowIndex n start m hw i) h
  have hpoint (i : Fin m) : ε / (4 * (q : ℝ) ^ 2) ≤ mean (fun w => bit (W i w)) := by
    have hlo : N - M ≤ (windowIndex n start m hw i).val := by
      dsimp [windowIndex, start]
      omega
    have hhi : (windowIndex n start m hw i).val ≤ N + M := by
      have hi := i.isLt
      dsimp [windowIndex, start]
      dsimp [m] at hi
      omega
    exact modal_witness_mean G M hM accepts selectors labels fallback
      (windowIndex n start m hw i) hlo hhi
  have hfirst : α ^ 2 * (m : ℝ) * ε ≤ mean (hits W) := by
    change α ^ 2 * (m : ℝ) * ε ≤ PoweringMoment.mean (hits W)
    rw [PoweringMoment.mean_hits]
    calc
      _ = ∑ _i : Fin m, ε / (4 * (q : ℝ) ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        dsimp [α]
        ring
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hpoint i)
  have hsecond : mean (fun w => hits E w ^ 2) ≤
      (m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε) :=
    window_second_moment_le L lambda certificate bad
      (decodedBad_rot L accepts reverse_accepts assignment) n start m hw
  have hε' : 0 < ε := hε
  have hm : 0 < m := by dsimp [m]; omega
  have hmReal : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hqReal : (0 : ℝ) < q := Nat.cast_pos.mpr Fintype.card_pos
  have hden : 0 < 1 - lambda := sub_pos.mpr certificate.lt_one
  have hC : 0 < C := by dsimp [C] <;> positivity
  have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hα : 0 < α := by dsimp [α] <;> positivity
  have ha : 0 < α ^ 2 * (m : ℝ) * ε := by positivity
  have hb : 0 < (m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε) := by
    have hdiff : 0 ≤ (m : ℝ) - 1 := sub_nonneg.mpr hmOne
    positivity
  have hCS := PoweringMoment.rejection_lower_bound E W R hWE hWR
    (α ^ 2 * (m : ℝ) * ε) ((m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε))
    ha hb hfirst hsecond
  have ht : (0 : ℝ) < ((n + 1 : Nat) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have hmn : m ≤ n + 1 := by dsimp [m, n]; omega
  have hmt : (m : ℝ) - 1 ≤ ((n + 1 : Nat) : ℝ) := by
    have hmnReal : (m : ℝ) ≤ ((n + 1 : Nat) : ℝ) := by exact_mod_cast hmn
    linarith
  have hratio := PoweringNumeric.count_moment_ratio_lower α ε C ((n + 1 : Nat) : ℝ)
    m hm hε' hC ht hmt
  change (α ^ 4 * (m : ℝ) / (C + 1)) * min ε (1 / ((n + 1 : Nat) : ℝ)) ≤ _
  change _ ≤ mean (fun d : Dart V (Bool × D) n =>
    bit ((poweredGraph L accepts n selectors).edgeSatisfied labels d = false))
  rw [rejection_mean_eq_path_mean]
  exact hratio.trans hCS

end UniqueGamesTheorem.Foundations.PCP.PoweringSoundness

namespace UniqueGamesTheorem.Foundations.PCP.PoweringGap

open PoweringWalks PoweringLabels PoweringOpinions PoweringTest
open SpectralReturn PoweringSoundness PoweringCounting

variable {V D A : Type*}

variable [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
  [Fintype A] [Nonempty A]

theorem uniform_count_gap (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate (lazyGraph G) lambda)
    (accepts : Edge V (Bool × D) → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts ((lazyGraph G).rot e) b a = accepts e a b)
    (M : Nat) (hM : 1 ≤ M)
    (selectors : ∀ v, AddressSelector (lazyGraph G)
      (2 * center (Fintype.card A) M + 1) v)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hgap : ∀ assignment : V → A,
      epsilon * (Fintype.card (Edge V (Bool × D)) : ℝ) ≤
        ((baseGraph (lazyGraph G) accepts reverse_accepts).rejectionCount assignment : ℝ))
    (labels : V → PaddedLabel (Bool × D) (2 * center (Fintype.card A) M + 1) A) :
    (gain (Fintype.card A) M lambda *
      min epsilon (1 / ((2 * center (Fintype.card A) M + 1 : Nat) : ℝ))) *
        (Fintype.card (Dart V (Bool × D) (2 * center (Fintype.card A) M)) : ℝ) ≤
      ((poweredGraph (lazyGraph G) accepts (2 * center (Fintype.card A) M)
        selectors).rejectionCount labels : ℝ) := by
  classical
  let L := lazyGraph G
  let N := center (Fintype.card A) M
  let n := 2 * N
  let H := poweredGraph L accepts n selectors
  change (gain (Fintype.card A) M lambda *
      min epsilon (1 / ((n + 1 : Nat) : ℝ))) *
        (Fintype.card (Dart V (Bool × D) n) : ℝ) ≤
      (H.rejectionCount labels : ℝ)
  rcases eq_or_lt_of_le hepsilon with hzero | hpositive
  · rw [← hzero]
    have hcap : (0 : ℝ) ≤ 1 / ((n + 1 : Nat) : ℝ) := by positivity
    rw [min_eq_left hcap, mul_zero, zero_mul]
    exact Nat.cast_nonneg _
  · let fallback : A := Classical.choice (inferInstance : Nonempty A)
    let assignment := decoded L (n + 1) N selectors labels fallback
    have hdecoded : epsilon ≤ decodedError L accepts n N selectors labels fallback := by
      change epsilon ≤ edgeDensity (decodedBad L accepts assignment)
      exact base_count_lower_to_density L accepts reverse_accepts assignment
        Fintype.card_pos epsilon (hgap assignment)
    have herror : 0 < decodedError L accepts n N selectors labels fallback :=
      hpositive.trans_le hdecoded
    have hsound := PoweringSoundness.rejection_lower_bound G lambda certificate
      accepts reverse_accepts M hM selectors labels fallback herror
    have hgain : 0 ≤ gain (Fintype.card A) M lambda :=
      gain_nonneg (Fintype.card A) M lambda certificate.lt_one
    have hmin : min epsilon (1 / ((n + 1 : Nat) : ℝ)) ≤
        min (decodedError L accepts n N selectors labels fallback)
          (1 / ((n + 1 : Nat) : ℝ)) :=
      min_le_min hdecoded (le_refl _)
    have hlower : gain (Fintype.card A) M lambda *
        min epsilon (1 / ((n + 1 : Nat) : ℝ)) ≤
        poweredRejection L accepts n selectors labels :=
      (mul_le_mul_of_nonneg_left hmin hgain).trans hsound
    exact (constraint_rejection_lower_iff H labels Fintype.card_pos
      (gain (Fintype.card A) M lambda *
        min epsilon (1 / ((n + 1 : Nat) : ℝ)))).mp hlower

end UniqueGamesTheorem.Foundations.PCP.PoweringGap

/-! Actual directed-cut expansion from the graph's zero-mean spectral
certificate. Parallel edges and loops retain their indexed port multiplicities. -/
namespace UniqueGamesTheorem.Foundations.PCP.SpectralCut

open scoped BigOperators
open PoweringWalks SpectralReturn

variable {V D : Type*} [Fintype V] [Fintype D] [DecidableEq V]

def cut (G : PortGraph V D) (S : Finset V) : Finset (V × D) :=
  Finset.univ.filter (fun e => e.1 ∈ S ∧ (G.rot e).1 ∉ S)

section Nonempty
variable [Nonempty V] [Nonempty D] (G : PortGraph V D)

omit [Nonempty V] in
/-- The normalized cut count is exactly mean minus one-step correlation. -/
theorem cut_density_eq (S : Finset V) :
    ((cut G S).card : ℝ) / (Fintype.card (V × D) : ℝ) =
      mean (indicator S) - correlation (indicator S) (averagingOperator G (indicator S)) := by
  classical
  calc
    _ = mean (indicator (cut G S)) := (mean_indicator (cut G S)).symm
    _ = mean (fun e : V × D => indicator S e.1 -
        indicator S e.1 * indicator S (G.rot e).1) := by
      congr 1
      funext e
      by_cases hv : e.1 ∈ S <;> by_cases hw : (G.rot e).1 ∈ S <;>
        simp [indicator, cut, hv, hw]
    _ = mean (fun v => mean (fun d : D => indicator S v -
        indicator S v * indicator S (G.rot (v,d)).1)) := mean_prod _
    _ = mean (fun v => indicator S v -
        indicator S v * averagingOperator G (indicator S) v) := by
      congr 1
      funext v
      rw [mean_sub, mean_const, mean_mul_left]
      rfl
    _ = _ := mean_sub _ _

theorem cut_density_ge_variance
    (certificate : SpectralCertificate G (1/2)) (S : Finset V) :
    (1/2:ℝ) * mean (indicator S) * (1 - mean (indicator S)) ≤
      ((cut G S).card : ℝ) / (Fintype.card (V × D) : ℝ) := by
  let f := indicator S
  have hz : mean (fun v => f v - mean f) = 0 := by
    rw [mean_sub, mean_const, sub_self]
  have he : energy (fun v => f v - mean f) = mean f - mean f ^ 2 := by
    rw [energy_sub_const, energy_indicator]
    ring
  have hb := zero_mean_correlation_bound G (1/2) certificate
    (fun v => f v - mean f) hz 1
  have hc := correlation_centered G f 1
  simp only [iterateOperator, pow_one, he] at hb hc
  rw [cut_density_eq]
  change (1/2:ℝ) * mean f * (1 - mean f) ≤
    mean f - correlation f (averagingOperator G f)
  nlinarith

theorem cut_density_ge_quarter
    (certificate : SpectralCertificate G (1/2)) (S : Finset V)
    (hsmall : 2 * S.card ≤ Fintype.card V) :
    mean (indicator S) / 4 ≤
      ((cut G S).card : ℝ) / (Fintype.card (V × D) : ℝ) := by
  have hN : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hp0 : 0 ≤ mean (indicator S) := mean_nonnegative _ (indicator_nonnegative S)
  have hp : mean (indicator S) ≤ (1/2:ℝ) := by
    rw [mean_indicator]
    apply (div_le_iff₀ hN).mpr
    have hs : (2:ℝ) * (S.card : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hsmall
    nlinarith
  have hv := cut_density_ge_variance G certificate S
  have hprod := mul_nonneg hp0 (sub_nonneg.mpr hp)
  nlinarith

/-- The real cardinal estimate before removing denominators. -/
theorem cut_card_ge_quarter_degree
    (certificate : SpectralCertificate G (1/2)) (S : Finset V)
    (hsmall : 2 * S.card ≤ Fintype.card V) :
    (Fintype.card D : ℝ) * (S.card : ℝ) / 4 ≤ ((cut G S).card : ℝ) := by
  have hN : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hD : (0:ℝ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  have h := cut_density_ge_quarter G certificate S hsmall
  rw [Fintype.card_prod, Nat.cast_mul] at h
  have hh := (le_div_iff₀ (mul_pos hN hD)).mp h
  have he : mean (indicator S) / 4 *
      ((Fintype.card V : ℝ) * (Fintype.card D : ℝ)) =
        (Fintype.card D : ℝ) * (S.card : ℝ) / 4 := by
    rw [mean_indicator]
    field_simp [ne_of_gt hN]
  rw [he] at hh
  exact hh

theorem degree_mul_card_le_four_cut
    (certificate : SpectralCertificate G (1/2)) (S : Finset V)
    (hsmall : 2 * S.card ≤ Fintype.card V) :
    Fintype.card D * S.card ≤ 4 * (cut G S).card := by
  have h := cut_card_ge_quarter_degree G certificate S hsmall
  have hr : (Fintype.card D : ℝ) * (S.card : ℝ) ≤ 4 * ((cut G S).card : ℝ) := by
    linarith
  exact_mod_cast hr

end Nonempty

/-- The natural-number expansion used in cloud rounding. Empty vertex sets
are included; a degree of at least eight supplies the nonempty port type. -/
theorem cut_card_ge_twice (G : PortGraph V D)
    (certificate : SpectralCertificate G (1/2)) (hdegree : 8 ≤ Fintype.card D)
    (S : Finset V) (hsmall : 2 * S.card ≤ Fintype.card V) :
    2 * S.card ≤ (cut G S).card := by
  let : Nonempty D := Fintype.card_pos_iff.mp (by omega)
  rcases isEmpty_or_nonempty V with hV | hV
  · let := hV
    have hzero : Fintype.card V = 0 := Fintype.card_eq_zero
    have hs : S.card = 0 := by omega
    simp only [hs, mul_zero, Nat.zero_le]
  · let := hV
    have h := degree_mul_card_le_four_cut G certificate S hsmall
    have hdeg := Nat.mul_le_mul_right S.card hdegree
    omega

end UniqueGamesTheorem.Foundations.PCP.SpectralCut

/-!
# Uniform restriction of Boolean tapes

Restricting a uniformly sampled Boolean function to a decidable subset gives
the uniform law on functions on that subset.  The subset and its complement
may be empty: their Boolean function spaces still contain the constant-false
function.  Extending by false gives a canonical full-domain oracle address.
-/

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_AlphabetGraphLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Relations.repeatedConsistentDecidable _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_headValue _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_head _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_tail _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.EmptyContext.equation_second_eq_third _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.EmptyContext.pairedEquations_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHonest.taggedAssignment_left _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHonest.taggedAssignment_right _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.canonicalInput_half _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.extendRestricted_valid _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.restrictQuery_extendRestricted _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Queries.mask_idempotent _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Relations.relationAt_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.rows_at _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Preprocessing.graph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.cloudRank_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_oldCloudIndex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.accepts_materialize _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.accepts_pad _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.baseGraph_pad _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_new _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_old _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.rotation_pad _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Regularization.graph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_reverse_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_reverse_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.paddedG_tail
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

theorem local_gap (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) (e : E) :
    AssignmentTester.truth (!(G.edgeSatisfied (decodedLabeling assignment) e)) / 2048 ≤
      localAverage G assignment e := by
  cases h : G.edgeSatisfied (decodedLabeling assignment) e with
  | false =>
      rw [localAverage_eq_tester]
      simpa [AssignmentTester.truth] using
        AlphabetReduction.rejected_edge_tester_bound (G.accepts e)
          (vertexBlock assignment (G.tail e)) (vertexBlock assignment (G.head e))
          (edgeOracle G assignment e) h
  | true =>
      simp only [Bool.not_true, AssignmentTester.truth, Bool.false_eq_true, ite_false, if_false, zero_div]
      apply Finset.expect_nonneg
      intro sample _
      exact AssignmentTester.truth_nonneg _

theorem average_gap [Fintype E] (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) :
    (𝔼 e : E, AssignmentTester.truth (!(G.edgeSatisfied (decodedLabeling assignment) e))) / 2048 ≤
      average G assignment := by
  unfold average
  rw [expect_prod, Finset.expect_div]
  exact Finset.expect_le_expect (fun e _ => local_gap G assignment e)

/-- The actual event count has a uniform loss of 2048, with no edge-dependent
sample multiplicities. This count statement also permits an empty dart type. -/
theorem rejection_count_bound [Fintype E] (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) :
    Fintype.card (LocalEvent A) * G.rejectionCount (decodedLabeling assignment) ≤
      2048 * QueryIncidence.verifierRejectionCount (verifier G) assignment := by
  classical
  cases isEmpty_or_nonempty E with
  | inl empty =>
      let := empty
      simp [ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts]
  | inr inhabited =>
      let := inhabited
      have h := average_gap G assignment
      rw [average_eq_count, expect_rejection_eq_count, card_event, Nat.cast_mul,
        div_div] at h
      have he : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
      have hl : (0 : ℝ) < Fintype.card (LocalEvent A) := by
        exact_mod_cast Fintype.card_pos
      have hc := (div_le_div_iff₀ (mul_pos he (by norm_num)) (mul_pos he hl)).mp h
      have hc' :
          ((Fintype.card (LocalEvent A) : ℝ) *
            (G.rejectionCount (decodedLabeling assignment) : ℝ)) * Fintype.card E ≤
          (2048 * (QueryIncidence.verifierRejectionCount (verifier G) assignment : ℝ)) * Fintype.card E := by
        simpa only [ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts,
          mul_assoc, mul_comm, mul_left_comm] using hc
      have result := (mul_le_mul_iff_left₀ he).mp hc'
      exact_mod_cast result

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem honest_event (G : ConstraintGraph V E A) (labeling : V → A)
    (satisfied : ∀ e, G.edgeSatisfied labeling e = true) (event : Event E A) :
    (verifier G).accepts event (QueryIncidence.response (verifier G) (honestAssignment G labeling) event) =
      true := by
  rcases event with ⟨e, kind, k, f, g, r₀, r₁, r₂⟩
  rw [response_eq_local, honest_edgeOracle G labeling e (satisfied e)]
  simp only [honest_vertexBlock]
  exact AssignmentTester.event_perfect_completeness (AlphabetReduction.pairEncoding (G.accepts e))
    ⟨(labeling (G.tail e), labeling (G.head e)), satisfied e⟩ kind k
    (restrictTape G e f) (restrictTape G e g) (restrictTape G e r₀)
    (restrictTape G e r₁) (restrictTape G e r₂)

omit [DecidableEq A] [Nonempty A] in
theorem perfect_completeness [DecidableEq V] [DecidableEq E] (G : ConstraintGraph V E A)
    (satisfied : G.Satisfiable) : (graph G).Satisfiable := by
  obtain ⟨labeling, h⟩ := satisfied
  exact QueryIncidence.satisfiable_of_verifier_satisfiable (verifier G) (by omega)
    ⟨honestAssignment G labeling, honest_event G labeling h⟩

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

variable {V E A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

/-- Real gaps transfer without rational approximation, including an empty
old dart type. The loss is exactly `2048 * 6 = 12288`. -/
theorem gap_transfer_real [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : ConstraintGraph V E A) (eps : ℝ) (_eps_nonnegative : 0 ≤ eps)
    (source : ∀ labeling : V → A,
      eps * (Fintype.card E : ℝ) ≤ (G.rejectionCount labeling : ℝ))
    (labeling : OutputVertex V E A → QueryIncidence.Label 6) :
    (eps / 12288) * (Fintype.card (OutputDart E A) : ℝ) ≤
      ((AlphabetGraph.graph G).rejectionCount labeling : ℝ) := by
  let assignment := QueryIncidence.decodedAssignment (by decide : 0 < 6) labeling
  have htest :
      (Fintype.card (AlphabetGraph.LocalEvent A) : ℝ) *
          (G.rejectionCount (AlphabetGraph.decodedLabeling assignment) : ℝ) ≤
        2048 * (QueryIncidence.verifierRejectionCount (AlphabetGraph.verifier G) assignment : ℝ) := by
    exact_mod_cast AlphabetGraph.rejection_count_bound G assignment
  have hinc :
      2 * (QueryIncidence.verifierRejectionCount (AlphabetGraph.verifier G) assignment : ℝ) ≤
        ((AlphabetGraph.graph G).rejectionCount labeling : ℝ) := by
    exact_mod_cast QueryIncidence.rejection_count_bound
      (AlphabetGraph.verifier G) (by decide : 0 < 6) labeling
  have hscaled :
      eps * (Fintype.card E : ℝ) * (Fintype.card (AlphabetGraph.LocalEvent A) : ℝ) ≤
        2048 * (QueryIncidence.verifierRejectionCount (AlphabetGraph.verifier G) assignment : ℝ) := by
    calc
      _ = (Fintype.card (AlphabetGraph.LocalEvent A) : ℝ) *
          (eps * (Fintype.card E : ℝ)) := by ring
      _ ≤ (Fintype.card (AlphabetGraph.LocalEvent A) : ℝ) *
          (G.rejectionCount (AlphabetGraph.decodedLabeling assignment) : ℝ) :=
        mul_le_mul_of_nonneg_left (source (AlphabetGraph.decodedLabeling assignment))
          (Nat.cast_nonneg _)
      _ ≤ _ := htest
  change (eps / 12288) *
    (Fintype.card (QueryIncidence.Dart (AlphabetGraph.Event E A) 6) : ℝ) ≤ _
  rw [QueryIncidence.card_dart, AlphabetGraph.card_event]
  push_cast
  nlinarith

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

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_Table
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table

variable {q : Nat}

theorem semantics_rows_congr {n m : Nat} {left right : GraphTables.Rows n m}
    (h : left = right) (hl : GraphTables.Valid left) (hr : GraphTables.Valid right) :
    GraphTables.semantics (⟨n, m, left, hl⟩ : GraphTables.Table) =
      GraphTables.semantics (⟨n, m, right, hr⟩ : GraphTables.Table) := by
  subst right
  rfl

/-- Full decoded graph equality, including reversal, endpoints, and every predicate bit. -/
theorem semantics_build (input : GenericGraphTables.Table q) :
    GraphTables.semantics (build input) =
      GraphTables.enumeratedGraph (AlphabetGraph.graph (GenericGraphTables.semantics input))
        (Enumeration.vertexEquiv input.vertices input.darts q)
        (Enumeration.dartEquiv input.darts q) Enumeration.labelEquiv := by
  exact (semantics_rows_congr (rows_eq_graphRows input) (rows_valid input)
    (GraphTables.graphRows_valid _)).trans (GraphTables.semantics_ofGraph _)

theorem edgeSatisfied_build (input : GenericGraphTables.Table q)
    (labeling : QueryIncidence.Vertex (AlphabetGraph.Event (Fin input.darts) (Fin q))
      (AlphabetGraph.Address (Fin input.vertices) (Fin input.darts) (Fin q)) →
        QueryIncidence.Label 6)
    (dart : QueryIncidence.Dart (AlphabetGraph.Event (Fin input.darts) (Fin q)) 6) :
    (GraphTables.semantics (build input)).edgeSatisfied
      (fun v => Enumeration.labelEquiv
        (labeling ((Enumeration.vertexEquiv input.vertices input.darts q).symm v)))
      (Enumeration.dartEquiv input.darts q dart) =
        (AlphabetGraph.graph (GenericGraphTables.semantics input)).edgeSatisfied labeling dart := by
  rw [semantics_build]
  exact GraphTables.enumeratedGraph_edgeSatisfied _ _ _ _ labeling dart

theorem rejectionCount_build (input : GenericGraphTables.Table q)
    (labeling : QueryIncidence.Vertex (AlphabetGraph.Event (Fin input.darts) (Fin q))
      (AlphabetGraph.Address (Fin input.vertices) (Fin input.darts) (Fin q)) →
        QueryIncidence.Label 6) :
    (GraphTables.semantics (build input)).rejectionCount
      (fun v => Enumeration.labelEquiv
        (labeling ((Enumeration.vertexEquiv input.vertices input.darts q).symm v))) =
        (AlphabetGraph.graph (GenericGraphTables.semantics input)).rejectionCount labeling := by
  rw [semantics_build]
  exact GraphTables.enumeratedGraph_rejectionCount _ _ _ _ labeling

theorem perfect_completeness [Nonempty (Fin q)] (input : GenericGraphTables.Table q)
    (satisfied : (GenericGraphTables.semantics input).Satisfiable) :
    (GraphTables.semantics (build input)).Satisfiable := by
  obtain ⟨labeling, accepted⟩ :=
    AlphabetGraph.perfect_completeness (GenericGraphTables.semantics input) satisfied
  refine ⟨fun v => Enumeration.labelEquiv
    (labeling ((Enumeration.vertexEquiv input.vertices input.darts q).symm v)), ?_⟩
  intro index
  have h := edgeSatisfied_build input labeling
    ((Enumeration.dartEquiv input.darts q).symm index)
  have index_eq := (Enumeration.dartEquiv input.darts q).apply_symm_apply index
  rw [index_eq] at h
  exact h.trans (accepted _)

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_AlphabetTableBoundsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryFormula.compactLiteral_positive _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.clause_eval_extend _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.clause_eval_restrict _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.SourceClause.localEval_restrict _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.patternRelationIndex_eq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_current _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_remaining _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTableBounds

open AlphabetTable

variable {q : Nat}

/-- The actual table output obeys the real gap bound, with no rational
approximation and with empty input dart sets allowed. -/
theorem gap_transfer_real (hq : 0 < q) (input : GenericGraphTables.Table q)
    (eps : ℝ) (eps_nonnegative : 0 ≤ eps)
    (source : ∀ labeling : Fin input.vertices → Fin q,
      eps * (input.darts : ℝ) ≤
        ((GenericGraphTables.semantics input).rejectionCount labeling : ℝ))
    (labeling : Fin (Table.build input).vertices → GraphTables.Label) :
    (eps / 12288) * ((Table.build input).darts : ℝ) ≤
      ((GraphTables.semantics (Table.build input)).rejectionCount labeling : ℝ) := by
  classical
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  let lifted := fun vertex => Enumeration.labelEquiv.symm
    (labeling (Enumeration.vertexEquiv input.vertices input.darts q vertex))
  have h := AlphabetGraphBounds.gap_transfer_real
    (GenericGraphTables.semantics input) eps eps_nonnegative
    (by simpa only [Fintype.card_fin] using source) lifted
  rw [Enumeration.card_dart] at h
  have counts := Table.rejectionCount_build input lifted
  have restored : (fun v : Fin (Table.build input).vertices => Enumeration.labelEquiv
      (lifted ((Enumeration.vertexEquiv input.vertices input.darts q).symm v))) = labeling := by
    funext v
    dsimp only [lifted]
    rw [Enumeration.labelEquiv.apply_symm_apply]
    exact congrArg labeling
      ((Enumeration.vertexEquiv input.vertices input.darts q).apply_symm_apply v)
  rw [restored] at counts
  rw [← counts] at h
  exact h

end UniqueGamesTheorem.Foundations.PCP.AlphabetTableBounds

end

section

namespace UniqueGamesTheorem.Foundations.PCP.VerifierToCNF

open Target

def clauseFailures {n : Nat} (clauses : List (Clause n)) (A : Fin n → Bool) : Nat :=
  (clauses.map (fun c => c.eval A)).count false

theorem forbiddenLiteral_false {q : Nat} (V : FiniteVerifier q) (A : Fin V.variables → Bool)
    (e : Fin V.events) (p : PatternIndex q) (i : Fin q) :
    (forbiddenLiteral V e p i).eval A = false ↔ A (V.query e i) = patternAt q p i := by
  cases hp : patternAt q p i <;> cases ha : A (V.query e i) <;>
    simp [forbiddenLiteral, Literal.eval, hp, ha]

theorem forbiddenClause_values {q : Nat} (V : FiniteVerifier q)
    (B : Fin (outputVariables V) → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (forbiddenClause V e p).map (fun l => l.eval B) =
      mismatchBits V (restrictAssignment V B) e p := by
  simp [forbiddenClause, mismatchBits, List.map_ofFn, Function.comp_def, liftLiteral, Literal.eval,
    restrictAssignment]

theorem mismatchBits_false {q : Nat} (V : FiniteVerifier q) (A : Fin V.variables → Bool)
    (e : Fin V.events) (p : PatternIndex q)
    (actual : ∀ i, A (V.query e i) = patternAt q p i) :
    (mismatchBits V A e p).any id = false := by
  apply List.any_eq_false.mpr
  intro b hb
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
  have h := (forbiddenLiteral_false V A e p i).mpr (actual i)
  simp [h]

theorem mismatchBits_true {q : Nat} (V : FiniteVerifier q) (A : Fin V.variables → Bool)
    (e : Fin V.events) (p : PatternIndex q) (honest : eventValue V A e = true)
    (rejected : V.accepts e (patternAt q p) = false) :
    (mismatchBits V A e p).any id = true := by
  cases h : (mismatchBits V A e p).any id with
  | true => rfl
  | false =>
    have none := List.any_eq_false.mp h
    have equal : (fun i => A (V.query e i)) = patternAt q p := by
      funext i
      apply (forbiddenLiteral_false V A e p i).mp
      have hi := none ((forbiddenLiteral V e p i).eval A)
        (List.mem_ofFn.mpr ⟨i, rfl⟩)
      cases hv : (forbiddenLiteral V e p i).eval A <;> simp_all
    have impossible : V.accepts e (patternAt q p) = true := by
      simpa only [eventValue, equal] using honest
    rw [rejected] at impossible
    contradiction

theorem extended_auxiliary_values {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.variables → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (auxiliaryNames V e p).map (extendAssignment V hq A) = fillBits (mismatchBits V A e p) := by
  simp only [auxiliaryNames, List.map_ofFn, Function.comp_def, extend_fresh, mismatchFill]
  exact ofFn_getElem_of_length _ _ (mismatchFill_length V hq A e p)

theorem tautology_satisfied {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (e : Fin V.events) (B : Fin (outputVariables V) → Bool) :
    (tautology V hq e).eval B = true := by
  simp [tautology, Clause.eval, Literal.eval]

theorem block_honest {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.variables → Bool) (e : Fin V.events) (p : PatternIndex q)
    (honest : eventValue V A e = true) :
    (block V hq e p).all (fun c => c.eval (extendAssignment V hq A)) = true := by
  cases accepted : V.accepts e (patternAt q p) with
  | true => simp [block, accepted, tautology_satisfied]
  | false =>
    have good := (fillBits_correct (mismatchBits V A e p) (by simpa using hq)).mpr
      (mismatchBits_true V A e p honest accepted)
    have values := splitLong_values (forbiddenClause V e p) (auxiliaryNames V e p)
      (extendAssignment V hq A)
    rw [forbiddenClause_values, restrict_extend, extended_auxiliary_values] at values
    have all := congrArg (fun bs : List Bool => bs.all id) values
    simp only [List.all_map, Function.comp_def, id_eq] at all
    simpa only [block, accepted, Bool.false_eq_true, ↓reduceIte] using all.trans good

theorem convert_completeness {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.variables → Bool) (honest : ∀ e, eventValue V A e = true) :
    (convert V hq).Satisfiable := by
  refine ⟨extendAssignment V hq A, fun c hc => ?_⟩
  obtain ⟨e, _, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨p, _, hc⟩ := List.mem_flatMap.mp hc
  exact List.all_eq_true.mp (block_honest V hq A e p (honest e)) c hc

theorem clauseFailures_append {n : Nat} (xs ys : List (Clause n)) (A : Fin n → Bool) :
    clauseFailures (xs ++ ys) A = clauseFailures xs A + clauseFailures ys A := by
  simp [clauseFailures, List.map_append, List.count_append]

theorem clauseFailures_le_flatMap {α : Type*} {n : Nat} (xs : List α)
    (f : α → List (Clause n)) (A : Fin n → Bool) (x : α) (hx : x ∈ xs) :
    clauseFailures (f x) A ≤ clauseFailures (xs.flatMap f) A := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp only [List.flatMap_cons, clauseFailures_append]
      omega
    · have h := ih hx
      simp only [List.flatMap_cons, clauseFailures_append]
      omega

/-- The actual answer pattern forces a failed chain, even when queried names
repeat and regardless of the labels on all allocated auxiliary variables. -/
theorem block_failed {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (B : Fin (outputVariables V) → Bool) (e : Fin V.events) (p : PatternIndex q)
    (rejected : V.accepts e (patternAt q p) = false)
    (actual : ∀ i, restrictAssignment V B (V.query e i) = patternAt q p i) :
    1 ≤ clauseFailures (block V hq e p) B := by
  have bitsFalse := mismatchBits_false V (restrictAssignment V B) e p actual
  have size : ((forbiddenClause V e p).map (fun l => l.eval B)).length =
      ((auxiliaryNames V e p).map B).length + 3 := by
    simp only [List.length_map, forbiddenClause, auxiliaryNames, List.length_ofFn]
    omega
  have failed := chainView_failed ((forbiddenClause V e p).map (fun l => l.eval B))
    ((auxiliaryNames V e p).map B) size (by
      rw [forbiddenClause_values]
      exact bitsFalse)
  simpa only [block, rejected, Bool.false_eq_true, ↓reduceIte, clauseFailures,
    splitLong_values] using failed

theorem eventBlock_failed {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (B : Fin (outputVariables V) → Bool) (e : Fin V.events)
    (rejected : eventValue V (restrictAssignment V B) e = false) :
    1 ≤ clauseFailures (eventBlock V hq e) B := by
  obtain ⟨p, hp⟩ := patternAt_surjective q (fun i => restrictAssignment V B (V.query e i))
  have rejectedPattern : V.accepts e (patternAt q p) = false := by
    rw [hp]
    exact rejected
  have failed := block_failed V hq B e p rejectedPattern (fun i => (congrFun hp i).symm)
  exact failed.trans (clauseFailures_le_flatMap (List.finRange (patterns q).length)
    (block V hq e) B p (by simp))

theorem clauseFailures_flatMap {α : Type*} {n : Nat} (xs : List α)
    (f : α → List (Clause n)) (A : Fin n → Bool) :
    clauseFailures (xs.flatMap f) A = (xs.map (fun x => clauseFailures (f x) A)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, clauseFailures_append, List.map_cons, List.sum_cons, ih]

theorem convert_count_bridge {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (B : Fin (outputVariables V) → Bool) :
    rejectedEventCount V (restrictAssignment V B) ≤ NameCompaction.failedCount (convert V hq) B := by
  change ((List.finRange V.events).map (eventValue V (restrictAssignment V B))).count false ≤
    clauseFailures ((List.finRange V.events).flatMap (eventBlock V hq)) B
  rw [count_false_map_sum, clauseFailures_flatMap]
  apply nat_sum_map_le
  intro e _
  cases rejected : eventValue V (restrictAssignment V B) e with
  | false => simpa only [rejected, Bool.false_eq_true, ↓reduceIte] using
      eventBlock_failed V hq B e rejected
  | true => simp only [↓reduceIte, Nat.zero_le]

end UniqueGamesTheorem.Foundations.PCP.VerifierToCNF

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_FinalBooleanVerifier
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.FinalBooleanVerifier

open Target

variable {V E : Type*} {n m : Nat}

/-- Acceptance is the actual graph predicate on the two recovered labels. -/
theorem eventValue_eq (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (assignment : Fin (n * 6) → Bool) (e : Fin m) :
    VerifierToCNF.eventValue (verifier G vertices edges) assignment e =
      G.edgeSatisfied (labelsOfBits vertices assignment) (edges.symm e) := by
  simp only [VerifierToCNF.eventValue, Fin.addCases_left, Fin.addCases_right,
    ConstraintGraph.edgeSatisfied]
  rfl

/-- The enumeration preserves the exact directed-dart rejection count. -/
theorem rejection_count_eq [Fintype E] (G : ConstraintGraph V E Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) (assignment : Fin (n * 6) → Bool) :
    VerifierToCNF.rejectedEventCount (verifier G vertices edges) assignment =
      G.rejectionCount (labelsOfBits vertices assignment) := by
  classical
  change ((List.finRange m).map
    (VerifierToCNF.eventValue (verifier G vertices edges) assignment)).count false = _
  rw [count_false_finRange]
  change (Finset.univ.filter (fun e : Fin m =>
    VerifierToCNF.eventValue (verifier G vertices edges) assignment e = false)).card =
      (G.rejectedDarts (labelsOfBits vertices assignment)).card
  apply Finset.card_equiv edges.symm
  intro e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    ConstraintGraph.rejectedDarts, eventValue_eq]

theorem verifier_completeness (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (labeling : V → Label)
    (satisfied : ∀ e, G.edgeSatisfied labeling e = true) :
    ∀ e, VerifierToCNF.eventValue (verifier G vertices edges)
      (bitsOfLabels vertices labeling) e = true := by
  intro e
  rw [eventValue_eq, labelsOfBits_bitsOfLabels]
  exact satisfied (edges.symm e)

abbrev OutputAssignment (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) :=
  Fin (VerifierToCNF.outputVariables (verifier G vertices edges)) → Bool

def extractLabeling (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (assignment : OutputAssignment G vertices edges) : V → Label :=
  labelsOfBits vertices (VerifierToCNF.restrictAssignment (verifier G vertices edges) assignment)

theorem cnf_completeness (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (sat : G.Satisfiable) : (cnf G vertices edges).Satisfiable := by
  obtain ⟨labeling, satisfied⟩ := sat
  exact VerifierToCNF.convert_completeness (verifier G vertices edges) (by decide)
    (bitsOfLabels vertices labeling) (verifier_completeness G vertices edges labeling satisfied)

theorem cnf_count_bridge [Fintype E] (G : ConstraintGraph V E Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) (assignment : OutputAssignment G vertices edges) :
    G.rejectionCount (extractLabeling G vertices edges assignment) ≤
      NameCompaction.failedCount (cnf G vertices edges) assignment := by
  have h := VerifierToCNF.convert_count_bridge (verifier G vertices edges) (by decide) assignment
  rw [rejection_count_eq] at h
  exact h

theorem failedCount_zero_of_satisfied (F : Formula) (assignment : Fin F.variables → Bool)
    (satisfied : ∀ c ∈ F.clauses, c.eval assignment = true) :
    NameCompaction.failedCount F assignment = 0 := by
  apply (VerifierToCNF.zero_false_count_iff_all _).mpr
  have h := List.all_eq_true.mpr satisfied
  simpa only [NameCompaction.evaluationList, List.all_map, Function.comp_def, id_eq] using h

theorem cnf_reflects [Fintype E] (G : ConstraintGraph V E Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) (sat : (cnf G vertices edges).Satisfiable) :
    G.Satisfiable := by
  obtain ⟨assignment, satisfied⟩ := sat
  have zero := failedCount_zero_of_satisfied (cnf G vertices edges) assignment satisfied
  have bound := cnf_count_bridge G vertices edges assignment
  have graphZero : G.rejectionCount (extractLabeling G vertices edges assignment) = 0 := by omega
  exact ⟨extractLabeling G vertices edges assignment,
    all_satisfied_of_rejectionCount_zero G _ graphZero⟩

theorem cnf_satisfiable_iff [Fintype E] (G : ConstraintGraph V E Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) :
    (cnf G vertices edges).Satisfiable ↔ G.Satisfiable :=
  ⟨cnf_reflects G vertices edges, cnf_completeness G vertices edges⟩

end UniqueGamesTheorem.Foundations.PCP.FinalBooleanVerifier

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingOverlayTables
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables

open PoweringWalks

theorem constraintGraph_ext {V E A : Type*} {G H : ConstraintGraph V E A}
    (hreverse : ∀ e, G.reverse e = H.reverse e)
    (htail : ∀ e, G.tail e = H.tail e)
    (haccepts : ∀ e a b, G.accepts e a b = H.accepts e a b) : G = H := by
  rcases G with ⟨r, hi, t, p, hp⟩
  rcases H with ⟨r', hi', t', p', hp'⟩
  have hr : r = r' := Equiv.ext hreverse
  cases hr
  have ht : t = t' := funext htail
  cases ht
  have ha : p = p' := funext fun e => funext fun a => funext fun b => haccepts e a b
  cases ha
  rfl

end UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PoweringPortReindexLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables
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

def walkEquiv (ports : D ≃ E) (n : Nat) : Walk V D n ≃ Walk V E n :=
  Equiv.prodCongr (Equiv.refl V) (wordEquiv ports n)

variable (G : PortGraph V D) (H : PortGraph V E) (ports : D ≃ E)
variable (rotation : ∀ v d, H.rot (v, ports d) =
  ((G.rot (v,d)).1, ports (G.rot (v,d)).2))

include rotation

theorem wordEnd_map (n : Nat) (v : V) (p : Fin n → D) :
    wordEnd H n v (wordEquiv ports n p) = wordEnd G n v p := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    simp only [wordEnd, next, wordEquiv, Equiv.coe_fn_mk, rotation]
    exact ih _ _

theorem endpoint_map (n : Nat) (w : Walk V D n) :
    endpoint H (walkEquiv ports n w) = endpoint G w :=
  wordEnd_map G H ports rotation n w.1 w.2

theorem reach_iff (t : Nat) (v u : V) :
    (∃ n, n ≤ t ∧ ∃ p : Fin n → D, wordEnd G n v p = u) ↔
    (∃ n, n ≤ t ∧ ∃ p : Fin n → E, wordEnd H n v p = u) := by
  constructor
  · rintro ⟨n,hn,p,hp⟩
    exact ⟨n,hn,wordEquiv ports n p,(wordEnd_map G H ports rotation n v p).trans hp⟩
  · rintro ⟨n,hn,p,hp⟩
    refine ⟨n,hn,(wordEquiv ports n).symm p,?_⟩
    rw [← wordEnd_map G H ports rotation, Equiv.apply_symm_apply]
    exact hp

def ballEquiv (t : Nat) (v : V) : Ball G t v ≃ Ball H t v where
  toFun u := ⟨u.val,(reach_iff G H ports rotation t v u.val).mp u.property⟩
  invFun u := ⟨u.val,(reach_iff G H ports rotation t v u.val).mpr u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem wordToBall_map (t : Nat) (v : V) (w : PortWords D t) :
    wordToBall H t v (addressEquiv ports t w) =
      ballEquiv G H ports rotation t v (wordToBall G t v w) := by
  apply Subtype.ext
  exact wordEnd_map G H ports rotation w.1.val v w.2

/-- Use the target selector, including its concrete enumeration choices. -/
def pullSelector {t : Nat} {v : V} (S : AddressSelector H t v) :
    AddressSelector G t v where
  address u := (addressEquiv ports t).symm
    (S.address (ballEquiv G H ports rotation t v u))
  correct u := by
    apply (ballEquiv G H ports rotation t v).injective
    rw [← wordToBall_map, Equiv.apply_symm_apply, S.correct]

theorem decode_pullSelector {t : Nat} {v : V} (S : AddressSelector H t v)
    (a : PaddedLabel E t A) (u : Ball G t v) :
    decode (pullSelector G H ports rotation S) (labelEquiv ports t a) u =
      decode S a (ballEquiv G H ports rotation t v u) := by
  simp [decode, pullSelector, labelEquiv]

theorem decode_transport {t : Nat} (selectors : ∀v, AddressSelector H t v)
    (a : PaddedLabel E t A) {v w : V} (hvw : v = w)
    (u : Ball G t v) (u' : Ball H t w) (hu : u.val = u'.val) :
    decode (pullSelector G H ports rotation (selectors v)) (labelEquiv ports t a) u =
      decode (selectors w) a u' := by
  subst w
  rw [decode_pullSelector]
  congr 1
  exact Subtype.ext hu

theorem advanceTail_map (n : Nat) (w : Walk V D (n+1)) :
    advanceTail H (walkEquiv ports (n+1) w) =
      walkEquiv ports n (advanceTail G w) := by
  apply Prod.ext
  · change (H.rot (w.1, ports (w.2 0))).1 = (G.rot (w.1,w.2 0)).1
    rw [rotation]
  · rfl

theorem edgeAt_map (n : Nat) (w : Walk V D (n+1)) (k : Fin (n+1)) :
    edgeAt H n (walkEquiv ports (n+1) w) k =
      ((edgeAt G n w k).1, ports (edgeAt G n w k).2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    induction k using Fin.cases with
    | zero => rfl
    | succ k =>
      simp only [edgeAt, Fin.cases_succ]
      rw [advanceTail_map G H ports rotation]
      exact ih _ _

variable (accepts : Edge V E → A → A → Bool)

theorem pathAccepts_map (n : Nat) (selectors : ∀v, AddressSelector H (n+1) v)
    (w : Walk V D (n+1)) (a b : PaddedLabel E (n+1) A) :
    pathAccepts G (pullAccepts ports accepts) n
      (fun v => pullSelector G H ports rotation (selectors v)) w
      (labelEquiv ports (n+1) a) (labelEquiv ports (n+1) b) =
    pathAccepts H accepts n selectors (walkEquiv ports (n+1) w) a b := by
  classical
  unfold pathAccepts
  congr 1
  apply propext
  apply forall_congr'
  intro k
  have ht := decode_transport G H ports rotation selectors a rfl
    (tailFromStart G n w k) (tailFromStart H n (walkEquiv ports (n+1) w) k)
    (congrArg Prod.fst (edgeAt_map G H ports rotation n w k)).symm
  have hh := decode_transport G H ports rotation selectors b
    (endpoint_map G H ports rotation (n+1) w).symm
    (headFromEnd G n w k) (headFromEnd H n (walkEquiv ports (n+1) w) k)
    (by
      change (G.rot (edgeAt G n w k)).1 =
        (H.rot (edgeAt H n (walkEquiv ports (n+1) w) k)).1
      rw [edgeAt_map G H ports rotation, rotation])
  rw [ht, hh]
  simp only [pullAccepts, edgeAt_map G H ports rotation]
  rfl

def dartEquiv (n : Nat) : Dart V D n ≃ Dart V E n :=
  Equiv.prodCongr (Equiv.refl Bool) (walkEquiv ports (n+1))

theorem edgeSatisfied_map (n : Nat) (selectors : ∀v, AddressSelector H (n+1) v)
    (labels : V → PaddedLabel E (n+1) A) (e : Dart V D n) :
    (poweredGraph G (pullAccepts ports accepts) n
      (fun v => pullSelector G H ports rotation (selectors v))).edgeSatisfied
        (fun v => labelEquiv ports (n+1) (labels v)) e =
    (poweredGraph H accepts n selectors).edgeSatisfied labels (dartEquiv ports n e) := by
  rcases e with ⟨direction,w⟩
  rw [poweredGraph_edgeSatisfied]
  change _ = (poweredGraph H accepts n selectors).edgeSatisfied labels
    (direction, walkEquiv ports (n+1) w)
  rw [poweredGraph_edgeSatisfied, endpoint_map G H ports rotation]
  exact pathAccepts_map G H ports rotation accepts n selectors w _ _

theorem rejectionCount_map [Fintype V] [Fintype D] [Fintype E]
    (n : Nat) (selectors : ∀v, AddressSelector H (n+1) v)
    (labels : V → PaddedLabel E (n+1) A) :
    (poweredGraph G (pullAccepts ports accepts) n
      (fun v => pullSelector G H ports rotation (selectors v))).rejectionCount
        (fun v => labelEquiv ports (n+1) (labels v)) =
    (poweredGraph H accepts n selectors).rejectionCount labels := by
  classical
  unfold ConstraintGraph.rejectionCount
  apply Finset.card_bij (fun e _ => dartEquiv ports n e)
  · intro e he
    rw [ConstraintGraph.mem_rejectedDarts, ← edgeSatisfied_map G H ports rotation]
    exact (ConstraintGraph.mem_rejectedDarts _ _ _).mp he
  · intro e _ f _ h
    exact (dartEquiv ports n).injective h
  · intro e he
    refine ⟨(dartEquiv ports n).symm e, ?_, (dartEquiv ports n).apply_symm_apply e⟩
    rw [ConstraintGraph.mem_rejectedDarts, edgeSatisfied_map G H ports rotation,
      Equiv.apply_symm_apply]
    exact (ConstraintGraph.mem_rejectedDarts _ _ _).mp he

theorem pullReverse
    (reverse_accepts : ∀ e a b, accepts (H.rot e) b a = accepts e a b)
    (e : Edge V D) (a b : A) :
    pullAccepts ports accepts (G.rot e) b a = pullAccepts ports accepts e a b := by
  simpa only [pullAccepts, rotation] using reverse_accepts (e.1,ports e.2) a b

theorem base_edgeSatisfied_map
    (reverse_accepts : ∀ e a b, accepts (H.rot e) b a = accepts e a b)
    (assignment : V → A) (e : Edge V D) :
    (baseGraph G (pullAccepts ports accepts)
      (pullReverse G H ports rotation accepts reverse_accepts)).edgeSatisfied assignment e =
    (baseGraph H accepts reverse_accepts).edgeSatisfied assignment (e.1,ports e.2) := by
  change accepts (e.1,ports e.2) (assignment e.1) (assignment (G.rot e).1) =
    accepts (e.1,ports e.2) (assignment e.1) (assignment (H.rot (e.1,ports e.2)).1)
  rw [rotation]

theorem base_rejectionCount_map [Fintype V] [Fintype D] [Fintype E]
    (reverse_accepts : ∀ e a b, accepts (H.rot e) b a = accepts e a b)
    (assignment : V → A) :
    (baseGraph G (pullAccepts ports accepts)
      (pullReverse G H ports rotation accepts reverse_accepts)).rejectionCount assignment =
    (baseGraph H accepts reverse_accepts).rejectionCount assignment := by
  classical
  let e : Edge V D ≃ Edge V E := Equiv.prodCongr (Equiv.refl V) ports
  have edgeEq (x : Edge V D) :=
    base_edgeSatisfied_map G H ports rotation accepts reverse_accepts assignment x
  unfold ConstraintGraph.rejectionCount
  apply Finset.card_bij (fun x _ => e x)
  · intro x hx
    rw [ConstraintGraph.mem_rejectedDarts]
    change (baseGraph H accepts reverse_accepts).edgeSatisfied assignment (x.1,ports x.2) = false
    rw [← edgeEq]
    exact (ConstraintGraph.mem_rejectedDarts _ _ _).mp hx
  · intro x _ y _ h
    exact e.injective h
  · intro y hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [ConstraintGraph.mem_rejectedDarts, edgeEq]
    change (baseGraph H accepts reverse_accepts).edgeSatisfied assignment (e (e.symm y)) = false
    rw [e.apply_symm_apply]
    exact (ConstraintGraph.mem_rejectedDarts _ _ _).mp hy

omit rotation in
/-- The generic lazy-graph gap survives a genuine rotation-preserving port
change and the target's chosen selectors, for every raw target labeling. -/
theorem uniform_count_gap
    [Fintype V] [Fintype D] [Fintype E] [Nonempty V] [Nonempty D]
    [Fintype A] [Nonempty A]
    (G : PortGraph V D) (H : PortGraph V E) (ports : (Bool × D) ≃ E)
    (rotation : ∀ v d, H.rot (v, ports d) =
      (((lazyGraph G).rot (v,d)).1, ports ((lazyGraph G).rot (v,d)).2))
    (lambda : ℝ) (certificate : SpectralCertificate (lazyGraph G) lambda)
    (accepts : Edge V E → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (H.rot e) b a = accepts e a b)
    (M : Nat) (hM : 1 ≤ M)
    (selectors : ∀v, AddressSelector H (2*center (Fintype.card A) M+1) v)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hgap : ∀ assignment : V → A,
      epsilon * (Fintype.card (Edge V E) : ℝ) ≤
        ((baseGraph H accepts reverse_accepts).rejectionCount assignment : ℝ))
    (labels : V → PaddedLabel E (2*center (Fintype.card A) M+1) A) :
    (gain (Fintype.card A) M lambda *
      min epsilon (1 / ((2*center (Fintype.card A) M+1 : Nat) : ℝ))) *
        (Fintype.card (Dart V E (2*center (Fintype.card A) M)) : ℝ) ≤
      ((poweredGraph H accepts (2*center (Fintype.card A) M) selectors).rejectionCount labels : ℝ) := by
  have hbase : ∀ assignment : V → A,
      epsilon * (Fintype.card (Edge V (Bool × D)) : ℝ) ≤
      ((baseGraph (lazyGraph G) (pullAccepts ports accepts)
        (pullReverse (lazyGraph G) H ports rotation accepts reverse_accepts)).rejectionCount assignment : ℝ) := by
    intro assignment
    rw [base_rejectionCount_map (lazyGraph G) H ports rotation,
      Fintype.card_congr (Equiv.prodCongr (Equiv.refl V) ports)]
    exact hgap assignment
  have bound := PoweringGap.uniform_count_gap G lambda certificate
    (pullAccepts ports accepts)
    (pullReverse (lazyGraph G) H ports rotation accepts reverse_accepts) M hM
    (fun v => pullSelector (lazyGraph G) H ports rotation (selectors v))
    epsilon hepsilon hbase (fun v => labelEquiv ports _ (labels v))
  rw [rejectionCount_map (lazyGraph G) H ports rotation,
    Fintype.card_congr (dartEquiv (V := V) ports (2*center (Fintype.card A) M))] at bound
  exact bound

end UniqueGamesTheorem.Foundations.PCP.PoweringPortReindex

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_FinalConstantsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.FinalConstants

noncomputable def cap : ℝ := 1 / (walkLength : ℝ)

theorem cap_positive : 0 < cap := by
  exact one_div_pos.mpr (by exact_mod_cast walkLength_positive)

theorem cap_le_one : cap ≤ 1 := by
  apply (div_le_one (by exact_mod_cast walkLength_positive)).2
  exact_mod_cast walkLength_positive

/-- The exact fixed constants make a whole round double the input gap until
the fixed positive threshold `cap` is reached. -/
theorem composed_gap (epsilon : ℝ) (he : 0 ≤ epsilon) :
    min (2 * epsilon) cap ≤
      gain * min (epsilon / (Preprocessing.sizeFactor : ℝ))
        (1 / (walkLength : ℝ)) := by
  have hs : (0 : ℝ) < Preprocessing.sizeFactor := by
    exact_mod_cast Preprocessing.sizeFactor_positive
  have hs1 : (1 : ℝ) ≤ Preprocessing.sizeFactor := by
    exact_mod_cast Preprocessing.sizeFactor_positive
  have hg : 0 ≤ gain := le_trans (by positivity) gain_large
  rw [mul_min_of_nonneg _ _ hg]
  apply min_le_min
  · calc
      2 * epsilon = (2 * (Preprocessing.sizeFactor : ℝ)) *
          (epsilon / (Preprocessing.sizeFactor : ℝ)) := by field_simp
      _ ≤ gain * (epsilon / (Preprocessing.sizeFactor : ℝ)) :=
        mul_le_mul_of_nonneg_right gain_large (div_nonneg he hs.le)
  · change cap ≤ gain * cap
    have hgain : 1 ≤ gain := by linarith [gain_large]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hgain cap_positive.le

end UniqueGamesTheorem.Foundations.PCP.FinalConstants

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

/-- Prefix, pivot and suffix together have the fixed odd walk length. -/
theorem walkLength_eq :
    2 * PoweringSoundness.center (Fintype.card Alphabet) FinalConstants.windowHalf + 1 =
      FinalConstants.walkLength := by
  rw [center_eq]
  rfl

/-- Both the coefficient and cap in the actual estimate match the fixed
round constants, for every real error parameter. -/
theorem scaled_bound_eq (ε : ℝ) :
    (PoweringSoundness.gain (Fintype.card Alphabet) FinalConstants.windowHalf (31 / 32) *
        min ε
          (1 / ((2 * PoweringSoundness.center (Fintype.card Alphabet)
            FinalConstants.windowHalf + 1 : Nat) : ℝ))) / 12288 =
      FinalConstants.gain * min ε FinalConstants.cap := by
  rw [walkLength_eq]
  rw [mul_div_right_comm, gain_card_eq]
  rfl

/-- The composed powering and alphabet-reduction coefficient yields the
fixed doubling bound after the checked preprocessing loss. -/
theorem composed_scaled_gap (ε : ℝ) (hε : 0 ≤ ε) :
    min (2 * ε) FinalConstants.cap ≤
      (PoweringSoundness.gain (Fintype.card Alphabet) FinalConstants.windowHalf (31 / 32) *
        min (ε / (Preprocessing.sizeFactor : ℝ))
          (1 / ((2 * PoweringSoundness.center (Fintype.card Alphabet)
            FinalConstants.windowHalf + 1 : Nat) : ℝ))) / 12288 := by
  rw [scaled_bound_eq]
  exact FinalConstants.composed_gap ε hε

end UniqueGamesTheorem.Foundations.PCP.PoweringFinalConstants

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingRegularTablesLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
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

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables

open scoped BigOperators
open PoweringWalks DegreeReplacement

theorem edgeSatisfied_ofCloudTables (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (labels : Fin (vertexCount t padding) → GraphTables.Label)
    (v : Vertex t padding) (p : Fin q ⊕ Unit) :
    (PortTables.baseGraph (ofCloudTables t padding tables)).edgeSatisfied labels
        (vertexOrder t padding v, portOrder q p) =
      (sourceGraph t padding tables).edgeSatisfied
        (fun z => labels (vertexOrder t padding z)) (v, p) := by
  change PortTables.accepts (ofCloudTables t padding tables)
    (vertexOrder t padding v, portOrder q p) (labels (vertexOrder t padding v))
    (labels (PortTables.rotation (ofCloudTables t padding tables)
      (vertexOrder t padding v, portOrder q p)).1) = _
  rw [rotation_ofCloudTables, accepts_ofCloudTables]
  rfl

/-- Numbering preserves the rejection count for every labeling. -/
theorem rejectionCount_ofCloudTables (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (labels : Fin (vertexCount t padding) → GraphTables.Label) :
    (PortTables.baseGraph (ofCloudTables t padding tables)).rejectionCount labels =
      (sourceGraph t padding tables).rejectionCount
        (fun z => labels (vertexOrder t padding z)) := by
  classical
  unfold ConstraintGraph.rejectionCount
  symm
  apply Finset.card_equiv (Equiv.prodCongr (vertexOrder t padding) (portOrder q))
  rintro ⟨v, p⟩
  simp only [ConstraintGraph.mem_rejectedDarts, Equiv.prodCongr_apply,
    Prod.map_apply, edgeSatisfied_ofCloudTables]

def liftedLabel (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (labels : Fin t.vertices → GraphTables.Label) :
    Fin (vertexCount t padding) → GraphTables.Label :=
  fun z => labels (paddedOwner (GraphTables.semantics t) (fun v => Fin (padding v))
    ((vertexOrder t padding).symm z))

end UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables

/-!
# Exact serialized family tables at actual regularization vertices

The geometric family maps request zero to a one-vertex table. Empty clouds in
regularization instead remain empty. The bridge therefore requires positive
cloud size, derived here from each actual original or dummy vertex.
-/

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingPaddingTables
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.accepts_materialize _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.lazy_accepts_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.lazy_accepts_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.overlay_accepts_expander _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.overlay_accepts_old
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

/-- Exact occurrence counts for arbitrary labels on all old and added vertices. -/
theorem pad_rejectionCount (table : Table n d) (h : n ≤ m)
    (labeling : Fin m → Label) :
    (baseGraph (pad table h)).rejectionCount labeling =
      (baseGraph table).rejectionCount (fun v => labeling (v.castLE h)) := by
  classical
  calc
    (baseGraph (pad table h)).rejectionCount labeling =
        (sumGraph table m).rejectionCount (fun v => labeling (vertexEquiv h v)) := by
      unfold ConstraintGraph.rejectionCount
      symm
      apply Finset.card_equiv (dartEquiv h)
      intro e
      simp only [ConstraintGraph.mem_rejectedDarts, edgeSatisfied_pad_equiv]
    _ = (baseGraph table).rejectionCount (fun v => labeling (v.castLE h)) := by
      simpa only [sumGraph, vertexEquiv_inl] using
        VertexPadding.pad_rejectionCount (baseGraph table) rfl (m - n)
          (fun v => labeling (vertexEquiv h v))

/-- A particular padded labeling satisfies exactly when its old restriction does. -/
theorem pad_labeling_satisfies_iff (table : Table n d) (h : n ≤ m)
    (labeling : Fin m → Label) :
    (∀ e, (baseGraph (pad table h)).edgeSatisfied labeling e = true) ↔
      ∀ e, (baseGraph table).edgeSatisfied (fun v => labeling (v.castLE h)) e = true := by
  constructor
  · intro hs e
    simpa only [edgeSatisfied_pad_old] using hs (e.1.castLE h, e.2)
  · intro hs e
    obtain ⟨v, hv⟩ := (vertexEquiv h).surjective e.1
    have he : e = (vertexEquiv h v, e.2) := Prod.ext hv.symm rfl
    rw [he]
    cases v with
    | inl v => simpa only [vertexEquiv_inl, edgeSatisfied_pad_old] using hs (v, e.2)
    | inr v => exact edgeSatisfied_pad_new table h labeling v e.2

/-- A computable extension uses label zero on every dummy vertex. -/
def extendLabeling (h : n ≤ m) (labeling : Fin n → Label) : Fin m → Label :=
  fun v => Sum.elim labeling (fun _ => 0) ((vertexEquiv h).symm v)

@[simp] theorem extendLabeling_old (h : n ≤ m) (labeling : Fin n → Label) (v : Fin n) :
    extendLabeling h labeling (v.castLE h) = labeling v := by
  simp only [extendLabeling, vertexEquiv_symm_old, Sum.elim_inl]

theorem pad_satisfiable_iff (table : Table n d) (h : n ≤ m) :
    (baseGraph (pad table h)).Satisfiable ↔ (baseGraph table).Satisfiable := by
  constructor
  · rintro ⟨labeling, hs⟩
    exact ⟨fun v => labeling (v.castLE h), (pad_labeling_satisfies_iff table h labeling).1 hs⟩
  · rintro ⟨labeling, hs⟩
    refine ⟨extendLabeling h labeling, (pad_labeling_satisfies_iff table h _).2 ?_⟩
    simpa only [extendLabeling_old] using hs

end UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingRegularSoundness
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
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

/-- Erasing a proof-equal table size preserves its exact spectral certificate. -/
theorem resizeTable_certificate {n m q : Nat} (h : n = m)
    (table : ExpanderTables.Table n q) (lambda : ℝ)
    (certificate : SpectralCertificate (ExpanderTables.graph table) lambda) :
    SpectralCertificate (ExpanderTables.graph (resizeTable h table)) lambda := by
  cases h
  exact certificate

theorem familyCloudTable_certificate_of_pos (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) (v : Fin t.vertices)
    (hk : 0 < PreprocessingCloudIndex.cloudSize t v) :
    SpectralCertificate (ExpanderTables.graph (familyCloudTable H t v)) (1 / 2 : ℝ) := by
  let : NeZero Expanders.baseDegree := ⟨baseDegree_ne_zero⟩
  unfold familyCloudTable
  rw [dite_eq_right (Nat.ne_of_gt hk)]
  apply resizeTable_certificate
  exact ExpanderTables.family_certificate H certificate _

theorem cloudGraphs_certificate_of_pos (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) (v : Fin t.vertices)
    (hk : 0 < PreprocessingCloudIndex.cloudSize t v) :
    SpectralCertificate (cloudGraphs t (padding t) (familyCloudTable H t) v)
      (1 / 2 : ℝ) := by
  exact GraphTransport.reindex_spectralCertificate _ _ _ _
    (familyCloudTable_certificate_of_pos H certificate t v hk)

/-- The exact finite cut inequality needed to pay for each changed cloud label. -/
theorem cloud_expansion (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) (v : Fin t.vertices)
    (S : Finset (PreprocessingCloudIndex.PaddedCloud t (padding t) v))
    (hsmall : S.card ≤
      Fintype.card (PreprocessingCloudIndex.PaddedCloud t (padding t) v) / 2) :
    2 * S.card ≤ (CloudRounding.directedCut
      (fun ed => ((cloudGraphs t (padding t) (familyCloudTable H t) v).rot ed).1) S).card := by
  by_cases hk : PreprocessingCloudIndex.cloudSize t v = 0
  · have hzero : Fintype.card (PreprocessingCloudIndex.PaddedCloud t (padding t) v) = 0 := by
      rw [PreprocessingCloudIndex.card_paddedCloud, cloudSize_add_padding, hk]
      rfl
    have hs : S.card = 0 := by omega
    simp only [hs, mul_zero, Nat.zero_le]
  · exact SpectralCut.cut_card_ge_twice
      (cloudGraphs t (padding t) (familyCloudTable H t) v)
      (cloudGraphs_certificate_of_pos H certificate t v (Nat.pos_of_ne_zero hk))
      (by simpa only [Fintype.card_fin] using internalDegree_ge_eight) S (by
        change 2 * S.card ≤
          Fintype.card (PreprocessingCloudIndex.PaddedCloud t (padding t) v)
        omega)

/-- Decode the actual numbered output labels by majority in each padded cloud. -/
noncomputable def roundLabels (t : GraphTables.Table)
    (labels : Fin (vertexCount t (padding t)) → GraphTables.Label) :
    Fin t.vertices → GraphTables.Label :=
  CloudRounding.roundLabels
    (paddedGraph (GraphTables.semantics t) (fun v => Fin (padding t v)))
    (fun z => labels (vertexOrder t (padding t) z))

/-- Direct soundness for the generated tables, with no matching-base premise. -/
theorem soundness (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table)
    (labels : Fin (vertexCount t (padding t)) → GraphTables.Label) :
    (GraphTables.semantics t).rejectionCount (roundLabels t labels) ≤
      (PortTables.baseGraph (regularize H t)).rejectionCount labels := by
  rw [regularize, rejectionCount_ofCloudTables]
  exact CloudRounding.padded_replacement_soundness (GraphTables.semantics t)
    (fun v => Fin (padding t v)) (cloudGraphs t (padding t) (familyCloudTable H t))
    (cloud_expansion H certificate t) (fun z => labels (vertexOrder t (padding t) z))

theorem completeness (H : BaseTable) (t : GraphTables.Table)
    (h : (GraphTables.semantics t).Satisfiable) :
    (PortTables.baseGraph (regularize H t)).Satisfiable := by
  obtain ⟨labels, hlabels⟩ := h
  refine ⟨liftedLabel t (padding t) labels, ?_⟩
  intro e
  obtain ⟨z, rfl⟩ :=
    (Equiv.prodCongr (vertexOrder t (padding t)) (portOrder internalDegree)).surjective e
  rcases z with ⟨v, p⟩
  change (PortTables.baseGraph (regularize H t)).edgeSatisfied
    (liftedLabel t (padding t) labels)
    (vertexOrder t (padding t) v, portOrder internalDegree p) = true
  rw [regularize, edgeSatisfied_ofCloudTables]
  simp only [liftedLabel, Equiv.symm_apply_apply]
  have hcomplete := replacement_complete
    (paddedGraph (GraphTables.semantics t) (fun v => Fin (padding t v)))
    (cloudGraphs t (padding t) (familyCloudTable H t)) labels
    (padded_complete (GraphTables.semantics t) (fun v => Fin (padding t v)) labels hlabels)
    (v, p)
  convert hcomplete using 1
  all_goals try with_reducible_and_instances rfl
  rfl

end UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularSoundness

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingTablesLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Soundness and expansion of the actual executable preprocessing tables.
The fixed base-table spectral certificate is supplied by the proved expander
existence theorem; no output expansion or output gap is assumed. -/

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingGuarantees

open PoweringWalks SpectralReturn PreprocessingTables
open PreprocessingRegularTables (internalDegree regularize)

variable {n d e : Nat}

theorem overlayFamily_certificate (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) :
    SpectralCertificate (ExpanderTables.graph (overlayFamily H t)) (1 / 2 : ℝ) := by
  let : NeZero Expanders.baseDegree := ⟨PreprocessingRegularSoundness.baseDegree_ne_zero⟩
  apply PreprocessingRegularSoundness.resizeTable_certificate
  exact ExpanderTables.family_certificate H certificate _

def restrictedLabel (t : GraphTables.Table)
    (labels : Fin (vertices t) → GraphTables.Label) :
    Fin (regularVertices t) → GraphTables.Label :=
  fun v => labels (v.castLE (PreprocessingLevels.le_paddedSize (regularVertices t)))

def roundLabels (t : GraphTables.Table)
    (labels : Fin (vertices t) → GraphTables.Label) : Fin t.vertices → GraphTables.Label :=
  PreprocessingRegularSoundness.roundLabels t (restrictedLabel t labels)

end UniqueGamesTheorem.Foundations.PCP.PreprocessingGuarantees

end

end

section

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.RoundGap

open AmplificationRound

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [Nonempty E]

def poweredLower (epsilon : ℝ) : ℝ :=
  PoweringSoundness.gain (Fintype.card Label) FinalConstants.windowHalf (31 / 32) *
    min (epsilon / (Preprocessing.sizeFactor : ℝ)) FinalConstants.cap

theorem poweredLower_nonnegative (epsilon : ℝ) (he : 0 ≤ epsilon) :
    0 ≤ poweredLower epsilon := by
  have hg := PoweringGap.gain_nonneg (Fintype.card Label)
    FinalConstants.windowHalf (31 / 32) (by norm_num)
  have hs : (0 : ℝ) < Preprocessing.sizeFactor := by
    exact_mod_cast Preprocessing.sizeFactor_positive
  exact mul_nonneg hg (le_min (div_nonneg he hs.le) FinalConstants.cap_positive.le)

end UniqueGamesTheorem.Foundations.PCP.RoundGap

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_SourceGapLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-!
The actual finite graph iteration used by the mathematical PCP construction.
One fixed, explicitly supplied complete address list is shared by every round.
Each round constructs a new constraint graph. The scalar gap and size are the
actual minimum rejection fraction and actual finite cardinalities of that graph.

The final Boolean formula uses supplied vertex and dart numberings. These
theorems establish the finite objects and their size/gap properties, not a
machine running-time theorem or an independently encoded NP-hardness theorem.
-/

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.PCPIteration

open FiniteGraph

def finalClauseGap : ℚ := 1 / (40960 * (FinalConstants.walkLength : ℚ))

end UniqueGamesTheorem.Foundations.PCP.PCPIteration

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_RawInitialTablesLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit structural numberings of the raw 3SAT incidence graph. Unused
declared variable names are retained; their unary input header pays for them.
The graph has one dummy vertex and one tautological loop, even for an empty
formula. No input-dependent choice of a finite enumeration is made. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialTables

open Target GraphTables

theorem raw64_satisfiable_iff (F : Formula) : (raw64 F).Satisfiable ↔ F.Satisfiable :=
  (AlphabetRetraction.satisfiable_pullback_iff (InitialGraph.raw F)
    AlphabetRetraction.decode64 AlphabetRetraction.encode64
      AlphabetRetraction.decode_encode64).trans (InitialGraph.raw_satisfiable_iff F)

theorem table_semantics (F : Formula) :
    GraphTables.semantics (table F) =
      (raw64 F).reindex (vertexOrder F) (dartOrder F) labelOrder := by
  change GraphTables.semantics (GraphTables.ofGraph
    (GraphTables.enumeratedGraph (raw64 F) (vertexOrder F) (dartOrder F) labelOrder)) = _
  rw [GraphTables.semantics_ofGraph]
  rfl

theorem table_satisfiable_iff (F : Formula) :
    (GraphTables.semantics (table F)).Satisfiable ↔ F.Satisfiable := by
  rw [table_semantics]
  exact ((raw64 F).satisfiable_reindex (vertexOrder F) (dartOrder F) labelOrder).trans
    (raw64_satisfiable_iff F)

end UniqueGamesTheorem.Foundations.PCP.RawInitialTables

/-! Polynomial arithmetic for the actual initial-machine phase counts. The
separate execution theorem must connect these counts to the concrete program. -/

/-! Explicit finite predicates and numeric row words of the initial incidence table.
Every relation retains all 4096 entries, including repetitions. -/

/-! The concrete numbered amplification round, with one fixed base expander.
Every intermediate is an actual stored table, with explicit finite coordinates.
The running-time certificate is a separate theorem about these same functions. -/

namespace UniqueGamesTheorem.Foundations.PCP.RoundTables

theorem alphabet_positive : 0 < alphabet := by
  unfold alphabet PoweringTables.labelCount
  exact Nat.pow_pos (by decide)

instance instNonemptyFinDartsValTableLtNatOfNat (input : Input) : Nonempty (Fin input.val.darts) := ⟨⟨0, input.property⟩⟩

def Satisfiable (input : Input) : Prop := (GraphTables.semantics input.val).Satisfiable

noncomputable def gap (input : Input) : ℝ := (GraphTables.semantics input.val).gap

theorem gap_nonnegative (input : Input) : 0 ≤ gap input :=
  (GraphTables.semantics input.val).gap_nonnegative

theorem gap_eq_zero_iff (input : Input) : gap input = 0 ↔ Satisfiable input :=
  (GraphTables.semantics input.val).gap_eq_zero_iff

theorem one_le_size_mul_gap (input : Input) (unsat : ¬ Satisfiable input) :
    1 ≤ (size input : ℝ) * gap input := by
  have h := (GraphTables.semantics input.val).inverse_card_le_gap_of_unsatisfiable unsat
  have hp : (0 : ℝ) < input.val.darts := Nat.cast_pos.mpr input.property
  simp only [Fintype.card_fin] at h
  have hd := (div_le_iff₀ hp).mp h
  have hsize : (input.val.darts : ℝ) ≤ (size input : ℝ) := by
    exact_mod_cast (Nat.le_add_left input.val.darts input.val.vertices)
  exact (show 1 ≤ (input.val.darts : ℝ) * gap input by
    simpa only [gap, mul_comm] using hd).trans
    (mul_le_mul_of_nonneg_right hsize (gap_nonnegative input))

theorem initial_satisfiable_iff (F : Target.Formula) : Satisfiable (initial F) ↔ F.Satisfiable :=
  RawInitialTables.table_satisfiable_iff F

end UniqueGamesTheorem.Foundations.PCP.RoundTables

/-! Gap amplification for the actual numbered table round. The fixed base
expander is the only supplied construction datum with a spectral certificate. -/

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

instance alphabetFintype (tape : Tape) : Fintype (Alphabet tape) := by
  cases tape <;> exact inferInstanceAs (Fintype Bool)

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

instance alphabetFintype (tape : Tape) : Fintype (Alphabet tape) := by
  rw [alphabet_eq]
  exact inferInstanceAs (Fintype Bool)

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_PoweringMachineRelationLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rotor step on the live unary port-table encoding. First read the reverse
dart identifier; then read that dart's tail vertex. This uses no division or
runtime graph data in finite control. Both positional selections are proved
from the actual serialization. -/

/-! Fixed port words are executed by a finite chain of actual rotor programs.
The six shared tapes hold table, query, scan, reverse identifier, scratch and
output. Each walk position has a separate physical vertex tape. The final
unary copy also handles the empty word and preserves the starting vertex. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineWord

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

instance labelDecidableEq (t : Nat) : DecidableEq (Label t) := by
  induction t with
  | zero => exact inferInstanceAs (DecidableEq MachineUnaryAffineAt.Label)
  | succ t ih =>
      letI := ih
      exact inferInstanceAs (DecidableEq (PoweringMachineRotor.Label ⊕ Label t))

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineWord

/-! A fixed shared tape layout for the actual powering field subroutines.
The vertex identifiers live on physical tapes. The trajectory capacity is
fixed by `max`; each bounded word uses its first `t` trajectory tapes. -/

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_PoweringGlobalEnumerationLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Explicit executable enumeration of the global powering tapes

The four header tapes come first, followed by the eleven shared roles, the
bounded trajectory tapes, and the final output tape. Both directions use
constructor cases and arithmetic sum encodings. No enumeration is selected
from a cardinality theorem.
-/

/-! A concrete relation-field producer: execute a fixed word from the live
start vertex, then read the predicate at the reached vertex and fixed port.
All instructions use the shared tape layout and preserve the finite row
buffer. No execution premise is supplied by the caller. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineField

open Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {n d max : Nat}

instance labelDecidableEq (op : Instruction d) : DecidableEq (Label op) := by
  cases op <;> dsimp only [Label] <;> infer_instance

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineField

/-! The concrete finite program that produces an entire powered-row input
block. Its static control executes the field plan backwards, so prepending each
computed unary Boolean field leaves the canonical serialized block in order. -/

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OriginalPrefixContinuation
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalPrefixContinuation

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n k t : Nat} {K : Type*} [Fintype K]

def tagLaw (ν : FiniteDistribution K) (hbranch : 0 < branch n) :
    FiniteDistribution (Fin (branch n) × K) := by
  letI : Nonempty (Fin (branch n)) := ⟨⟨0, hbranch⟩⟩
  exact (FiniteDistribution.uniform (Fin (branch n))).product ν

end
end PerfectCompleteness.OriginalPrefixContinuation

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_UpperCutTriangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.UpperCutTriangle

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped Classical

noncomputable section

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n j i t : Nat}

abbrev Prefix (branch : Nat → Nat) (j i : Nat) := GeometricCutSplit.Prefix branch (j + 1) (i + 1)

end
end PerfectCompleteness.UpperCutTriangle

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_GeometricPrefixSplit
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.GeometricPrefixSplit

open RecursiveSpaces DescendantSpaces
open GeometricCutSplit (Prefix PrefixDepth prefixPathDepth prefixPath castPath prefixLaw)
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

variable {branch : Nat → Nat}

variable {root mid low : Nat}

def splitEquiv (hlow : low ≤ mid) (hmid : mid ≤ root) :
    Prefix branch root low ≃ Prefix branch root mid × Prefix branch mid low :=
  (Equiv.cast (congrArg (PrefixDepth branch low)
    (show root - low = (mid - low) + (root - mid) by omega))).trans
      ((depthEquiv low (mid - low) (root - mid)).trans
        ((Equiv.cast (congrArg (fun n => PrefixDepth branch n (root - mid))
          (Nat.add_sub_of_le hlow))).prodCongr (Equiv.refl _)))

def joinEquiv (hlow : low ≤ mid) (hmid : mid ≤ root) :
    Prefix branch root mid × Prefix branch mid low ≃ Prefix branch root low :=
  (splitEquiv hlow hmid).symm

@[simp] theorem split_join (hlow : low ≤ mid) (hmid : mid ≤ root)
    (pair : Prefix branch root mid × Prefix branch mid low) :
    splitEquiv hlow hmid (joinEquiv hlow hmid pair) = pair :=
  (splitEquiv hlow hmid).apply_symm_apply pair

@[simp] theorem join_split (hlow : low ≤ mid) (hmid : mid ≤ root)
    (pref : Prefix branch root low) :
    joinEquiv hlow hmid (splitEquiv hlow hmid pref) = pref :=
  (splitEquiv hlow hmid).symm_apply_apply pref

end PerfectCompleteness.GeometricPrefixSplit

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalPairCoarse
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalPairCoarse

open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped BigOperators Classical

noncomputable section

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat} {Ω : Type*} [Fintype Ω]
  (S : HierarchicalAdviceExperiment.Experiment branch rows n t Ω)

abbrev PairRecord := HierarchicalAgreementMean.PairRecord (rows := rows) S.slots S.upper
abbrev Matrix := HierarchicalMatrixTable.Matrix (rows := rows) S.slots S.upper
abbrev OldRecord := HierarchicalAdviceExperiment.Background S × Matrix S

local instance backgroundFintype : Fintype (HierarchicalAdviceExperiment.Background S) :=
  Fintype.ofFinite _

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace S.slots S.upper) :=
  Fintype.ofFinite _

def oldRecord (record : PairRecord S) : OldRecord S := (record.1, record.2.1)

end
end PerfectCompleteness.HierarchicalPairCoarse

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HeterogeneousPairAdvice
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HeterogeneousPairAdvice

noncomputable section

open scoped BigOperators Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat} {O : Type*} [Fintype O]
  {Ω : O → Type*} [∀ o, Fintype (Ω o)]
  (S : (o : O) → HierarchicalAdviceExperiment.Experiment branch rows n t (Ω o))

local instance backgroundFintype (o : O) :
    Fintype (HierarchicalAdviceExperiment.Background (S o)) :=
  HierarchicalAdviceExperiment.backgroundFintype (S o)

local instance rowSpaceFintype_rd52179_2 (o : O) :
    Fintype (NodeEmbedding.RowSpace (S o).slots (S o).upper) :=
  HierarchicalPairCoarse.rowSpaceFintype (S o)
abbrev PairSample := Σ o : O, HierarchicalPairCoarse.PairRecord (S o)

abbrev AdviceSample (r : Nat) :=
  Σ z : PairSample S, HierarchicalAdviceExperiment.Advice (S z.1) r

def appendLaw (P : FiniteDistribution (PairSample S)) (r : Nat) :
    FiniteDistribution (AdviceSample S r) :=
  CompletionSoundness.sigmaLaw P
    (fun z => HierarchicalAdviceExperiment.adviceLaw (S z.1) r)

def referencePairLaw (outer : FiniteDistribution O)
    (backgrounds : (o : O) →
      FiniteDistribution (HierarchicalAdviceExperiment.Background (S o)))
    (hrows : ∀ o, 0 < rows (Nodes.height (S o).upper)) :
    FiniteDistribution (PairSample S) :=
  CompletionSoundness.sigmaLaw outer (fun o =>
    HierarchicalAgreementMean.referenceLaw (S o).slots (S o).upper (backgrounds o) (hrows o))

end
end PerfectCompleteness.HeterogeneousPairAdvice

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_OwnInputAffineSliceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.OwnInputAffineSlice

noncomputable section

open scoped BigOperators TensorProduct Classical
open UniqueGamesTheorem.Foundations.Games
open TreeSourceSpaces HierarchicalArrays OwnInputReference

section FiniteLaws

variable {A B T : Type*} [Fintype A] [Fintype B] [Fintype T]

theorem probability_product_and (μ : FiniteDistribution A) (ν : FiniteDistribution B)
    (hidden : A → Bool) (visible : B → Bool) :
    (μ.product ν).probability (fun x => hidden x.1 && visible x.2) =
      μ.probability hidden * ν.probability visible := by
  simp only [FiniteDistribution.probability, FiniteDistribution.product,
    Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro v _
  cases hidden h <;> cases visible v <;> simp

theorem product_slice_positive (μ : FiniteDistribution A) (ν : FiniteDistribution B)
    (g : A → T) (slice : T → Bool) (visible : B → Bool)
    (positive : 0 < (μ.product ν).probability
      (fun x => slice (g x.1) && visible x.2)) :
    0 < (μ.pushforward g).probability slice := by
  rw [FiniteDistribution.probability_pushforward]
  by_contra hn
  have hz : μ.probability (fun h => slice (g h)) = 0 :=
    le_antisymm (le_of_not_gt hn) (μ.probability_nonnegative _)
  have hp := positive
  rw [probability_product_and μ ν (fun h : A => slice (g h)) visible, hz, zero_mul] at hp
  exact (lt_irrefl 0) hp

end FiniteLaws

section TensorMatch

variable {ℓ : Nat} {H : Type*} [AddCommGroup H] [Module F2 H]
  [Finite H] [FiniteDimensional F2 H]

def tensorSlice (W : Submodule F2 (Fin ℓ → F2))
    (Q : Submodule F2 (Module.Dual F2 H)) (target : Q →ₗ[F2] W)
    (X : W ⊗[F2] H) : Bool :=
  decide (TensorRestriction.restrictionMap Q X = target)

end TensorMatch

end
end PerfectCompleteness.OwnInputAffineSlice


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalProjectedSliceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HierarchicalProjectedSlice

noncomputable section

open scoped BigOperators Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (originalSlots projectedSlots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ s j, MixedSupport.Projection (originalSlots s j) (projectedSlots s j))
  (upper : Nodes branch n) (lowerLevel : Nat)
  (background : HierarchicalMatrixTable.Background (rows := rows) originalSlots upper)

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace originalSlots upper) :=
  Fintype.ofFinite _

variable {Ω : Type*}
  [Fintype Ω]
  (original : FiniteDistribution Ω)
  (arrays : Ω → Arrays originalSlots rows)
  (lowerEvent : Ω → Bool)
  (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  {r : Nat}
  (ρ : ℝ)
  (A : ManyGoodRows.RowMap (Block rows upper) r)

local instance valueFintype_rd52179_3 : Fintype
    (Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :=
  Fintype.ofFinite _
abbrev HiddenTensor := LinearMap.ker A ⊗[F2] NodeEmbedding.NodeH projectedSlots upper

end
end PerfectCompleteness.HierarchicalProjectedSlice


namespace PerfectCompleteness.HierarchicalProjectedMeeting

noncomputable section

open scoped Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays HierarchicalProjectedSlice
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype
attribute [local instance] RightDecoder.characterFintype RightDecoder.scalarFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots projected : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ s j, MixedSupport.Projection (slots s j) (projected s j))
  (upper : Nodes branch n) (lowerLevel : Nat)
  (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _

end
end PerfectCompleteness.HierarchicalProjectedMeeting


namespace PerfectCompleteness.SourceProjectedCanonicalQuery

open scoped Classical
open RecursiveSpaces TreeSourceSpaces HierarchicalArrays

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  {slots projected : Slots branch n → Fin t → MixedSupport.Slot}
  (rows : Nat → Nat)
  (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))

def query {Y : Type*} (arrays : Arrays slots rows) (post : Output branch n rows → Y) :
    MixedSupport.Assignment (TreeCanonical.numberedSlots slots) → Y :=
  post ∘ TreeCanonical.numberedFunction slots (fullJoint arrays)

end
end PerfectCompleteness.SourceProjectedCanonicalQuery


namespace PerfectCompleteness.HierarchicalProjectedRawPrediction

noncomputable section

open scoped Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n t : Nat}
  (originalSlots projectedSlots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ s j, MixedSupport.Projection (originalSlots s j) (projectedSlots s j))
  (rows : Nat → Nat) (upper lower : Nodes branch n) (lowerLevel : Nat)

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace originalSlots upper) :=
  Fintype.ofFinite _

end
end PerfectCompleteness.HierarchicalProjectedRawPrediction

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_HierarchicalBackgroundVariation
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalBackgroundVariation

open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped BigOperators Classical

noncomputable section

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n)

local instance backgroundFintype :
    Fintype (HierarchicalAgreementMean.Background (rows := rows) slots upper) := Fintype.ofFinite _

end
end PerfectCompleteness.HierarchicalBackgroundVariation

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalUsefulBackground
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalUsefulBackground

open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped Classical

noncomputable section

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n)

local instance backgroundFintype :
    Fintype (HierarchicalAgreementMean.Background (rows := rows) slots upper) := Fintype.ofFinite _

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace slots upper) := Fintype.ofFinite _

end
end PerfectCompleteness.HierarchicalUsefulBackground

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_ProjectedCutChoices
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ProjectedCutChoices

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  {Z : Fin (branch n) → Type*} [∀ child, Fintype (Z child)]
  (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
  (projected : (child : Fin (branch n)) → Z child → Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ child z s a, MixedSupport.Projection
    (childSlots slots child s a) (projected child z s a))

def choicesLaw (choiceLaw : (child : Fin (branch n)) → FiniteDistribution (Z child))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) : FiniteDistribution (Choices (Z := Z)) :=
  FiniteProduct.law (fun child =>
    (ProjectionPosterior.bernoulli β hβ hβ').product (choiceLaw child))

end
end PerfectCompleteness.ProjectedCutChoices

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceProjectedTag
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceProjectedTag

noncomputable section

open scoped Classical
open RecursiveSpaces
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n t m v : Nat}

def flagLaw (flag : Fin (branch n) → FiniteDistribution Bool) :
    FiniteDistribution (Flags (branch := branch) (n := n)) :=
  FiniteProduct.law flag

end
end PerfectCompleteness.SourceProjectedTag

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_InitializationMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine


open Turing
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)
open PostfixModel

@[simp] theorem tapes_reversed (base : Tape → List Bool) (m i d : Nat) (output : List Bool) :
    tapes base m i d output .reversed = output := rfl

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_OrClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure

open Turing PostfixModel
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)


variable {K Λ σ : Type} [DecidableEq K]

@[simp] theorem tokenBits_false : tokenBits [Token.const false] = [false] := rfl

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourceClauseCountMachine
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceClauseCountMachine


open Turing UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition UniqueGamesTheorem.Reduction.MachineTransfer

variable {K Λ A : Type} [DecidableEq K]

def instruction (tape : Fin 4 → K) (labels : Label → Λ) (done rejected : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .tableOut => loopAt (tape 0) (tape 2) id false
      (labels .tableOut) (some (labels .tableBack))
  | .tableBack => MachineCopy.forkLoop (tape 2) (tape 0) (tape 1) false
      (labels .tableBack) (some (labels (.skip 0)))
  | .skip slot => UnaryBlockSkipMachine.instruction (tape 1) (labels (.skip slot))
      (UnaryBlockSkipMachine.nextField (fun slot => labels (.skip slot))
        (some (labels .readCount)) slot) rejected
  | .readCount => Hastad.SourceMachine.fieldLoop (tape 1) (tape 3)
      (labels .readCount) (some (labels .drain))
  | .drain => MachineDrain.drain (tape 1) (labels .drain) done

variable (tape : Fin 4 → K) (distinct : Function.Injective tape)
variable (labels : Label → Λ) (done rejected : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ l, program (labels l) = instruction tape labels done rejected l)
variable (base : K → List Bool) (ambient : A)

include distinct atLabels

theorem copyTrace (table output : List Bool)
    (tableWord : base (tape 0) = table) (scratchEmpty : base (tape 2) = []) :
    (advance (TM2.step program))^[2 * (table.length + 1)]
      (some ⟨some (labels .tableOut), clean ambient, workTapes tape base [] output⟩) =
      some ⟨some (labels (.skip 0)), clean ambient, workTapes tape base table output⟩ := by
  have hd (i j : Fin 4) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have source : workTapes tape base [] output (tape 0) = table := by
    simp [workTapes, hd, tableWord]
  have scratch : workTapes tape base [] output (tape 2) = [] := by
    simp [workTapes, hd, scratchEmpty]
  have run := MachineCopy.copyTrace (tape 0) (tape 1) (tape 2)
    (hd 0 1 (by decide)) (hd 0 2 (by decide)) (hd 1 2 (by decide)) false
    (labels .tableOut) (labels .tableBack) (some (labels (.skip 0))) program
    (atLabels .tableOut) (atLabels .tableBack) (workTapes tape base [] output)
    scratch ambient none
  rw [source, workTapes_input tape distinct, List.append_nil, update_input tape distinct] at run
  exact run

theorem readTrace (m : Nat) (body output : List Bool) :
    (advance (TM2.step program))^[m + 1]
      (some ⟨some (labels .readCount), clean ambient,
        workTapes tape base (encodeWord m ++ body) output⟩) =
      some ⟨some (labels .drain), clean ambient,
        workTapes tape base body (List.replicate m true ++ output)⟩ := by
  have different : tape 1 ≠ tape 3 := fun h => (by decide : (1 : Fin 4) ≠ 3) (distinct h)
  exact Hastad.SourceMachine.fieldLoopTrace (tape 1) (tape 3) different
    (labels .readCount) (some (labels .drain)) program (atLabels .readCount)
    base m body output ambient none

theorem drainTrace (body output : List Bool) :
    (advance (TM2.step program))^[body.length + 1]
      (some ⟨some (labels .drain), clean ambient, workTapes tape base body output⟩) =
      some ⟨done, clean ambient, workTapes tape base [] output⟩ := by
  have run := MachineDrain.drainTrace (tape 1) (labels .drain) done program
    (atLabels .drain) (workTapes tape base [] output) body ambient none
  rw [update_input tape distinct, update_input tape distinct] at run
  exact run

end PerfectCompleteness.SourceClauseCountMachine

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

theorem loopTapes_index (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input : List Bool) (remaining first : Nat) (output : List Bool) :
    loopTapes tape base input remaining first output (tape 2) = List.replicate first true := by
  have hd (i j : Fin 5) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  simp [loopTapes, hd]

theorem update_input (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input replacement : List Bool) (remaining first : Nat)
    (output : List Bool) :
    Function.update (loopTapes tape base input remaining first output) (tape 0) replacement =
      loopTapes tape base replacement remaining first output := by
  have hd (i j : Fin 5) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 0
  · subst k; simp [loopTapes, hd]
  · simp [loopTapes, h, Function.update_apply]

theorem update_index (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input : List Bool) (remaining first replacement : Nat)
    (output : List Bool) :
    Function.update (loopTapes tape base input remaining first output)
        (tape 2) (List.replicate replacement true) =
      loopTapes tape base input remaining replacement output := by
  have hd (i j : Fin 5) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 2
  · subst k; simp [loopTapes, hd]
  · simp [loopTapes, h, Function.update_apply]

theorem tapesAt_loop (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input replacement : List Bool) (remaining first : Nat)
    (output newOutput : List Bool) :
    tapesAt (tape 0) (tape 4) (loopTapes tape base input remaining first output)
      replacement newOutput = loopTapes tape base replacement remaining first newOutput := by
  unfold tapesAt
  rw [update_input tape distinct, update_output]

end Program

end PerfectCompleteness.SourceOccurrenceLoopMachine

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

def instruction (q : Nat) (enumeration : Fin stackCount ≃ K) (tape : Fin 4 → K)
    (initial : A) (labels : Labels enumeration (tape 3) → Λ) :
    Labels enumeration (tape 3) → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .reverse => loopAt (tape 0) (tape 3) id false (labels .reverse)
      (some (labels (.header TargetHeaderMachine.main)))
  | .header label => TargetHeaderMachine.instruction q (headerTape tape)
      (fun l => labels (.header l))
      (MachineDrainMany.entry (MachineDrainMany.workTapes enumeration (tape 3))
        (fun l => labels (.cleanup l)) (some (labels .finish))) label
  | .cleanup label => MachineDrainMany.instruction
      (MachineDrainMany.workTapes enumeration (tape 3))
      (fun l => labels (.cleanup l)) (some (labels .finish)) label
  | .finish => .load (fun _ => (initial, none)) .halt

def budget (q count : Nat) (enumeration : Fin stackCount ≃ K) (tape : Fin 4 → K)
    (base : K → List Bool) (body : List Bool) : Nat :=
  body.length + 1 + (6 * (count + 2) + 1) +
    (MachineDrainMany.lengthSum (MachineDrainMany.workTapes enumeration (tape 3))
      (headerTapes q count tape base body) +
      (MachineDrainMany.workTapes enumeration (tape 3)).length) + 1

end PerfectCompleteness.TargetFinalizeMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_TermMachine
attribute [-simp] _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_false _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_archive _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableWords.decode_rotationWords _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.TermMachine

open Turing MachineComposition PostfixModel


@[simp] theorem tokenBits_append (first second : List Token) :
    tokenBits (first ++ second) = tokenBits first ++ tokenBits second := by
  simp [tokenBits, tokenWords, List.flatMap_append, encodeWords_append]


end UniqueGamesTheorem.Foundations.Complexity.CookLevin.TermMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_TargetFinalizeBound
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

omit [DecidableEq K] in
theorem lengthSum_le (chosen : List K) (base : K → List Bool) (B : Nat)
    (bounded : ∀ k, (base k).length ≤ B) :
    MachineDrainMany.lengthSum chosen base ≤ chosen.length * B := by
  induction chosen with
  | nil => simp [MachineDrainMany.lengthSum]
  | cons k chosen ih =>
      simp only [MachineDrainMany.lengthSum, List.map_cons, List.sum_cons,
        List.length_cons, Nat.add_mul, Nat.one_mul] at *
      have hk := bounded k
      omega

theorem budget_le (q count : Nat) (enumeration : Fin stackCount ≃ K) (tape : Fin 4 → K)
    (base : K → List Bool) (body : List Bool) (B : Nat)
    (bounded : ∀ k, (base k).length ≤ B) (bodyBound : body.length ≤ B)
    (countBound : count ≤ B) :
    budget q count enumeration tape base body ≤
      (15 + stackCount * (q + 9)) * (B + 1) := by
  let chosen := MachineDrainMany.workTapes enumeration (tape 3)
  have hlength : chosen.length ≤ stackCount := MachineDrainMany.workTapes_length_le _ _
  have hsum := lengthSum_le chosen (headerTapes q count tape base body) (4 * B + q + 4)
    (headerTapes_length_le q count tape base body B bounded bodyBound countBound)
  have hsum' := hsum.trans (Nat.mul_le_mul_right (4 * B + q + 4) hlength)
  have hsmall : 4 * B + q + 5 ≤ (q + 9) * (B + 1) := by
    rw [Nat.mul_add, Nat.mul_one, Nat.add_mul]
    omega
  have hscaled := Nat.mul_le_mul_left stackCount hsmall
  have hfirst : body.length + 1 + (6 * (count + 2) + 1) + 1 ≤ 15 * (B + 1) := by
    omega
  calc
    budget q count enumeration tape base body ≤
        15 * (B + 1) + stackCount * (4 * B + q + 5) := by
          unfold budget
          dsimp only [chosen] at hsum' hlength
          rw [Nat.mul_add stackCount (4 * B + q + 4) 1, Nat.mul_one]
          omega
    _ ≤ 15 * (B + 1) + stackCount * ((q + 9) * (B + 1)) := Nat.add_le_add_left hscaled _
    _ = _ := by simp only [Nat.add_mul, Nat.mul_assoc]

end PerfectCompleteness.TargetFinalizeBound

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_StoppedSharedSampler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedSharedSampler

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open PreliminarySampler
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {v m n t cut : Nat} {branch rows repeats : Nat → Nat}

abbrev Context (branch : Nat → Nat) (n t m cut : Nat) (rows : Nat → Nat) :=
  Questions branch n t m ×
    (GeometricCutSplit.Prefix branch n (cut + 1) × CanonicalDirections.Tuple rows n)

end
end PerfectCompleteness.StoppedSharedSampler

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_WholeArrayExteriorLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeArrayExteriorLaw

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open TreeSourceSpaces HierarchicalArrays DescendantSpaces WholeArraySampler

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

instance exteriorFintype (rows : Nat → Nat)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (lower : Nodes branch (n + 1)) :
    Fintype (OwnInputReference.Exterior slots rows (Sum.inl ()) lower) :=
  OwnInputReference.exteriorFintype (branch := branch) (n := n + 1) (t := t)
    slots rows (Sum.inl ()) lower

end
end PerfectCompleteness.WholeArrayExteriorLaw

end

end OAI
end


