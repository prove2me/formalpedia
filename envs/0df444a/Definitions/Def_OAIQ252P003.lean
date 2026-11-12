-- Prove2me | Definitions.Def_OAIQ252P003
-- name    : OAIQ252P003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T07:32:20.126638+00:00
-- url     : https://prove2.me/theorems/15e49502-f8c0-48e8-865c-32dcddfe417c
-- title:
--   Definitions bundle OAIQ252P003 of the split of OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 846 declarations of OpenAI's Lean: 415 definitions, 14 inductive types or structures, 22 instances and 395 theorems. The definitions and types are `OAI.PerfectCompleteness.BinaryInputReduction.computation`, `OAI.PerfectCompleteness.BinaryTotalInputMachine.computableInPolyTime`, `OAI.PerfectCompleteness.BinaryTotalInputMachine.outputsInTime`, `OAI.PerfectCompleteness.BlockQuotient.blockFiberEquiv`, `OAI.PerfectCompleteness.BlockQuotient.projectBlock`, `OAI.PerfectCompleteness.BoundedListSampling.jointLaw`, `OAI.PerfectCompleteness.BoundedListSampling.listLaw`, `OAI.PerfectCompleteness.BoundedListSampling.outputLaw`, `OAI.PerfectCompleteness.BucketMatrixResampling.Matrix`, `OAI.PerfectCompleteness.BucketMatrixResampling.assembledMatrix`, `OAI.PerfectCompleteness.BucketQuotientAgreement.agreement`, `OAI.PerfectCompleteness.BucketQuotientAgreement.directionCollision`, `OAI.PerfectCompleteness.BucketSampler.RecursiveTape`, `OAI.PerfectCompleteness.BucketSampler.recursiveEvaluate`, `OAI.PerfectCompleteness.BucketSampler.recursiveTapeLaw`, `OAI.PerfectCompleteness.BucketSampler.tapeLaw`, `OAI.PerfectCompleteness.BucketUniform.coordinateDirection`, `OAI.PerfectCompleteness.BucketUniform.coordinateTape`, `OAI.PerfectCompleteness.BucketUniform.evaluateLinear`, `OAI.PerfectCompleteness.BucketUniform.ofRowsLinear`, `OAI.PerfectCompleteness.BucketUsefulCollision.fill`, `OAI.PerfectCompleteness.CandidateCoupling.DirectionTuple`, `OAI.PerfectCompleteness.CandidateCoupling.Shared`, `OAI.PerfectCompleteness.CandidateCoupling.candidateFraction`, `OAI.PerfectCompleteness.CandidateCoupling.conditionalSharedLaw`, `OAI.PerfectCompleteness.CandidateCoupling.directionsLaw`, `OAI.PerfectCompleteness.CandidateCoupling.sharedLaw`, `OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse`, `OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine`, `OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel`, `OAI.PerfectCompleteness.CanonicalDictionaryAppendMachine.State`, `OAI.PerfectCompleteness.CanonicalDictionaryAppendMachine.clean`, `OAI.PerfectCompleteness.CanonicalDictionaryAppendMachine.emitLoop`, `OAI.PerfectCompleteness.CanonicalDictionaryAppendMachine.finish`, `OAI.PerfectCompleteness.CanonicalDictionaryAppendMachine.instruction`, `OAI.PerfectCompleteness.CanonicalDictionaryMachine.Label`, `OAI.PerfectCompleteness.CanonicalDictionaryMachine.State`, `OAI.PerfectCompleteness.CanonicalDictionaryMachine.Token`, `OAI.PerfectCompleteness.CanonicalDictionaryMachine.clean`, `OAI.PerfectCompleteness.CanonicalDictionaryMachine.index` and 389 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `PerfectCompleteness_Algebra_BilinearGramCompressionLemmas`, `PerfectCompleteness_Algebra_BucketMatrixResampling`, `PerfectCompleteness_Algebra_CanonicalMatrixTable`, `PerfectCompleteness_Algebra_HierarchicalMatrixTable`, `PerfectCompleteness_Algebra_MatrixRowQuotientLaw`, `PerfectCompleteness_Construction_BucketQuotientAgreement`, `PerfectCompleteness_Construction_CanonicalLocalCompletion`, `PerfectCompleteness_Construction_CutChildGrouping`, `PerfectCompleteness_Construction_DescendantSpacesLemmas`, `PerfectCompleteness_Construction_FlexibleLocalCompletionLemmas`, `PerfectCompleteness_Construction_LocalCompletionFamily`, `PerfectCompleteness_Construction_NodeEmbedding`, `PerfectCompleteness_Construction_OriginalChildScalarAssemblyLemmas`, `PerfectCompleteness_Construction_OriginalChildScalars`, `PerfectCompleteness_Construction_ProjectedNodeEmbedding`, `PerfectCompleteness_Construction_RelativeDescendantProductsLemmas`, `PerfectCompleteness_Construction_SourceQuestionOrderLemmas`, `PerfectCompleteness_Construction_TreeCanonical`, `PerfectCompleteness_Construction_TreeSourceSpaces`, `PerfectCompleteness_Decoding_BucketUsefulCollision`, `PerfectCompleteness_Decoding_ChildAssemblyProjection`, `PerfectCompleteness_Decoding_ChildBlockProjection`, `PerfectCompleteness_Decoding_DecoderContraction`, `PerfectCompleteness_Decoding_DecoderSourcePullback`, `PerfectCompleteness_Decoding_HierarchicalLeftDecoder`, `PerfectCompleteness_Decoding_HierarchicalUsefulCollision`, `PerfectCompleteness_Decoding_RightDecoderLemmas`, `PerfectCompleteness_Foundations_CanonicalCoarseningErasure`, `PerfectCompleteness_Foundations_CanonicalDictionaryNames`, `PerfectCompleteness_Foundations_CanonicalDirections`, `PerfectCompleteness_Foundations_CanonicalEdgesLemmas`, `PerfectCompleteness_Foundations_CanonicalKeys`, `PerfectCompleteness_Foundations_CanonicalPartialTable`, `PerfectCompleteness_Foundations_CanonicalVertexNames`, `PerfectCompleteness_Foundations_ClauseSupportLemmas`, `PerfectCompleteness_Foundations_CutTerminalSplit`, `PerfectCompleteness_Foundations_DesignatedLeavesLemmas`, `PerfectCompleteness_Foundations_FiniteProduct`, `PerfectCompleteness_Foundations_GeometricPathLemmas`, `PerfectCompleteness_Foundations_HierarchicalAgreementMean`, `PerfectCompleteness_Foundations_HierarchicalArrays`, `PerfectCompleteness_Foundations_HierarchicalFrozenTablesLemmas`, `PerfectCompleteness_Foundations_KeyFiniteness`, `PerfectCompleteness_Foundations_LinearEvaluationLemmas`, `PerfectCompleteness_Foundations_ManyGoodRowsLemmas`, `PerfectCompleteness_Foundations_OccurrenceStochasticLemmas`, `PerfectCompleteness_Foundations_OddListExtraction`, `PerfectCompleteness_Foundations_PartitionsLemmas`, `PerfectCompleteness_Foundations_PrefixTests`, `PerfectCompleteness_Foundations_QuotientTableAgreementLemmas`, `PerfectCompleteness_Foundations_RecursiveSpaceEquivLemmas`, `PerfectCompleteness_Foundations_RecursiveSpaces`, `PerfectCompleteness_Foundations_SourceClause`, `PerfectCompleteness_Foundations_SourceOddListsLemmas`, `PerfectCompleteness_Foundations_SourceStrategy`, `PerfectCompleteness_Foundations_TerminalCalls`, `PerfectCompleteness_Machines_BinaryInputReduction`, `PerfectCompleteness_Machines_BinaryOccurrenceRename`, `PerfectCompleteness_Machines_BinaryParsingLemmas`, `PerfectCompleteness_Machines_BinaryRenameMachine`, `PerfectCompleteness_Machines_BinaryTotalInputMachine`, `PerfectCompleteness_Machines_BinaryValidatorMachine`, `PerfectCompleteness_Machines_CanonicalCoarseningEncoding`, `PerfectCompleteness_Machines_CanonicalDictionaryAppendMachine`, `PerfectCompleteness_Machines_CanonicalDictionaryMachine`, `PerfectCompleteness_Machines_CanonicalEndpointMachine`, `PerfectCompleteness_Machines_CanonicalKeyMachine`, `PerfectCompleteness_Machines_CanonicalKeyShapeMachineLemmas`, `PerfectCompleteness_Machines_CanonicalLabelEncoding`, `PerfectCompleteness_Machines_DomainEncoding`, `PerfectCompleteness_Machines_FiniteBlockMachineLemmas`, `PerfectCompleteness_Machines_KeyMetadataMachine`, `PerfectCompleteness_Machines_OwnInputReferenceLemmas`, `PerfectCompleteness_Reduction_CanonicalGameLemmas`, `PerfectCompleteness_Reduction_CanonicalNamedGame`, `PerfectCompleteness_Reduction_CompletionSoundness`, `PerfectCompleteness_Reduction_OccurrenceGame`, `PerfectCompleteness_Reduction_PreliminaryAveraging`, `PerfectCompleteness_Reduction_SourceCompleteness`, `PerfectCompleteness_Reduction_SourceGame`, `PerfectCompleteness_Repetition_CleanConditioning`, `PerfectCompleteness_Repetition_CutChildCleanLawLemmas`, `PerfectCompleteness_Repetition_RepetitionRateLemmas`, `PerfectCompleteness_Sampling_BoundedListSamplingLemmas`, `PerfectCompleteness_Sampling_BucketSampler`, `PerfectCompleteness_Sampling_BucketUniformLemmas`, `PerfectCompleteness_Sampling_CandidateCoupling`, `PerfectCompleteness_Sampling_CutSamplerRefinement`, `PerfectCompleteness_Sampling_FiniteListSampling`, `PerfectCompleteness_Sampling_PreliminarySampler`, `PerfectCompleteness_Sampling_RationalFiniteLawLemmas`, `PerfectCompleteness_Sampling_RecordSeedSamplingLemmas`, `PerfectCompleteness_Sampling_UniformChildSum`, `PerfectCompleteness_Sampling_WholeArraySampler`, `UniqueGames_Foundations_Conditioning`, `UniqueGames_Foundations_FiniteTrialsLemmas`, `UniqueGames_Foundations_PinskerLemmas`, `UniqueGames_Foundations_SamplingLemmas`, `UniqueGames_Foundations_ValueLemmas`, `UniqueGames_Games_FactorizationLemmas`, `UniqueGames_Machines_MachineCeilingPower`, `UniqueGames_Machines_MachineCompositionLemmas`, `UniqueGames_Machines_MachineCopy`, `UniqueGames_Machines_MachineDrain`, `UniqueGames_Machines_MachineFiniteAlphabet`, `UniqueGames_Machines_MachineSubroutineLemmas`.
--
--   **Imports.** It imports the published bundle `Def_PerfectCompleteness`; the bundles `OAIQ252P000` and `OAIQ252P001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ252P007`, `OAIQ252P008`, `OAIQ252P009`, `OAIQ252P010` and `OAIQ252P011`; the statements `OAI.PerfectCompleteness.BucketQuotientAgreement.agreement_eq_nonzeroAgreement` and `OAI.PerfectCompleteness.BucketQuotientAgreement.directionCollision_eq`.
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

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_BilinearGramCompressionLemmas
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.TensorCosetEvaluation

noncomputable section

open scoped TensorProduct

section GeneralField

variable {𝕜 U H : Type*} [Field 𝕜]
  [AddCommGroup U] [Module 𝕜 U] [AddCommGroup H] [Module 𝕜 H]

@[simp] theorem pureFrequency_tmul (a : Module.Dual 𝕜 U)
    (q : Module.Dual 𝕜 H) (u : U) (h : H) :
    pureFrequency a q (u ⊗ₜ[𝕜] h) = a u * q h := by
  simp only [pureFrequency, TensorProduct.lift.tmul, LinearMap.smulRight_apply,
    LinearMap.smul_apply, smul_eq_mul]

@[simp] theorem scalarRestriction_zero (u : U) :
    scalarRestriction (0 : Module.Dual 𝕜 (U ⊗[𝕜] H)) u = 0 := by
  apply LinearMap.ext
  intro h
  rfl

@[simp] theorem scalarRestriction_add (Φ Ψ : Module.Dual 𝕜 (U ⊗[𝕜] H))
    (u : U) : scalarRestriction (Φ + Ψ) u = scalarRestriction Φ u + scalarRestriction Ψ u := by
  apply LinearMap.ext
  intro h
  rfl

@[simp] theorem scalarRestriction_sub (Φ Ψ : Module.Dual 𝕜 (U ⊗[𝕜] H))
    (u : U) : scalarRestriction (Φ - Ψ) u = scalarRestriction Φ u - scalarRestriction Ψ u := by
  apply LinearMap.ext
  intro h
  rfl

@[simp] theorem scalarRestriction_smul (c : 𝕜) (Φ : Module.Dual 𝕜 (U ⊗[𝕜] H))
    (u : U) : scalarRestriction (c • Φ) u = c • scalarRestriction Φ u := by
  apply LinearMap.ext
  intro h
  rfl

@[simp] theorem scalarRestriction_pure (a : Module.Dual 𝕜 U)
    (q : Module.Dual 𝕜 H) (u : U) :
    scalarRestriction (pureFrequency a q) u = a u • q := by
  apply LinearMap.ext
  intro h
  simp only [scalarRestriction_apply, pureFrequency_tmul,
    LinearMap.smul_apply, smul_eq_mul]

end GeneralField

end
end PerfectCompleteness.TensorCosetEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_PartitionsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.PointwiseSpaces

variable {X Y Z : Type*}

variable {𝕜 : Type*} [Field 𝕜]

theorem pullback_injective (r : X → Y) (hr : Function.Surjective r) :
    Function.Injective (pullback 𝕜 r) := by
  intro f g h
  funext y
  obtain ⟨x, rfl⟩ := hr y
  exact congrFun h x

theorem le_squareSpace (H : Submodule 𝕜 (X → 𝕜)) (hone : (1 : X → 𝕜) ∈ H) :
    H ≤ squareSpace H := by
  intro f hf
  simpa only [mul_one] using mul_mem_squareSpace H hf hone

theorem one_mem_squareSpace (H : Submodule 𝕜 (X → 𝕜))
    (hone : (1 : X → 𝕜) ∈ H) : (1 : X → 𝕜) ∈ squareSpace H :=
  le_squareSpace H hone hone

theorem squareSpace_map_pullback (r : X → Y) (H : Submodule 𝕜 (Y → 𝕜)) :
    (squareSpace H).map (pullback 𝕜 r) = squareSpace (H.map (pullback 𝕜 r)) := by
  apply le_antisymm
  · exact squareSpace_pullback_le r H _ le_rfl
  · apply Submodule.span_le.mpr
    rintro u ⟨f, hf, g, hg, rfl⟩
    obtain ⟨f', hf', rfl⟩ := Submodule.mem_map.mp hf
    obtain ⟨g', hg', rfl⟩ := Submodule.mem_map.mp hg
    exact Submodule.mem_map.mpr ⟨f' * g', mul_mem_squareSpace H hf' hg', rfl⟩

section Children

variable {J : Type*} {D E : J → Type*}

theorem child_square_le (r : ∀ i, X → D i)
    (H : ∀ i, Submodule 𝕜 (D i → 𝕜)) (i : J) :
    (squareSpace (H i)).map (pullback 𝕜 (r i)) ≤ childSpace r H :=
  le_iSup (fun j => (squareSpace (H j)).map (pullback 𝕜 (r j))) i

theorem child_le (r : ∀ i, X → D i)
    (H : ∀ i, Submodule 𝕜 (D i → 𝕜)) (i : J)
    (hone : (1 : D i → 𝕜) ∈ H i) :
    (H i).map (pullback 𝕜 (r i)) ≤ childSpace r H := by
  intro f hf
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hf
  exact child_square_le r H i
    (Submodule.mem_map_of_mem (le_squareSpace (H i) hone hg))

theorem one_mem_childSpace_of_child (r : ∀ i, X → D i)
    (H : ∀ i, Submodule 𝕜 (D i → 𝕜)) (i : J)
    (hone : (1 : D i → 𝕜) ∈ H i) : (1 : X → 𝕜) ∈ childSpace r H := by
  have h : pullback 𝕜 (r i) (1 : D i → 𝕜) ∈ childSpace r H :=
    child_square_le r H i
      (Submodule.mem_map_of_mem (one_mem_squareSpace (H i) hone))
  simpa only [pullback_one] using h

end Children

end PerfectCompleteness.PointwiseSpaces

end

section

namespace PerfectCompleteness.ProductReduction

variable {I : Type*} {X R W : I → Type*} {Y : Type*}

theorem productMap_surjective (r : ∀ i, X i → R i)
    (hr : ∀ i, Function.Surjective (r i)) :
    Function.Surjective (productMap r) := by
  intro z
  refine ⟨fun i => (hr i (z i)).choose, ?_⟩
  funext i
  exact (hr i (z i)).choose_spec

theorem constant_on_product_fibers [Finite I]
    (r : ∀ i, X i → R i) (f : (∀ i, X i) → Y)
    (hf : CoordinateInvariant r f) {x x' : ∀ i, X i}
    (h : productMap r x = productMap r x') : f x = f x' := by
  classical
  let : Fintype I := Fintype.ofFinite I
  have hreplace : ∀ s : Finset I, f (s.piecewise x' x) = f x := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp only [Finset.piecewise_empty]
    | @insert i s hi ih =>
      have hstep : f ((insert i s).piecewise x' x) = f (s.piecewise x' x) := by
        apply hf i
        · intro j hji
          exact Finset.piecewise_insert_of_ne s x' x hji
        · simp only [Finset.piecewise_insert_self,
            Finset.piecewise_eq_of_notMem s x' x hi]
          exact (congrFun h i).symm
      exact hstep.trans ih
  simpa only [Finset.piecewise_univ] using (hreplace Finset.univ).symm

end PerfectCompleteness.ProductReduction

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_RecursiveSpaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.RecursiveSpaces

open PointwiseSpaces

universe u v w

instance slotsFintype (branch : Nat → Nat) (n : Nat) : Fintype (Slots branch n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
      letI : Fintype (Slots branch n) := ih
      exact inferInstanceAs (Fintype (Fin (branch n) × Slots branch n))

instance slotsDecidableEq (branch : Nat → Nat) (n : Nat) :
    DecidableEq (Slots branch n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ n ih =>
      letI : DecidableEq (Slots branch n) := ih
      exact inferInstanceAs (DecidableEq (Fin (branch n) × Slots branch n))

variable {branch : Nat → Nat} {n : Nat}

theorem childRestriction_surjective (A : Slots branch (n + 1) → Type u)
    (hnonempty : ∀ s, Nonempty (A s)) (i : Fin (branch n)) :
    Function.Surjective (childRestriction A i) := by
  classical
  intro y
  let base : ∀ j : Fin (branch n), Assignment (childFamily A j) :=
    fun j s => Classical.choice (hnonempty (j, s))
  refine ⟨fun s => Function.update base i y s.1 s.2, ?_⟩
  funext s
  simp only [childRestriction, Function.update_self]

variable {𝕜 : Type w} [Field 𝕜]

theorem one_mem_space (branch : Nat → Nat) :
    ∀ (n : Nat) (A : Slots branch n → Type u),
      (∀ k < n, 0 < branch k) → (1 : Assignment A → 𝕜) ∈ space 𝕜 branch n A := by
  intro n
  induction n with
  | zero =>
      intro A _
      exact Submodule.mem_top
  | succ n ih =>
      intro A hbranch
      let i : Fin (branch n) := ⟨0, hbranch n (Nat.lt_succ_self n)⟩
      apply one_mem_childSpace_of_child (childRestriction A)
        (fun j => space 𝕜 branch n (childFamily A j)) i
      exact ih (childFamily A i)
        (fun k hk => hbranch k (Nat.lt_trans hk (Nat.lt_succ_self n)))

theorem child_square_le_space (A : Slots branch (n + 1) → Type u)
    (i : Fin (branch n)) :
    (squareSpace (space 𝕜 branch n (childFamily A i))).map
        (pullback 𝕜 (childRestriction A i)) ≤ space 𝕜 branch (n + 1) A :=
  child_square_le (childRestriction A) (fun j => space 𝕜 branch n (childFamily A j)) i

theorem child_le_space (A : Slots branch (n + 1) → Type u)
    (i : Fin (branch n)) (hbranch : ∀ k < n, 0 < branch k) :
    (space 𝕜 branch n (childFamily A i)).map
        (pullback 𝕜 (childRestriction A i)) ≤ space 𝕜 branch (n + 1) A :=
  child_le (childRestriction A) (fun j => space 𝕜 branch n (childFamily A j)) i
    (one_mem_space branch n (childFamily A i) hbranch)

end PerfectCompleteness.RecursiveSpaces

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_FiniteTrialsLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finite two-player games with actual joint question distributions.

An answer function receives only its own player's question. In a repeated game,
that question is the entire tuple, so a repeated strategy need not act separately
on coordinates. The predicate may reject invalid answers depending on questions.
All probabilities below are actual finite sums of real weights.
-/

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators

noncomputable section

namespace FiniteDistribution

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

/-- Pushforward counts all preimages, including collisions. -/
def pushforward (μ : FiniteDistribution Ω) (f : Ω → Γ) : FiniteDistribution Γ := by
  classical
  exact
    { weight := fun y => ∑ x, if f x = y then μ.weight x else 0
      nonnegative := fun y => Finset.sum_nonneg fun x _ => by
        split
        · exact μ.nonnegative x
        · exact le_rfl
      normalized := by
        rw [Finset.sum_comm]
        simpa using μ.normalized }

theorem probability_pushforward (μ : FiniteDistribution Ω) (f : Ω → Γ)
    (event : Γ → Bool) :
    (μ.pushforward f).probability event = μ.probability (fun x => event (f x)) := by
  classical
  simp only [probability, pushforward]
  calc
    _ = ∑ y, ∑ x, if f x = y then (if event y then μ.weight x else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : event y = true <;> simp [hy]
    _ = _ := by rw [Finset.sum_comm]; simp

end FiniteDistribution

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

def wins (G : Game Q₁ Q₂ A₁ A₂) (strategy : Strategy Q₁ Q₂ A₁ A₂)
    (questions : Q₁ × Q₂) : Bool :=
  G.accepts questions.1 questions.2 (strategy.1 questions.1) (strategy.2 questions.2)

def success (G : Game Q₁ Q₂ A₁ A₂) (strategy : Strategy Q₁ Q₂ A₁ A₂) : ℝ :=
  G.questions.probability (G.wins strategy)

@[simp] theorem repetition_accepts_iff (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (x : Fin n → Q₁) (y : Fin n → Q₂) (a : Fin n → A₁) (b : Fin n → A₂) :
    (G.repetition n).accepts x y a b = true ↔
      ∀ i, G.accepts (x i) (y i) (a i) (b i) = true := by
  classical
  simp [repetition]

/-- One coordinate's success may depend on the entire local question tuples. -/
def coordinateWin (G : Game Q₁ Q₂ A₁ A₂) {n : Nat}
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (coordinate : Fin n) (questions : (Fin n → Q₁) × (Fin n → Q₂)) : Bool :=
  G.accepts (questions.1 coordinate) (questions.2 coordinate)
    (strategy.1 questions.1 coordinate) (strategy.2 questions.2 coordinate)

def selectedWins (G : Game Q₁ Q₂ A₁ A₂) {n : Nat}
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (questions : (Fin n → Q₁) × (Fin n → Q₂)) : Bool := by
  classical
  exact decide (∀ i ∈ selected, G.coordinateWin strategy i questions = true)

@[simp] theorem selectedWins_empty (G : Game Q₁ Q₂ A₁ A₂) {n : Nat}
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (questions : (Fin n → Q₁) × (Fin n → Q₂)) :
    G.selectedWins strategy ∅ questions = true := by
  simp [selectedWins]

end Game

end

end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_Conditioning
attribute [-simp] _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
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

def selectedSuccess (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) : ℝ :=
  (G.repetition n).questions.probability (G.selectedWins strategy selected)

@[simp] theorem selectedSuccess_empty (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    G.selectedSuccess strategy ∅ = 1 := by
  have h : G.selectedWins strategy ∅ = fun _ => true :=
    funext (G.selectedWins_empty strategy)
  rw [selectedSuccess, h, FiniteDistribution.probability_true]

end Game

end

end UniqueGamesTheorem.Foundations.Games

end

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

theorem eq_of_weight_eq {μ ν : FiniteDistribution Ω}
    (h : ∀ x, μ.weight x = ν.weight x) : μ = ν := by
  cases μ with
  | mk w hw hs =>
    cases ν with
    | mk w' hw' hs' =>
      have he : w = w' := funext h
      cases he
      rfl

def product (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ) :
    FiniteDistribution (Ω × Γ) where
  weight x := μ.weight x.1 * ν.weight x.2
  nonnegative x := mul_nonneg (μ.nonnegative _) (ν.nonnegative _)
  normalized := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ν.normalized, mul_one]
    exact μ.normalized

end FiniteDistribution

end
end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_SamplingLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Exact finite sampling laws used to identify verifier distributions with repeated
game question laws. These are finite sum/product identities, not independence
assumptions about an unspecified distribution.
-/

namespace UniqueGamesTheorem.Foundations.Games.FiniteDistribution
open scoped BigOperators
noncomputable section

def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteDistribution Ω where
  weight _ := 1 / (Fintype.card Ω : ℝ)
  nonnegative _ := div_nonneg zero_le_one (Nat.cast_nonneg _)
  normalized := by
    have hn : (Fintype.card Ω : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_div]
    exact mul_inv_cancel₀ hn

end
end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_RecursiveSpaceEquivLemmas
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ReducedPartition

variable {X W R Y : Type*}

@[simp] theorem output_label (r : X → R) (f : X → Y)
    (hf : ConstantOnFibers r f) (x : X) : output r f (label r f x) = f x :=
  ((mem_iff r f hf (label r f x) x).1 (self_mem_fiber r f x)).symm

theorem output_injective (r : X → R) (f : X → Y) :
    Function.Injective (output r f) := by
  intro P Q h
  apply Subtype.ext
  calc
    P.val = fiber r f (representative r f P) := (representative_spec r f P).symm
    _ = fiber r f (representative r f Q) := fiber_eq_of_output_eq r f h
    _ = Q.val := representative_spec r f Q

@[simp] theorem label_representative (r : X → R) (f : X → Y) (P : Part r f) :
    label r f (representative r f P) = P := by
  apply Subtype.ext
  exact representative_spec r f P

theorem label_surjective (r : X → R) (f : X → Y) :
    Function.Surjective (label r f) := by
  intro P
  exact ⟨representative r f P, label_representative r f P⟩

instance instFinitePart [Finite X] (r : X → R) (f : X → Y) : Finite (Part r f) :=
  Finite.of_surjective (label r f) (label_surjective r f)

theorem output_eq_of_shared_part
    (π : X → W) (rX : X → R) (rW : W → R) (fX : X → Y) (fW : W → Y)
    (hr : ∀ x, rX x = rW (π x)) (hf : ∀ x, fX x = fW (π x))
    (hW : ConstantOnFibers rW fW)
    (P : Part rX fX) (Q : Part rW fW) (hPQ : P.val = Q.val) :
    output rX fX P = output rW fW Q := by
  let x := representative rX fX P
  have hx : rX x ∈ P.val := representative_mem rX fX P
  have hmem : rW (π x) ∈ Q.val := by
    rw [← hr x, ← hPQ]
    exact hx
  change fX x = output rW fW Q
  exact (hf x).trans ((mem_iff rW fW hW Q (π x)).1 hmem)

end PerfectCompleteness.ReducedPartition

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_PinskerLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Target

def Formula.Satisfiable (formula : Formula) : Prop :=
  ∃ assignment : Fin formula.variables → Bool,
    ∀ clause ∈ formula.clauses, clause.eval assignment = true

end UniqueGamesTheorem.Foundations.Target

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceClause
attribute [-instance] _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.clause_eval_extend _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.clause_eval_restrict _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceClause

open UniqueGamesTheorem.Foundations.Target

structure NormalizedClause («variables» : Nat) where
  clause : Clause «variables»
  distinct : ∀ i j : Fin 3,
    clause[i].variableIndex = clause[j].variableIndex → i = j

def NormalizedClause.variable {n : Nat} (c : NormalizedClause n) (i : Fin 3) : Fin n :=
  c.clause[i].variableIndex

def NormalizedClause.signs {n : Nat} (c : NormalizedClause n) : Triple :=
  (c.clause[0].positive, c.clause[1].positive, c.clause[2].positive)

def NormalizedClause.restrict {n : Nat} (c : NormalizedClause n)
    (assignment : Fin n → Bool) : Triple :=
  (assignment (c.variable 0), assignment (c.variable 1), assignment (c.variable 2))

@[simp] theorem localEval_restrict {n : Nat} (c : NormalizedClause n)
    (assignment : Fin n → Bool) :
    localEval c.signs (c.restrict assignment) = c.clause.eval assignment := by
  rfl

def occurrenceVariable {n m : Nat} (clauses : Fin m → NormalizedClause n)
    (e : Occurrence m) : Fin n :=
  (clauses e.1).variable e.2

end PerfectCompleteness.SourceClause

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_ClauseSupportLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalLabelEncoding.labelEmbedding_val _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ClauseSupport

open SourceClause

variable {C C' D E Y Z : Type*}

theorem clauseMode_bit {signs : Triple} (f : C → Answer signs → Y)
    (hused : ¬ Unused f) (i : Fin 3) (hi : Reducible f i) : clauseMode f = .bit i := by
  classical
  have hex : ∃ j, Reducible f j := ⟨i, hi⟩
  simp only [clauseMode, ite_eq_right hused, dite_eq_left hex]
  exact congrArg Mode.bit (used_reduction_unique f hused hex.choose_spec hi)

theorem clauseMode_eq_of_predicates {signs : Triple}
    (f : C → Answer signs → Y) (g : C' → Answer signs → Z)
    (hu : Unused f ↔ Unused g) (hr : ∀ i, Reducible f i ↔ Reducible g i) :
    clauseMode f = clauseMode g := by
  classical
  by_cases hf : Unused f
  · rw [clauseMode_unused f hf, clauseMode_unused g (hu.1 hf)]
  · have hg : ¬ Unused g := fun h => hf (hu.2 h)
    by_cases hred : ∃ i, Reducible f i
    · obtain ⟨i, hi⟩ := hred
      rw [clauseMode_bit f hf i hi, clauseMode_bit g hg i ((hr i).1 hi)]
    · have hn : ¬ ∃ i, Reducible g i := by
        rintro ⟨i, hi⟩
        exact hred ⟨i, (hr i).2 hi⟩
      rw [clauseMode_full f hf hred, clauseMode_full g hg hn]

theorem clauseMode_kernel_invariant {signs : Triple}
    (f : C → Answer signs → Y) (g : C → Answer signs → Z)
    (hkernel : ∀ c u v, f c u = f c v ↔ g c u = g c v) :
    clauseMode f = clauseMode g :=
  clauseMode_eq_of_predicates f g (unused_kernel_invariant f g hkernel)
    (fun i => factors_kernel_invariant f g (coordinate i) hkernel)

theorem unprojected_mode_eq {signs : Triple} (f : C → Answer signs → Y)
    (context : C' → C) (hcontext : Function.Surjective context) :
    clauseMode (pull f context id) = clauseMode f := by
  apply clauseMode_eq_of_predicates
  · exact unused_pull_iff f context id hcontext Function.surjective_id
  · intro i
    exact factors_pull_iff f context id (coordinate i) hcontext Function.surjective_id

theorem clauseReduction_sound {signs : Triple} (f : C → Answer signs → Y)
    (c : C) (u v : Answer signs) (h : clauseReduction f u = clauseReduction f v) :
    f c u = f c v := by
  classical
  by_cases hu : Unused f
  · exact hu c u v
  · by_cases hr : ∃ i, Reducible f i
    · obtain ⟨i, hi⟩ := hr
      have hm := clauseMode_bit f hu i hi
      have hc : coordinate i u = coordinate i v := by
        simpa only [clauseReduction, hm, reduceByMode, ReducedValue.bit.injEq] using h
      exact hi c u v hc
    · have hm := clauseMode_full f hu hr
      have hv : u.val = v.val := by
        simpa only [clauseReduction, hm, reduceByMode, ReducedValue.full.injEq] using h
      exact congrArg (f c) (Subtype.ext hv)

theorem unprojected_clause_reduction_eq {signs : Triple} (f : C → Answer signs → Y)
    (context : C' → C) (hcontext : Function.Surjective context) (u : Answer signs) :
    clauseReduction (pull f context id) u = clauseReduction f u := by
  simp only [clauseReduction, unprojected_mode_eq f context hcontext]

theorem projected_reduction_eq {signs : Triple} (f : C → Bool → Y)
    (context : C' → C) (hcontext : Function.Surjective context)
    (i : Fin 3) (u : Answer signs) :
    clauseReduction (pull f context (coordinate i)) u = bitReduction f (coordinate i u) := by
  classical
  have hu := projected_unused_iff (signs := signs) f context hcontext i
  by_cases hf : Unused f
  · simp [clauseReduction, clauseMode_unused _ (hu.2 hf), reduceByMode, bitReduction, hf]
  · have hp : ¬ Unused (pull f context (coordinate (signs := signs) i)) :=
      fun h => hf (hu.1 h)
    rw [clauseReduction, clauseMode_bit _ hp i (projected_reducible f context i)]
    simp [reduceByMode, bitReduction, hf]

end PerfectCompleteness.ClauseSupport

end

section

namespace PerfectCompleteness.MixedSupport

open ClauseSupport

variable {I C C' Y : Type*}

def projectionMap {slots projected : I → Slot}
    (p : ∀ i, Projection (slots i) (projected i)) :
    Assignment slots → Assignment projected :=
  ProductReduction.productMap (fun i => (p i).map)

theorem projectionMap_surjective {slots projected : I → Slot}
    (p : ∀ i, Projection (slots i) (projected i)) :
    Function.Surjective (projectionMap p) :=
  ProductReduction.productMap_surjective _ (fun i => (p i).surjective)

variable [DecidableEq I]

theorem projectionMap_update {slots projected : I → Slot}
    (p : ∀ i, Projection (slots i) (projected i))
    (x : Assignment slots) (i : I) (u : (slots i).Domain) :
    projectionMap p (Function.update x i u) =
      Function.update (projectionMap p x) i ((p i).map u) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [projectionMap, ProductReduction.productMap]
  · simp [projectionMap, ProductReduction.productMap, Function.update_of_ne hji]

theorem sectionFunction_pullback {slots projected : I → Slot}
    (p : ∀ i, Projection (slots i) (projected i))
    (f : Assignment projected → Y) (i : I) :
    sectionFunction slots (f ∘ projectionMap p) i =
      pull (sectionFunction projected f i) (projectionMap p) (p i).map := by
  funext context u
  exact congrArg f (projectionMap_update p context i u)

theorem localReduction_sound (s : Slot) (f : C → s.Domain → Y)
    (c : C) (u v : s.Domain) (h : localReduction s f u = localReduction s f v) :
    f c u = f c v := by
  cases s with
  | clause occurrence variableIDs signs => exact clauseReduction_sound f c u v h
  | bit variableID => exact bitReduction_sound f c u v h

theorem localReduction_projection {s t : Slot} (p : Projection s t)
    (f : C → t.Domain → Y) (context : C' → C)
    (hcontext : Function.Surjective context) (u : s.Domain) :
    localReduction s (pull f context p.map) u = localReduction t f (p.map u) := by
  cases p with
  | keep s =>
    cases s with
    | clause occurrence variableIDs signs =>
      exact unprojected_clause_reduction_eq f context hcontext u
    | bit variableID => exact unprojected_bit_reduction_eq f context hcontext u
  | select occurrence variableIDs signs i =>
    exact projected_reduction_eq f context hcontext i u

noncomputable def reduction (slots : I → Slot) (f : Assignment slots → Y) :
    Assignment slots → I → ReducedValue :=
  ProductReduction.productMap (coordinateReduction slots f)

theorem reduction_projection {slots projected : I → Slot}
    (p : ∀ i, Projection (slots i) (projected i))
    (f : Assignment projected → Y) (x : Assignment slots) :
    reduction slots (f ∘ projectionMap p) x = reduction projected f (projectionMap p x) := by
  funext i
  change localReduction (slots i) (sectionFunction slots (f ∘ projectionMap p) i) (x i) = _
  rw [sectionFunction_pullback]
  exact localReduction_projection (p i) (sectionFunction projected f i)
    (projectionMap p) (projectionMap_surjective p) (x i)

theorem coordinateInvariant (slots : I → Slot) (f : Assignment slots → Y) :
    ProductReduction.CoordinateInvariant (coordinateReduction slots f) f := by
  apply ProductReduction.coordinateInvariant_of_update
  intro i x u h
  have hs := localReduction_sound (slots i) (sectionFunction slots f i) x (x i) u h
  simpa only [sectionFunction, Function.update_eq_self] using hs

theorem constant_on_reduction_fibers [Finite I]
    (slots : I → Slot) (f : Assignment slots → Y) {x x' : Assignment slots}
    (h : reduction slots f x = reduction slots f x') : f x = f x' :=
  ProductReduction.constant_on_product_fibers _ f (coordinateInvariant slots f) h

end PerfectCompleteness.MixedSupport

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_CanonicalKeys
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalLabelEncoding.labelEmbedding_val _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CanonicalKeys

open ClauseSupport MixedSupport

variable {n : Nat} {Y : Type*}

noncomputable def partition (slots : Fin n → Slot) (f : Assignment slots → Y) :
    Set (Set (Fin n → ReducedValue)) :=
  ReducedPartition.parts (reduction slots f) f

noncomputable def key (side : Side) (slots : Fin n → Slot)
    (f : Assignment slots → Y) : Key n :=
  ⟨side, retainedKeys slots f, partition slots f⟩

theorem constantOnFibers (slots : Fin n → Slot) (f : Assignment slots → Y) :
    ReducedPartition.ConstantOnFibers (reduction slots f) f := by
  intro x x' h
  exact constant_on_reduction_fibers slots f h

theorem partition_projection {slots projected : Fin n → Slot}
    (p : ∀ i, Projection (slots i) (projected i)) (f : Assignment projected → Y) :
    partition slots (f ∘ projectionMap p) = partition projected f := by
  exact ReducedPartition.parts_eq_of_pullback
    (projectionMap p) (projectionMap_surjective p)
    (reduction slots (f ∘ projectionMap p)) (reduction projected f)
    (f ∘ projectionMap p) f (reduction_projection p f) (fun _ => rfl)

abbrev Label (slots : Fin n → Slot) (f : Assignment slots → Y) :=
  ReducedPartition.Part (reduction slots f) f

noncomputable def evaluateLabel (slots : Fin n → Slot) (f : Assignment slots → Y)
    (x : Assignment slots) : Label slots f :=
  ReducedPartition.label (reduction slots f) f x

noncomputable def restore (slots : Fin n → Slot) (f : Assignment slots → Y)
    (P : Label slots f) : Y :=
  ReducedPartition.output (reduction slots f) f P

@[simp] theorem restore_evaluateLabel (slots : Fin n → Slot)
    (f : Assignment slots → Y) (x : Assignment slots) :
    restore slots f (evaluateLabel slots f x) = f x :=
  ReducedPartition.output_label (reduction slots f) f (constantOnFibers slots f) x

theorem restore_injective (slots : Fin n → Slot) (f : Assignment slots → Y) :
    Function.Injective (restore slots f) :=
  ReducedPartition.output_injective (reduction slots f) f

noncomputable def transportLabel {slots projected : Fin n → Slot}
    (p : ∀ i, Projection (slots i) (projected i)) (f : Assignment projected → Y)
    (P : Label slots (f ∘ projectionMap p)) : Label projected f :=
  ⟨P.val, by
    change P.val ∈ partition projected f
    rw [← partition_projection p f]
    exact P.property⟩

end PerfectCompleteness.CanonicalKeys

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_CanonicalEdgesLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalLabelEncoding.labelEmbedding_val _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CanonicalEdges

open MixedSupport CanonicalKeys

variable {n : Nat} {Y Z : Type*}

noncomputable def coarsen (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (P : Label slots f) : Label slots (p ∘ f) :=
  evaluateLabel slots (p ∘ f) (ReducedPartition.representative (reduction slots f) f P)

@[simp] theorem restore_coarsen (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (P : Label slots f) :
    restore slots (p ∘ f) (coarsen slots f p P) = p (restore slots f P) := by
  exact restore_evaluateLabel slots (p ∘ f)
    (ReducedPartition.representative (reduction slots f) f P)

theorem coarsen_eq_iff (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (P : Label slots f) (Q : Label slots (p ∘ f)) :
    coarsen slots f p P = Q ↔ p (restore slots f P) = restore slots (p ∘ f) Q := by
  constructor
  · intro h
    rw [← restore_coarsen slots f p P, h]
  · intro h
    apply restore_injective slots (p ∘ f)
    exact (restore_coarsen slots f p P).trans h

@[simp] theorem coarsen_evaluateLabel (slots : Fin n → Slot)
    (f : Assignment slots → Y) (p : Y → Z) (x : Assignment slots) :
    coarsen slots f p (evaluateLabel slots f x) = evaluateLabel slots (p ∘ f) x := by
  apply (coarsen_eq_iff slots f p _ _).2
  rw [restore_evaluateLabel, restore_evaluateLabel]
  rfl

theorem card_coarsen_fiber_le [Finite Y] (slots : Fin n → Slot)
    (f : Assignment slots → Y) (p : Y → Z) (Q : Label slots (p ∘ f)) :
    Nat.card {P : Label slots f // coarsen slots f p P = Q} ≤
      Nat.card {y : Y // p y = restore slots (p ∘ f) Q} := by
  let restoreFiber : {P : Label slots f // coarsen slots f p P = Q} →
      {y : Y // p y = restore slots (p ∘ f) Q} :=
    fun P => ⟨restore slots f P.val, (coarsen_eq_iff slots f p P.val Q).1 P.property⟩
  apply Nat.card_le_card_of_injective restoreFiber
  intro P P' h
  apply Subtype.ext
  apply restore_injective slots f
  exact congrArg Subtype.val h

theorem coarsen_at_most_two [Finite Y] (slots : Fin n → Slot)
    (f : Assignment slots → Y) (p : Y → Z)
    (hp : ∀ z, Nat.card {y : Y // p y = z} ≤ 2) (Q : Label slots (p ∘ f)) :
    Nat.card {P : Label slots f // coarsen slots f p P = Q} ≤ 2 :=
  (card_coarsen_fiber_le slots f p Q).trans (hp (restore slots (p ∘ f) Q))

end PerfectCompleteness.CanonicalEdges

end

section

namespace PerfectCompleteness.CanonicalKeyShape

open ClauseSupport MixedSupport
open scoped Classical

noncomputable section

def erase : Slot → Shape
  | .clause _ _ signs => .clause signs
  | .bit _ => .bit

def dummy : Shape → Slot
  | .clause signs => .clause 0 (fun _ => 0) signs
  | .bit => .bit 0

@[simp] theorem erase_dummy (s : Shape) : erase (dummy s) = s := by
  cases s <;> rfl

def domainEquiv (s : Slot) : s.Domain ≃ (dummy (erase s)).Domain := by
  cases s <;> exact Equiv.refl _

instance dummyDomainFintype (s : Shape) : Fintype (dummy s).Domain := by
  cases s <;> dsimp [dummy, Slot.Domain] <;> infer_instance

def shape {I : Type*} (slots : I → Slot) : I → Shape := fun i => erase (slots i)

def dummySlots {I : Type*} (shapes : I → Shape) : I → Slot := fun i => dummy (shapes i)

instance dummyAssignmentFintype {I : Type*} [Fintype I] [DecidableEq I]
    (shapes : I → Shape) : Fintype (Assignment (dummySlots shapes)) := by
  change Fintype (∀ i : I, (dummy (shapes i)).Domain)
  infer_instance

def assignmentEquiv {I : Type*} (slots : I → Slot) :
    Assignment slots ≃ Assignment (dummySlots (shape slots)) where
  toFun x i := domainEquiv (slots i) (x i)
  invFun x i := (domainEquiv (slots i)).symm (x i)
  left_inv x := by funext i; exact (domainEquiv (slots i)).symm_apply_apply (x i)
  right_inv x := by funext i; exact (domainEquiv (slots i)).apply_symm_apply (x i)

@[simp] theorem assignmentEquiv_apply {I : Type*} (slots : I → Slot)
    (x : Assignment slots) (i : I) :
    assignmentEquiv slots x i = domainEquiv (slots i) (x i) := rfl

def transport {I Y : Type*} (slots : I → Slot) (f : Assignment slots → Y) :
    Assignment (dummySlots (shape slots)) → Y := f ∘ (assignmentEquiv slots).symm

@[simp] theorem transport_apply {I Y : Type*} (slots : I → Slot)
    (f : Assignment slots → Y) (x : Assignment slots) :
    transport slots f (assignmentEquiv slots x) = f x := by
  simp only [transport, Function.comp_apply, Equiv.symm_apply_apply]

theorem assignmentEquiv_update {I : Type*} [DecidableEq I]
    (slots : I → Slot) (x : Assignment slots) (i : I) (u : (slots i).Domain) :
    assignmentEquiv slots (Function.update x i u) =
      Function.update (assignmentEquiv slots x) i (domainEquiv (slots i) u) := by
  funext j
  exact Function.apply_update (fun i => domainEquiv (slots i)) x i u j

theorem sectionFunction_erasure {I Y : Type*} [DecidableEq I]
    (slots : I → Slot) (f : Assignment slots → Y) (i : I) :
    sectionFunction slots f i =
      pull (sectionFunction (dummySlots (shape slots)) (transport slots f) i)
        (assignmentEquiv slots) (domainEquiv (slots i)) := by
  funext context u
  change f (Function.update context i u) =
    f ((assignmentEquiv slots).symm
      (Function.update (assignmentEquiv slots context) i (domainEquiv (slots i) u)))
  rw [← assignmentEquiv_update, Equiv.symm_apply_apply]

theorem localReduction_erasure {C C' Y : Type*} (s : Slot)
    (f : C → (dummy (erase s)).Domain → Y) (context : C' → C)
    (hcontext : Function.Surjective context) (u : s.Domain) :
    localReduction s (pull f context (domainEquiv s)) u =
      localReduction (dummy (erase s)) f (domainEquiv s u) := by
  cases s with
  | clause occurrence variableIDs signs =>
      exact unprojected_clause_reduction_eq f context hcontext u
  | bit variableID =>
      exact unprojected_bit_reduction_eq f context hcontext u

theorem reduction_erasure {I Y : Type*} [DecidableEq I]
    (slots : I → Slot) (f : Assignment slots → Y) (x : Assignment slots) :
    reduction slots f x =
      reduction (dummySlots (shape slots)) (transport slots f) (assignmentEquiv slots x) := by
  funext i
  change localReduction (slots i) (sectionFunction slots f i) (x i) = _
  rw [sectionFunction_erasure]
  exact localReduction_erasure (slots i)
    (sectionFunction (dummySlots (shape slots)) (transport slots f) i)
    (assignmentEquiv slots) (assignmentEquiv slots).surjective (x i)

theorem partition_erasure {n : Nat} {Y : Type*}
    (slots : Fin n → Slot) (f : Assignment slots → Y) :
    CanonicalKeys.partition slots f =
      CanonicalKeys.partition (dummySlots (shape slots)) (transport slots f) := by
  exact ReducedPartition.parts_eq_of_pullback (assignmentEquiv slots)
    (assignmentEquiv slots).surjective
    (reduction slots f) (reduction (dummySlots (shape slots)) (transport slots f))
    f (transport slots f) (reduction_erasure slots f)
    (fun x => (transport_apply slots f x).symm)

def mode {C Y : Type*} (s : Slot) : (C → s.Domain → Y) → SupportMode :=
  match s with
  | .clause _ _ _ => fun f =>
      match clauseMode f with
      | .dropped => .dropped
      | .bit i => .clauseBit i
      | .full => .full
  | .bit _ => fun f => if Unused f then .dropped else .bit

def recover : Slot → SupportMode → SlotKey
  | .clause _ variableIDs _, .clauseBit i => .bit (variableIDs i)
  | .clause occurrence _ signs, .full => .full occurrence signs
  | .bit variableID, .bit => .bit variableID
  | _, _ => .dropped

theorem localKey_recover {C Y : Type*} (s : Slot) (f : C → s.Domain → Y) :
    localKey s f = recover s (mode s f) := by
  cases s with
  | clause occurrence variableIDs signs =>
      cases hmode : clauseMode f <;>
        simp only [localKey, clauseKey, mode, hmode, recover]
  | bit variableID =>
      change C → Bool → Y at f
      change (if Unused f then SlotKey.dropped else SlotKey.bit variableID) =
        recover (.bit variableID) (if Unused f then SupportMode.dropped else SupportMode.bit)
      by_cases h : Unused f <;> simp only [h, ite_true, if_true, ite_false, if_false, recover]

theorem mode_erasure {C C' Y : Type*} (s : Slot)
    (f : C → (dummy (erase s)).Domain → Y) (context : C' → C)
    (hcontext : Function.Surjective context) :
    mode s (pull f context (domainEquiv s)) = mode (dummy (erase s)) f := by
  cases s with
  | clause occurrence variableIDs signs =>
      change C → Answer signs → Y at f
      change (match clauseMode (pull f context id) with
        | .dropped => SupportMode.dropped
        | .bit i => SupportMode.clauseBit i
        | .full => SupportMode.full) = _
      rw [unprojected_mode_eq f context hcontext]
      rfl
  | bit variableID =>
      change C → Bool → Y at f
      change (if Unused (pull f context id) then SupportMode.dropped else SupportMode.bit) =
        (if Unused f then SupportMode.dropped else SupportMode.bit)
      rw [unused_pull_iff f context id hcontext Function.surjective_id]

def modes {I Y : Type*} [DecidableEq I] (slots : I → Slot)
    (f : Assignment slots → Y) : I → SupportMode :=
  fun i => mode (slots i) (sectionFunction slots f i)

theorem modes_erasure {I Y : Type*} [DecidableEq I]
    (slots : I → Slot) (f : Assignment slots → Y) :
    modes slots f = modes (dummySlots (shape slots)) (transport slots f) := by
  funext i
  unfold modes
  rw [sectionFunction_erasure]
  exact mode_erasure (slots i)
    (sectionFunction (dummySlots (shape slots)) (transport slots f) i)
    (assignmentEquiv slots) (assignmentEquiv slots).surjective

theorem keyFields_recover {I Y : Type*} [DecidableEq I]
    (slots : I → Slot) (f : Assignment slots → Y) :
    keyFields slots f = fun i =>
      recover (slots i) (modes (dummySlots (shape slots)) (transport slots f) i) := by
  have hm := modes_erasure slots f
  funext i
  change localKey (slots i) (sectionFunction slots f i) = _
  rw [localKey_recover]
  change recover (slots i) (modes slots f i) = _
  rw [hm]

def retained {n : Nat} (slots : Fin n → Slot) (support : Fin n → SupportMode) :
    List (Fin n × SlotKey) :=
  ((List.finRange n).map (fun i => (i, recover (slots i) (support i)))).filter
    (fun entry => decide (entry.2 ≠ .dropped))

theorem retainedKeys_recover {n : Nat} {Y : Type*}
    (slots : Fin n → Slot) (f : Assignment slots → Y) :
    retainedKeys slots f =
      retained slots (modes (dummySlots (shape slots)) (transport slots f)) := by
  simp only [retainedKeys, keyFields_recover, retained]

abbrev Input (n k : Nat) :=
  Σ shapes : Fin n → Shape, Assignment (dummySlots shapes) → Fin k

instance inputFintype (n k : Nat) : Fintype (Input n k) := by
  unfold Input
  infer_instance

def input {n k : Nat} (slots : Fin n → Slot) (f : Assignment slots → Fin k) : Input n k :=
  ⟨shape slots, transport slots f⟩

def inputPartition {n k : Nat} (data : Input n k) :
    Set (Set (Fin n → ReducedValue)) :=
  CanonicalKeys.partition (dummySlots data.1) data.2

def inputModes {n k : Nat} (data : Input n k) : Fin n → SupportMode :=
  modes (dummySlots data.1) data.2

theorem inputPartition_eq {n k : Nat} (slots : Fin n → Slot)
    (f : Assignment slots → Fin k) :
    inputPartition (input slots f) = CanonicalKeys.partition slots f :=
  (partition_erasure slots f).symm

theorem inputModes_recover {n k : Nat} (slots : Fin n → Slot)
    (f : Assignment slots → Fin k) :
    retained slots (inputModes (input slots f)) = retainedKeys slots f :=
  (retainedKeys_recover slots f).symm

end
end PerfectCompleteness.CanonicalKeyShape

end

section

namespace PerfectCompleteness.SourceKeys

open SourceClause MixedSupport CanonicalKeys

variable {v m n : Nat} {I Y Z : Type*}

def slot (clauses : Fin m → NormalizedClause v) : Endpoint v m → Slot
  | .clause c => .clause c.val (fun i => ((clauses c).variable i).val) (clauses c).signs
  | .variable j => .bit j.val

inductive Step (clauses : Fin m → NormalizedClause v) :
    Endpoint v m → Endpoint v m → Type
  | keep (s : Endpoint v m) : Step clauses s s
  | select (c : Fin m) (position : Fin 3) :
      Step clauses (.clause c) (.variable ((clauses c).variable position))

def Step.projection {clauses : Fin m → NormalizedClause v}
    {s t : Endpoint v m} : Step clauses s t → Projection (slot clauses s) (slot clauses t)
  | .keep s => .keep (slot clauses s)
  | .select c i => .select c.val (fun j => ((clauses c).variable j).val) (clauses c).signs i

def endpointValue (clauses : Fin m → NormalizedClause v) (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true) :
    (s : Endpoint v m) → (slot clauses s).Domain
  | .clause c => ⟨(clauses c).restrict assignment, by
      apply (mem_satisfyingTriples (clauses c).signs _).2
      rw [localEval_restrict]
      exact hsat c⟩
  | .variable j => assignment j

theorem coordinate_restrict (c : NormalizedClause v) (assignment : Fin v → Bool)
    (i : Fin 3) : (c.restrict assignment).at i = assignment (c.variable i) := by
  refine Fin.cases (by rfl) (fun j => ?_) i
  refine Fin.cases (by rfl) (fun k => ?_) j
  have hk : k = 0 := Subsingleton.elim _ _
  subst k
  rfl

def realizingAssignment (clauses : Fin m → NormalizedClause v)
    (assignment : Fin v → Bool) (hsat : ∀ c, (clauses c).clause.eval assignment = true)
    (endpoints : I → Endpoint v m) : Assignment (slot clauses ∘ endpoints) :=
  fun i => endpointValue clauses assignment hsat (endpoints i)

end PerfectCompleteness.SourceKeys

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_FactorizationLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart
attribute [-simp] _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The actual single-coordinate dependency-breaking reveal distribution.
The tag records which endpoint of the question pair was revealed. -/

namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- Independently reveal either endpoint with probability one half. -/
def revealLaw (μ : FiniteDistribution (X × Y)) :
    FiniteDistribution ((X × Y) × (X ⊕ Y)) :=
  (μ.product (FiniteDistribution.uniform Bool)).pushforward
    (fun z => (z.1, revealEndpoint z.1 z.2))

def revealFirstLaw (μ : FiniteDistribution (X × Y)) :
    FiniteDistribution ((X ⊕ Y) × (X × Y)) :=
  (revealLaw μ).transport (Equiv.prodComm _ _)

omit [DecidableEq X] [DecidableEq Y] in
@[simp] theorem revealFirstLaw_weight (μ : FiniteDistribution (X × Y))
    (r : X ⊕ Y) (q : X × Y) :
    (revealFirstLaw μ).weight (r,q) = (revealLaw μ).weight (q,r) := rfl

end
end UniqueGamesTheorem.Foundations.Repetition

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

/-! Static concatenation of finitely many concrete subroutines on common
tapes. The labels are a finite disjoint sum; no runtime instruction counter
or list is placed in the machine state. The simulation theorem composes the
actual local traces with exactly their summed transition counts. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineFiniteSequence

open Turing MachineComposition

variable {Command : Type} (LocalLabel : Command → Type)

variable (main : ∀ command, LocalLabel command)
variable {K Λ σ : Type} {Γ : K → Type}

variable (localInstruction : ∀ command, (LocalLabel command → Λ) → Option Λ →
  LocalLabel command → TM2.Stmt Γ Λ σ)

variable {Data : Type} (result : Command → Data → Data) (cost : Command → Data → Nat)

variable [DecidableEq K]

/-- This generic composition lemma retains the local execution obligations.
Concrete callers discharge them with the rotor, comparison and row programs. -/
theorem trace (program : Λ → TM2.Stmt Γ Λ σ)
    (invariant : Data → Prop) (state : Data → σ) (tapes : Data → ∀ k, List (Γ k))
    (commands : List Command)
    (localInvariant : ∀ command ∈ commands, ∀ data, invariant data →
      invariant (result command data))
    (localTrace : ∀ command ∈ commands, ∀ (labels : LocalLabel command → Λ) (exit : Option Λ),
      (∀ l, program (labels l) = localInstruction command labels exit l) →
      ∀ data, invariant data →
      (advance (TM2.step program))^[cost command data]
        (some ⟨some (labels (main command)), state data, tapes data⟩) =
      some ⟨exit, state (result command data), tapes (result command data)⟩)
    (labels : Label LocalLabel commands → Λ) (exit : Option Λ)
    (atLabels : ∀ l, program (labels l) =
      instruction LocalLabel main localInstruction commands labels exit l)
    (data : Data) (valid : invariant data) :
    (advance (TM2.step program))^[steps result cost commands data]
      (some ⟨entry LocalLabel main commands labels exit, state data, tapes data⟩) =
    some ⟨exit, state (resultOf result commands data), tapes (resultOf result commands data)⟩ := by
  induction commands generalizing data with
  | nil => rfl
  | cons command commands ih =>
      have firstRun := localTrace command (by simp)
        (fun l => labels (.inl l))
        (entry LocalLabel main commands (fun l => labels (.inr l)) exit)
        (fun l => atLabels (.inl l)) data valid
      have nextValid := localInvariant command (by simp) data valid
      have tailRun := ih
        (fun c hc d hd => localInvariant c (by simp [hc]) d hd)
        (fun c hc => localTrace c (by simp [hc]))
        (fun l => labels (.inr l)) (fun l => atLabels (.inr l))
        (result command data) nextValid
      rw [steps, Nat.add_comm, Function.iterate_add_apply]
      change (advance (TM2.step program))^[steps result cost commands (result command data)]
        ((advance (TM2.step program))^[cost command data]
          (some ⟨some (labels (.inl (main command))), state data, tapes data⟩)) = _
      rw [firstRun]
      exact tailRun

end UniqueGamesTheorem.Foundations.Complexity.MachineFiniteSequence

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineSubroutineLemmas
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec.decodeWords_encodeWord _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter.counterTapes_counter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Concrete finite-alphabet serialization primitives. A natural word `n` is `n`
one-bits followed by a zero delimiter. These are size and decoding theorems, not
running-time certificates. In particular, output length is never called runtime.
-/

namespace UniqueGamesTheorem.Foundations.Complexity

theorem encodeWords_injective {xs ys : List Nat} (h : encodeWords xs = encodeWords ys) :
    xs = ys := by
  have decoded := congrArg decodeWords h
  simpa only [decodeWords_encodeWords, Option.some.injEq] using decoded

theorem encodeWords_length_le (ns : List Nat) (bound : Nat)
    (bounded : ∀ n ∈ ns, n ≤ bound) :
    (encodeWords ns).length ≤ ns.length * (bound + 1) := by
  induction ns with
  | nil => simp [encodeWords]
  | cons n ns ih =>
      have hn := bounded n (by simp)
      have hns := ih (fun x hx => bounded x (by simp [hx]))
      simp only [encodeWords, List.length_append, encodeWord_length, List.length_cons,
        Nat.add_mul, Nat.one_mul]
      omega

open Target

end UniqueGamesTheorem.Foundations.Complexity

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_LinearEvaluationLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.DirectionQuotient

abbrev F2 := UniqueGamesTheorem.Integration.BinaryLinear.F2

variable {V B : Type*} [AddCommGroup V] [Module F2 V]

def line (a : V) : Submodule F2 V := Submodule.span F2 {a}

abbrev Space (a : V) := V ⧸ line a

def proj (a : V) : V →ₗ[F2] Space a := (line a).mkQ

theorem proj_surjective (a : V) : Function.Surjective (proj a) :=
  (line a).mkQ_surjective

theorem card_line (a : V) (ha : a ≠ 0) : Nat.card (line a) = 2 := by
  calc
    Nat.card (line a) = Nat.card F2 :=
      Nat.card_congr (LinearEquiv.toSpanNonzeroSingleton F2 V a ha).symm.toEquiv
    _ = 2 := Nat.card_zmod 2

theorem card_proj_fiber (a : V) (ha : a ≠ 0) (z : Space a) :
    Nat.card {v : V // proj a v = z} = 2 := by
  rw [UniqueGamesTheorem.Gadget.LinearEvaluation.fiber_card_eq_kernel_of_surjective
    (proj a) (proj_surjective a) z]
  change Nat.card (LinearMap.ker (line a).mkQ) = 2
  rw [Submodule.ker_mkQ]
  exact card_line a ha

def projectWithSide (a : V) (x : V × B) : Space a × B :=
  (proj a x.1, x.2)

def withSideFiberEquiv (a : V) (z : Space a × B) :
    {x : V × B // projectWithSide a x = z} ≃ {v : V // proj a v = z.1} where
  toFun x := ⟨x.val.1, congrArg Prod.fst x.property⟩
  invFun v := ⟨(v.val, z.2), Prod.ext v.property rfl⟩
  left_inv x := by
    apply Subtype.ext
    exact Prod.ext rfl (congrArg Prod.snd x.property).symm
  right_inv v := by
    apply Subtype.ext
    rfl

theorem card_projectWithSide_fiber (a : V) (ha : a ≠ 0) (z : Space a × B) :
    Nat.card {x : V × B // projectWithSide a x = z} = 2 :=
  (Nat.card_congr (withSideFiberEquiv a z)).trans (card_proj_fiber a ha z.1)

open MixedSupport CanonicalKeys

end PerfectCompleteness.DirectionQuotient

end

section

namespace PerfectCompleteness.BlockQuotient

open DirectionQuotient

variable {I B : Type*} {V : I → Type*} [DecidableEq I]

variable [∀ i, AddCommGroup (V i)] [∀ i, Module F2 (V i)]

def projectBlock (selected : I) (a : V selected) (x : JointOutput V B) :
    Space a × (OtherBlocks V selected × B) :=
  projectWithSide a (splitOutput V B selected x)

@[simp] theorem projectBlock_selected (selected : I) (a : V selected)
    (x : JointOutput V B) : (projectBlock selected a x).1 = proj a (x.1 selected) := rfl

@[simp] theorem projectBlock_other (selected : I) (a : V selected)
    (x : JointOutput V B) (i : {i // i ≠ selected}) :
    (projectBlock selected a x).2.1 i = x.1 i.val := rfl

@[simp] theorem projectBlock_side (selected : I) (a : V selected)
    (x : JointOutput V B) : (projectBlock selected a x).2.2 = x.2 := rfl

def blockFiberEquiv (selected : I) (a : V selected)
    (z : Space a × (OtherBlocks V selected × B)) :
    {x : JointOutput V B // projectBlock selected a x = z} ≃
      {y : V selected × (OtherBlocks V selected × B) // projectWithSide a y = z} where
  toFun x := ⟨splitOutput V B selected x.val, x.property⟩
  invFun y := ⟨(splitOutput V B selected).symm y.val, by
    change projectWithSide a (splitOutput V B selected ((splitOutput V B selected).symm y.val)) = z
    rw [(splitOutput V B selected).apply_symm_apply]
    exact y.property⟩
  left_inv x := by
    apply Subtype.ext
    exact (splitOutput V B selected).symm_apply_apply x.val
  right_inv y := by
    apply Subtype.ext
    exact (splitOutput V B selected).apply_symm_apply y.val

theorem card_projectBlock_fiber (selected : I) (a : V selected) (ha : a ≠ 0)
    (z : Space a × (OtherBlocks V selected × B)) :
    Nat.card {x : JointOutput V B // projectBlock selected a x = z} = 2 :=
  (Nat.card_congr (blockFiberEquiv selected a z)).trans
    (card_projectWithSide_fiber a ha z)

open MixedSupport CanonicalKeys

theorem coarsenBlock_at_most_two [Finite I] [∀ i, Finite (V i)] [Finite B] {n : Nat}
    (slots : Fin n → Slot) (f : Assignment slots → JointOutput V B)
    (selected : I) (a : V selected) (ha : a ≠ 0)
    (Q : Label slots (projectBlock selected a ∘ f)) :
    Nat.card {P : Label slots f //
      CanonicalEdges.coarsen slots f (projectBlock selected a) P = Q} ≤ 2 := by
  apply CanonicalEdges.coarsen_at_most_two slots f (projectBlock selected a)
  intro z
  exact (card_projectBlock_fiber selected a ha z).le

end PerfectCompleteness.BlockQuotient

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_DescendantSpacesLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.RecursiveSpaceEquiv.spaceEquiv_apply _root_.OAI.PerfectCompleteness.RecursiveSpaceEquiv.squareEquiv_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
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

def slotEmbedding : {n m : Nat} → Path branch n m → Slots branch m → Slots branch n
  | _, _, .refl _, s => s
  | _, _, .step i p, s => (i, slotEmbedding p s)

@[simp] theorem slotEmbedding_refl (s : Slots branch n) :
    slotEmbedding (.refl n) s = s := rfl

@[simp] theorem slotEmbedding_step (i : Fin (branch n)) (p : Path branch n m)
    (s : Slots branch m) :
    slotEmbedding (.step i p) s = (i, slotEmbedding p s) := rfl

theorem height_le (p : Path branch n m) : m ≤ n := by
  induction p with
  | refl n => exact Nat.le_refl n
  | step i p ih => exact Nat.le_trans ih (Nat.le_succ _)

abbrev family (p : Path branch n m) (A : Slots branch n → Type u) :
    Slots branch m → Type u := fun s => A (p.slotEmbedding s)

def restriction (p : Path branch n m) (A : Slots branch n → Type u) :
    Assignment A → Assignment (p.family A) := fun x s => x (p.slotEmbedding s)

@[simp] theorem restriction_apply (p : Path branch n m)
    (A : Slots branch n → Type u) (x : Assignment A) (s : Slots branch m) :
    p.restriction A x s = x (p.slotEmbedding s) := rfl

@[simp] theorem restriction_refl (A : Slots branch n → Type u) :
    restriction (.refl n) A = id := rfl

theorem restriction_surjective (p : Path branch n m) :
    ∀ (A : Slots branch n → Type u), (∀ s, Nonempty (A s)) →
      Function.Surjective (p.restriction A) := by
  induction p with
  | refl n =>
      intro A _ y
      exact ⟨y, rfl⟩
  | step i p ih =>
      intro A hnonempty
      exact (ih (childFamily A i) (fun s => hnonempty (i, s))).comp
        (childRestriction_surjective A hnonempty i)

end Path

variable {𝕜 : Type w} [Field 𝕜] {branch : Nat → Nat} {n m : Nat}

theorem space_descendant_le (p : Path branch n m) :
    ∀ (A : Slots branch n → Type u), (∀ k < n, 0 < branch k) →
      (space 𝕜 branch m (p.family A)).map (pullback 𝕜 (p.restriction A)) ≤
        space 𝕜 branch n A := by
  induction p with
  | refl n =>
      intro A _ f hf
      obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hf
      exact hg
  | @step n m i p ih =>
      intro A hbranch f hf
      obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hf
      have hb : ∀ k < n, 0 < branch k :=
        fun k hk => hbranch k (Nat.lt_trans hk (Nat.lt_succ_self n))
      have hchild : pullback 𝕜 (p.restriction (childFamily A i)) g ∈
          space 𝕜 branch n (childFamily A i) :=
        ih (childFamily A i) hb (Submodule.mem_map_of_mem hg)
      exact child_le_space A i hb (Submodule.mem_map_of_mem hchild)

theorem squareSpace_descendant_le (p : Path branch n m)
    (A : Slots branch n → Type u) (hbranch : ∀ k < n, 0 < branch k) :
    (squareSpace (space 𝕜 branch m (p.family A))).map
        (pullback 𝕜 (p.restriction A)) ≤ squareSpace (space 𝕜 branch n A) :=
  squareSpace_pullback_le _ _ _ (space_descendant_le p A hbranch)

theorem step_square_le_space (A : Slots branch (n + 1) → Type u)
    (i : Fin (branch n)) (p : Path branch n m)
    (hbranch : ∀ k < n, 0 < branch k) :
    (squareSpace (space 𝕜 branch m ((Path.step i p).family A))).map
        (pullback 𝕜 ((Path.step i p).restriction A)) ≤ space 𝕜 branch (n + 1) A := by
  intro f hf
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hf
  have hchild : pullback 𝕜 (p.restriction (childFamily A i)) g ∈
      squareSpace (space 𝕜 branch n (childFamily A i)) :=
    squareSpace_descendant_le p (childFamily A i) hbranch
      (Submodule.mem_map_of_mem hg)
  exact child_square_le_space A i (Submodule.mem_map_of_mem hchild)

theorem descendant_square_le_space (p : Path branch n m)
    (A : Slots branch n → Type u) (hbranch : ∀ k < n, 0 < branch k)
    (hproper : m < n) :
    (squareSpace (space 𝕜 branch m (p.family A))).map
        (pullback 𝕜 (p.restriction A)) ≤ space 𝕜 branch n A := by
  cases p with
  | refl n => exact False.elim (Nat.lt_irrefl n hproper)
  | @step n m i p =>
      exact step_square_le_space A i p
        (fun k hk => hbranch k (Nat.lt_trans hk (Nat.lt_succ_self n)))

end PerfectCompleteness.DescendantSpaces



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_OccurrenceGame
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart
attribute [-simp] _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

noncomputable section

structure OccurrenceGame (E Q₁ Q₂ A₁ A₂ : Type*)
    [Fintype E] [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] where
  occurrences : FiniteDistribution E
  left : E → Q₁
  right : E → Q₂
  accepts : E → A₁ → A₂ → Bool

namespace OccurrenceGame

variable {E Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype E] [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

def ofProjection (μ : FiniteDistribution E) (left : E → Q₁) (right : E → Q₂)
    (projection : E → A₁ → A₂) : OccurrenceGame E Q₁ Q₂ A₁ A₂ := by
  classical
  exact
    { occurrences := μ
      left := left
      right := right
      accepts := fun e a b => decide (projection e a = b) }

def endpoints (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) (e : E) : Q₁ × Q₂ :=
  (G.left e, G.right e)

def wins (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) (e : E) : Bool :=
  G.accepts e (strategy.1 (G.left e)) (strategy.2 (G.right e))

def success (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) : ℝ :=
  G.occurrences.probability (G.wins strategy)

structure EndpointPresentation (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) where
  predicate : Q₁ → Q₂ → A₁ → A₂ → Bool
  agrees : ∀ e a b, G.accepts e a b = predicate (G.left e) (G.right e) a b

def toGame (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (p : G.EndpointPresentation) : Game Q₁ Q₂ A₁ A₂ where
  questions := G.occurrences.pushforward G.endpoints
  accepts := p.predicate

@[simp] theorem toGame_success (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (p : G.EndpointPresentation) (strategy : Strategy Q₁ Q₂ A₁ A₂) :
    (G.toGame p).success strategy = G.success strategy := by
  unfold Game.success OccurrenceGame.success toGame
  rw [FiniteDistribution.probability_pushforward]
  congr 1
  funext e
  exact (p.agrees e (strategy.1 (G.left e)) (strategy.2 (G.right e))).symm


variable [Nonempty A₁] [Nonempty A₂]

def value (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty G.success

theorem success_le_value (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) : G.success strategy ≤ G.value := by
  classical
  exact Finset.le_sup' G.success (Finset.mem_univ strategy)

theorem value_le_iff (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) (bound : ℝ) :
    G.value ≤ bound ↔ ∀ strategy : Strategy Q₁ Q₂ A₁ A₂, G.success strategy ≤ bound := by
  classical
  simp [value, Finset.sup'_le_iff]

end OccurrenceGame
end
end PerfectCompleteness

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineCopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCopy

open Turing

variable {K Λ σ β : Type} [DecidableEq K]

/-- A timed witness whose stored step count is the exact two-loop trace length. -/
def copyInTime (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch)
    (fallback : β) (firstLabel secondLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atFirst : program firstLabel =
      Reduction.MachineTransfer.loopAt source scratch id fallback firstLabel (some secondLabel))
    (atSecond : program secondLabel = forkLoop scratch source destination fallback secondLabel exit)
    (base : K → List β) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option β) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some firstLabel, (ambient, register), base⟩
      (some ⟨exit, (ambient, none),
        Function.update base destination (base source ++ base destination)⟩)
      (2 * ((base source).length + 1)) where
  steps := 2 * ((base source).length + 1)
  evals_in_steps := copyTrace source destination scratch sourceDestination sourceScratch
    destinationScratch fallback firstLabel secondLabel exit program atFirst atSecond base
    scratchEmpty ambient register
  steps_le_m := Nat.le_refl _

end UniqueGamesTheorem.Foundations.Complexity.MachineCopy

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineDrain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Actual complete-stack cleanup, with an arbitrary continuation. Each symbol
costs one transition and the empty-stack branch costs one final transition. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineDrain

open Turing

variable {K Λ σ : Type} [DecidableEq K]

def drainInTime (source : K) (again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atDrain : program again = drain source again exit)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, (ambient, register), base⟩
      (some ⟨exit, (ambient, none), Function.update base source []⟩)
      ((base source).length + 1) where
  steps := (base source).length + 1
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[(base source).length + 1]
      (some ⟨some again, (ambient, register), base⟩) = _
    simpa only [Function.update_eq_self] using
      drainTrace source again exit program atDrain base (base source) ambient register
  steps_le_m := Nat.le_refl _

end UniqueGamesTheorem.Foundations.Complexity.MachineDrain

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

abbrev Alphabet (_ : Tape) := Bool

end UniqueGamesTheorem.Foundations.Complexity.MachineCeilingPower

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_CompletionSoundness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CompletionSoundness

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open CompletionProbability

noncomputable section

section SeedLaws
variable {E : Type*} {Seed : E → Type*}
  [Fintype E] [∀ e, Fintype (Seed e)]

def sigmaLaw (μ : FiniteDistribution E) (ν : ∀ e, FiniteDistribution (Seed e)) :
    FiniteDistribution (Σ e, Seed e) where
  weight es := μ.weight es.1 * (ν es.1).weight es.2
  nonnegative es := mul_nonneg (μ.nonnegative es.1) ((ν es.1).nonnegative es.2)
  normalized := by
    rw [Fintype.sum_sigma]
    calc
      _ = ∑ e, μ.weight e := by
        apply Finset.sum_congr rfl
        intro e _
        change (∑ seed : Seed e, μ.weight e * (ν e).weight seed) = μ.weight e
        rw [← Finset.mul_sum, (ν e).normalized, mul_one]
      _ = 1 := μ.normalized

end SeedLaws

@[simp] theorem roundLabel_legal {L A : Type*} (legal : L ↪ A)
    (default l : L) : roundLabel legal default (legal l) = l := by
  have h : ∃ l', legal l' = legal l := ⟨l, rfl⟩
  simp only [roundLabel, dite_eq_left h]
  exact legal.injective (Classical.choose_spec h)

structure LegalProjectionGame (E Q₁ Q₂ : Type*)
    (L : Q₁ → Type*) (R : Q₂ → Type*) [Fintype E] where
  occurrences : FiniteDistribution E
  left : E → Q₁
  right : E → Q₂
  projection : ∀ e, L (left e) → R (right e)

namespace LegalProjectionGame

variable {E Q₁ Q₂ : Type*} {L : Q₁ → Type*} {R : Q₂ → Type*}
  [Fintype E] (G : LegalProjectionGame E Q₁ Q₂ L R)

def wins (s : LegalStrategy L R) (e : E) : Bool :=
  decide (G.projection e (s.1 (G.left e)) = s.2 (G.right e))

def success (s : LegalStrategy L R) : ℝ := G.occurrences.probability (G.wins s)

section Completion
variable [Fintype Q₁] [Fintype Q₂]
  {A B : Type*} [Fintype A] [Fintype B]
  {Seed : E → Type*} [∀ e, Fintype (Seed e)]

def completedGame (ν : ∀ e, FiniteDistribution (Seed e))
    (complete : ∀ e, Seed e → A → B) :
    OccurrenceGame (Σ e, Seed e) Q₁ Q₂ A B :=
  OccurrenceGame.ofProjection (sigmaLaw G.occurrences ν)
    (fun es => G.left es.1) (fun es => G.right es.1)
    (fun es => complete es.1 es.2)

end Completion

variable [Fintype Q₁] [Fintype Q₂] [∀ x, Fintype (L x)]
  {A B : Type*} [Fintype A] [Fintype B]

structure CompletionFamily (legalL : ∀ x, L x ↪ A) (legalR : ∀ y, R y ↪ B) where
  size : E → Nat
  positive : ∀ e, 0 < size e
  map : ∀ e, Fin (size e) → A → B
  agrees : ∀ e seed l, map e seed (legalL (G.left e) l) =
    legalR (G.right e) (G.projection e l)
  exact_two : ∀ e seed b, Fintype.card {a : A // map e seed a = b} = 2
  illegal_probability : ∀ e (a : Illegal (legalL (G.left e))) (b : B),
    uniformProbability (fun seed => map e seed a.val = b) ≤
      2 / (Fintype.card A - Fintype.card (L (G.left e)) : Nat)

namespace CompletionFamily
variable {G} {legalL : ∀ x, L x ↪ A} {legalR : ∀ y, R y ↪ B}

def seedLaw (F : G.CompletionFamily legalL legalR) (e : E) :
    FiniteDistribution (Fin (F.size e)) := by
  letI : Nonempty (Fin (F.size e)) := ⟨⟨0, F.positive e⟩⟩
  exact FiniteDistribution.uniform (Fin (F.size e))

def game (F : G.CompletionFamily legalL legalR) :
    OccurrenceGame (Σ e, Fin (F.size e)) Q₁ Q₂ A B :=
  G.completedGame F.seedLaw F.map

end CompletionFamily

end LegalProjectionGame

end
end PerfectCompleteness.CompletionSoundness

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_FiniteProduct
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FiniteProduct

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

def law (P : (i : I) → FiniteDistribution (Ω i)) :
    FiniteDistribution ((i : I) → Ω i) where
  weight x := ∏ i, (P i).weight (x i)
  nonnegative x := Finset.prod_nonneg fun i _ => (P i).nonnegative (x i)
  normalized := by
    rw [← Fintype.prod_sum]
    simp only [FiniteDistribution.normalized, Finset.prod_const_one]

end
end PerfectCompleteness.FiniteProduct

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_RecordSeedSamplingLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite
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

def DrawIndex (repeats : Nat → Nat) : {n m : Nat} → Path branch n m → Type
  | _, _, .refl _ => Unit
  | n + 1, _, .step i p =>
      OffPath i ⊕ ((Fin (repeats (n + 1)) × Bool) × DrawIndex repeats p)

noncomputable instance drawIndexFintype (repeats : Nat → Nat) (p : Path branch n m) :
    Fintype (DrawIndex repeats p) := by
  induction p with
  | refl n => exact inferInstanceAs (Fintype Unit)
  | @step n m i p ih =>
      letI : Fintype (DrawIndex repeats p) := ih
      exact inferInstanceAs (Fintype
        (OffPath i ⊕ ((Fin (repeats (n + 1)) × Bool) × DrawIndex repeats p)))

noncomputable instance drawIndexDecidableEq (repeats : Nat → Nat) (p : Path branch n m) :
    DecidableEq (DrawIndex repeats p) := by
  induction p with
  | refl n => exact inferInstanceAs (DecidableEq Unit)
  | @step n m i p ih =>
      letI : DecidableEq (DrawIndex repeats p) := ih
      exact inferInstanceAs (DecidableEq
        (OffPath i ⊕ ((Fin (repeats (n + 1)) × Bool) × DrawIndex repeats p)))

variable (𝕜 : Type w) [Field 𝕜]

def DrawSpace (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) → (A : Slots branch n → Type u) →
      DrawIndex repeats p → Type (max u w)
  | n, _, .refl _, A, _ => space 𝕜 branch n A
  | n + 1, _, .step i p, A, j =>
      match j with
      | Sum.inl j => squareSpace (space 𝕜 branch n (childFamily A j.val))
      | Sum.inr j => DrawSpace 𝕜 repeats p (childFamily A i) j.2

abbrev Tape (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) :=
  (j : DrawIndex repeats p) → DrawSpace 𝕜 repeats p A j

def zeroDraw (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) → (A : Slots branch n → Type u) →
      (j : DrawIndex repeats p) → DrawSpace 𝕜 repeats p A j
  | n, _, .refl _, A, _ => (0 : space 𝕜 branch n A)
  | n + 1, _, .step i p, A, j =>
      match j with
      | Sum.inl j => (0 : squareSpace (space 𝕜 branch n (childFamily A j.val)))
      | Sum.inr j => zeroDraw 𝕜 repeats p (childFamily A i) j.2

def zeroTape (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) : Tape 𝕜 repeats p A :=
  zeroDraw 𝕜 repeats p A

instance drawSpaceNonempty (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) (j : DrawIndex repeats p) :
    Nonempty (DrawSpace 𝕜 repeats p A j) :=
  ⟨zeroDraw 𝕜 repeats p A j⟩

theorem drawSpace_finite [Finite 𝕜] (repeats : Nat → Nat) (p : Path branch n m) :
    ∀ (A : Slots branch n → Type u), (∀ s, Finite (A s)) →
      ∀ j : DrawIndex repeats p, Finite (DrawSpace 𝕜 repeats p A j) := by
  induction p with
  | refl n =>
      intro A hA j
      let : ∀ s, Finite (A s) := hA
      change Finite (space 𝕜 branch n A)
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

instance drawSpaceFinite [Finite 𝕜] (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) [∀ s, Finite (A s)] (j : DrawIndex repeats p) :
    Finite (DrawSpace 𝕜 repeats p A j) :=
  drawSpace_finite 𝕜 repeats p A (fun _ => inferInstance) j

noncomputable instance drawSpaceFintype [Finite 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) (A : Slots branch n → Type u) [∀ s, Finite (A s)]
    (j : DrawIndex repeats p) : Fintype (DrawSpace 𝕜 repeats p A j) :=
  Fintype.ofFinite _

def subTape (repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (A : Slots branch (n + 1) → Type u) (t : Tape 𝕜 repeats (.step i p) A)
    (h : Fin (repeats (n + 1))) (b : Bool) :
    Tape 𝕜 repeats p (childFamily A i) :=
  fun j => t (.inr ((h, b), j))

noncomputable section

def combineFunction (A : Slots branch (n + 1) → Type u) (i : Fin (branch n))
    (r : Nat)
    (ordinary : (j : OffPath i) → squareSpace (space 𝕜 branch n (childFamily A j.val)))
    (left right : Fin r → space 𝕜 branch n (childFamily A i)) : Assignment A → 𝕜 :=
  (∑ j : OffPath i, pullback 𝕜 (childRestriction A j.val) (ordinary j).val) +
    ∑ h : Fin r, pullback 𝕜 (childRestriction A i) ((left h).val * (right h).val)

theorem combineFunction_mem (A : Slots branch (n + 1) → Type u)
    (i : Fin (branch n)) (r : Nat)
    (ordinary : (j : OffPath i) → squareSpace (space 𝕜 branch n (childFamily A j.val)))
    (left right : Fin r → space 𝕜 branch n (childFamily A i)) :
    combineFunction 𝕜 A i r ordinary left right ∈ space 𝕜 branch (n + 1) A := by
  apply (space 𝕜 branch (n + 1) A).add_mem
  · apply (space 𝕜 branch (n + 1) A).sum_mem
    intro j _
    exact child_square_le_space A j.val (Submodule.mem_map_of_mem (ordinary j).property)
  · apply (space 𝕜 branch (n + 1) A).sum_mem
    intro h _
    exact child_square_le_space A i (Submodule.mem_map_of_mem
      (mul_mem_squareSpace _ (left h).property (right h).property))

def combine (A : Slots branch (n + 1) → Type u) (i : Fin (branch n)) (r : Nat)
    (ordinary : (j : OffPath i) → squareSpace (space 𝕜 branch n (childFamily A j.val)))
    (left right : Fin r → space 𝕜 branch n (childFamily A i)) :
    space 𝕜 branch (n + 1) A :=
  ⟨combineFunction 𝕜 A i r ordinary left right,
    combineFunction_mem 𝕜 A i r ordinary left right⟩

@[simp] theorem combine_zero (A : Slots branch (n + 1) → Type u)
    (i : Fin (branch n)) (r : Nat) :
    combine 𝕜 A i r (fun _ => 0) (fun _ => 0) (fun _ => 0) = 0 := by
  apply Subtype.ext
  funext x
  simp [combine, combineFunction, PointwiseSpaces.pullback]

def evaluate (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) → (A : Slots branch n → Type u) →
      Tape 𝕜 repeats p A → space 𝕜 branch n A
  | _, _, .refl _, _, t => t ()
  | n + 1, _, .step i p, A, t =>
      combine 𝕜 A i (repeats (n + 1)) (fun j => t (.inl j))
        (fun h => evaluate 𝕜 repeats p (childFamily A i)
          (subTape 𝕜 repeats i p A t h false))
        (fun h => evaluate 𝕜 repeats p (childFamily A i)
          (subTape 𝕜 repeats i p A t h true))

@[simp] theorem evaluate_refl (repeats : Nat → Nat)
    (A : Slots branch n → Type u) (t : Tape 𝕜 repeats (.refl n) A) :
    evaluate 𝕜 repeats (.refl n) A t = t () := rfl

@[simp] theorem evaluate_zeroTape (repeats : Nat → Nat) (p : Path branch n m) :
    ∀ (A : Slots branch n → Type u),
      evaluate 𝕜 repeats p A (zeroTape 𝕜 repeats p A) = 0 := by
  induction p with
  | refl n =>
      intro A
      rfl
  | @step n m i p ih =>
      intro A
      change combine 𝕜 A i (repeats (n + 1)) (fun _ => 0)
        (fun _ => evaluate 𝕜 repeats p (childFamily A i)
          (zeroTape 𝕜 repeats p (childFamily A i)))
        (fun _ => evaluate 𝕜 repeats p (childFamily A i)
          (zeroTape 𝕜 repeats p (childFamily A i))) = 0
      simp only [ih, combine_zero]

variable [Finite 𝕜]

def tapeLaw (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) [∀ s, Finite (A s)] :
    FiniteDistribution (Tape 𝕜 repeats p A) :=
  FiniteProduct.law (fun j => FiniteDistribution.uniform (DrawSpace 𝕜 repeats p A j))

def law (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) [∀ s, Finite (A s)]
    [Fintype (space 𝕜 branch n A)] : FiniteDistribution (space 𝕜 branch n A) :=
  (tapeLaw 𝕜 repeats p A).pushforward (evaluate 𝕜 repeats p A)

end
end PerfectCompleteness.RecursiveSampler

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_BucketSampler
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite
attribute [-simp] _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.BucketSampler

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {Ω H : Type*} [AddCommGroup H] [Module F2 H]

section Laws

variable [Fintype Ω]

def tapeLaw (ℓ : Nat) (μ : FiniteDistribution Ω) : FiniteDistribution (Tape ℓ Ω) :=
  FiniteProduct.law (fun _ : Direction ℓ => μ)

@[simp] theorem tapeLaw_weight (ℓ : Nat) (μ : FiniteDistribution Ω) (t : Tape ℓ Ω) :
    (tapeLaw ℓ μ).weight t = ∏ v : Direction ℓ, μ.weight (t v) := rfl

@[simp] theorem tapeLaw_zero_width_weight (μ : FiniteDistribution Ω) (t : Tape 0 Ω) :
    (tapeLaw 0 μ).weight t = 1 := by
  simp [tapeLaw, FiniteProduct.law]

end Laws


open PointwiseSpaces RecursiveSpaces DescendantSpaces

universe u
variable {branch : Nat → Nat} {n m : Nat}

abbrev RecursiveTape (ℓ : Nat) (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) :=
  Tape ℓ (RecursiveSampler.Tape F2 repeats p A)

def recursiveEvaluate (ℓ : Nat) (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) (t : RecursiveTape ℓ repeats p A) :
    Fin ℓ → space F2 branch n A :=
  evaluate ℓ (RecursiveSampler.evaluate F2 repeats p A) t

def recursiveTapeLaw (ℓ : Nat) (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) [∀ s, Finite (A s)] :
    FiniteDistribution (RecursiveTape ℓ repeats p A) :=
  tapeLaw ℓ (RecursiveSampler.tapeLaw F2 repeats p A)

end
end PerfectCompleteness.BucketSampler

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_RationalFiniteLawLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



noncomputable section

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

namespace UniqueGamesTheorem.Foundations.Games.FiniteDistribution

@[simp] theorem pushforward_id {A : Type*} [Fintype A]
    (μ : FiniteDistribution A) : μ.pushforward id = μ := by
  classical
  apply eq_of_weight_eq
  intro a
  simp [pushforward]

end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_BucketUniformLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.BucketUniform

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open BucketSampler (F2 Direction)

variable {H : Type*} [AddCommGroup H] [Module F2 H]

def coordinateDirection {ℓ : Nat} (i : Fin ℓ) : Direction ℓ :=
  ⟨Pi.single i (1 : F2), by
    intro h
    have hi := congrFun h i
    simp at hi⟩

def evaluateLinear (ℓ : Nat) : (Direction ℓ → H) →ₗ[F2] (Fin ℓ → H) where
  toFun := BucketSampler.evaluate ℓ (id : H → H)
  map_add' t u := by
    funext i
    simp only [BucketSampler.evaluate, id_eq, Pi.add_apply, smul_add,
      Finset.sum_add_distrib]
  map_smul' a t := by
    funext i
    change (∑ v : Direction ℓ, v.val i • (a • t v)) =
      a • ∑ v : Direction ℓ, v.val i • t v
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun v _ => smul_comm _ _ _)

@[simp] theorem evaluateLinear_apply (ℓ : Nat) (t : Direction ℓ → H) :
    evaluateLinear ℓ t = BucketSampler.evaluate ℓ (id : H → H) t := rfl

def coordinateTape {ℓ : Nat} (rows : Fin ℓ → H) : Direction ℓ → H :=
  ∑ i : Fin ℓ, Pi.single (coordinateDirection i) (rows i)


variable {Ω : Type*} (V : Submodule F2 (Ω → F2))

def ofRowsLinear (ℓ : Nat) :
    (Fin ℓ → V) →ₗ[F2] (Module.Dual F2 V →ₗ[F2] (Fin ℓ → F2)) where
  toFun := EvaluationMatrix.ofRows V
  map_add' rows rows' := by
    apply LinearMap.ext
    intro q
    funext i
    exact map_add q (rows i) (rows' i)
  map_smul' a rows := by
    apply LinearMap.ext
    intro q
    funext i
    exact map_smul q a (rows i)

end
end PerfectCompleteness.BucketUniform



namespace PerfectCompleteness.RecursiveSamplerBiasAlgebra

open PointwiseSpaces RecursiveSpaces RecursiveSampler
open scoped BigOperators

universe u w

variable (𝕜 : Type w) [Field 𝕜]

def squareProduct {X : Type u} (H : Submodule 𝕜 (X → 𝕜)) :
    H →ₗ[𝕜] H →ₗ[𝕜] squareSpace H :=
  LinearMap.mk₂ 𝕜
    (fun g h => ⟨g.val * h.val, mul_mem_squareSpace H g.property h.property⟩)
    (fun g g' h => Subtype.ext (add_mul g.val g'.val h.val))
    (fun c g h => Subtype.ext (smul_mul_assoc c g.val h.val))
    (fun g h h' => Subtype.ext (mul_add g.val h.val h'.val))
    (fun c g h => Subtype.ext (mul_smul_comm c g.val h.val))

@[simp] theorem squareProduct_val {X : Type u} (H : Submodule 𝕜 (X → 𝕜))
    (g h : H) : (squareProduct 𝕜 H g h).val = g.val * h.val := rfl

variable {branch : Nat → Nat} {n : Nat}

def childSquareLift (A : Slots branch (n + 1) → Type u) (i : Fin (branch n)) :
    squareSpace (space 𝕜 branch n (childFamily A i)) →ₗ[𝕜]
      space 𝕜 branch (n + 1) A where
  toFun g := ⟨pullback 𝕜 (childRestriction A i) g.val,
    child_square_le_space A i (Submodule.mem_map_of_mem g.property)⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp] theorem childSquareLift_val (A : Slots branch (n + 1) → Type u)
    (i : Fin (branch n)) (g : squareSpace (space 𝕜 branch n (childFamily A i))) :
    (childSquareLift 𝕜 A i g).val = pullback 𝕜 (childRestriction A i) g.val := rfl

def childProduct (A : Slots branch (n + 1) → Type u) (i : Fin (branch n)) :
    space 𝕜 branch n (childFamily A i) →ₗ[𝕜]
      space 𝕜 branch n (childFamily A i) →ₗ[𝕜] space 𝕜 branch (n + 1) A :=
  (squareProduct 𝕜 (space 𝕜 branch n (childFamily A i))).compr₂
    (childSquareLift 𝕜 A i)

@[simp] theorem childProduct_val (A : Slots branch (n + 1) → Type u)
    (i : Fin (branch n)) (g h : space 𝕜 branch n (childFamily A i)) :
    (childProduct 𝕜 A i g h).val =
      pullback 𝕜 (childRestriction A i) (g.val * h.val) := rfl

def childBilinear (A : Slots branch (n + 1) → Type u) (i : Fin (branch n))
    (f : space 𝕜 branch (n + 1) A →ₗ[𝕜] 𝕜) :
    space 𝕜 branch n (childFamily A i) →ₗ[𝕜]
      space 𝕜 branch n (childFamily A i) →ₗ[𝕜] 𝕜 :=
  (childProduct 𝕜 A i).compr₂ f

@[simp] theorem childBilinear_apply (A : Slots branch (n + 1) → Type u)
    (i : Fin (branch n)) (f : space 𝕜 branch (n + 1) A →ₗ[𝕜] 𝕜)
    (g h : space 𝕜 branch n (childFamily A i)) :
    childBilinear 𝕜 A i f g h =
      f (childSquareLift 𝕜 A i
        (squareProduct 𝕜 (space 𝕜 branch n (childFamily A i)) g h)) := rfl

end PerfectCompleteness.RecursiveSamplerBiasAlgebra



namespace PerfectCompleteness.RecursiveSampler

open PointwiseSpaces RecursiveSpaces DescendantSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

universe u w

variable {branch : Nat → Nat} {n m : Nat}

variable (𝕜 : Type w) [Field 𝕜]

abbrev OrdinaryTape (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u) :=
  (j : OffPath i) → DrawSpace 𝕜 repeats (.step i p) A (.inl j)

abbrev CallTapes (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u) :=
  CallIndex repeats n → Tape 𝕜 repeats p (childFamily A i)

def splitTapeEquiv (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u) :
    Tape 𝕜 repeats (.step i p) A ≃
      OrdinaryTape 𝕜 repeats i p A × CallTapes 𝕜 repeats i p A where
  toFun t := (fun j => t (.inl j), fun hb => subTape 𝕜 repeats i p A t hb.1 hb.2)
  invFun z j := match j with
    | .inl j => z.1 j
    | .inr j => z.2 j.1 j.2
  left_inv t := by
    funext j
    cases j <;> rfl
  right_inv z := by
    apply Prod.ext
    · funext j
      rfl
    · funext hb j
      rfl

noncomputable def evaluateCalls (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    (calls : CallTapes 𝕜 repeats i p A) :
    CallIndex repeats n → space 𝕜 branch n (childFamily A i) :=
  fun hb => evaluate 𝕜 repeats p (childFamily A i) (calls hb)

noncomputable def splitEvaluatedTape (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    (t : Tape 𝕜 repeats (.step i p) A) :
    OrdinaryTape 𝕜 repeats i p A ×
      (CallIndex repeats n → space 𝕜 branch n (childFamily A i)) :=
  ((splitTapeEquiv 𝕜 repeats i p A t).1,
    evaluateCalls 𝕜 repeats i p A (splitTapeEquiv 𝕜 repeats i p A t).2)

noncomputable section

variable [Finite 𝕜]

def callScalarLaw (𝕜 : Type w) [Field 𝕜] [Finite 𝕜]
    (repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (A : Slots branch (n + 1) → Type u) [hA : ∀ s, Finite (A s)]
    [Fintype (space 𝕜 branch n (childFamily A i))] :
    FiniteDistribution (CallIndex repeats n → space 𝕜 branch n (childFamily A i)) := by
  letI : ∀ s, Finite (childFamily A i s) := fun s => hA (i, s)
  exact FiniteProduct.law (fun _ : CallIndex repeats n =>
    law 𝕜 repeats p (childFamily A i))

end
end PerfectCompleteness.RecursiveSampler

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_BucketMatrixResampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.BucketMatrixResampling

noncomputable section

open scoped Classical
open UniqueGamesTheorem.Foundations.Games
open BucketSampler (F2 Direction Tape)

variable {Ω : Type*} (V : Submodule F2 (Ω → F2))

abbrev Matrix (ℓ : Nat) := Module.Dual F2 V →ₗ[F2] (Fin ℓ → F2)

def assembledMatrix (ℓ : Nat) (t : Tape ℓ V) : Matrix V ℓ :=
  EvaluationMatrix.ofRows V (BucketSampler.evaluate ℓ (id : V → V) t)

end
end PerfectCompleteness.BucketMatrixResampling

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_MatrixRowQuotientLaw
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.MatrixRowQuotientLaw

noncomputable section

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open MatrixRowQuotient

variable {𝕜 H K : Type*} [Field 𝕜]
  [AddCommGroup H] [Module 𝕜 H] [AddCommGroup K] [Module 𝕜 K]

def projectMatrixLinear (W : Submodule 𝕜 H) :
    (Module.Dual 𝕜 H →ₗ[𝕜] K) →ₗ[𝕜] (Module.Dual 𝕜 (H ⧸ W) →ₗ[𝕜] K) where
  toFun := projectMatrix W
  map_add' X Y := by
    apply LinearMap.ext
    intro q
    rfl
  map_smul' a X := by
    apply LinearMap.ext
    intro q
    rfl

@[simp] theorem projectMatrixLinear_apply (W : Submodule 𝕜 H)
    (X : Module.Dual 𝕜 H →ₗ[𝕜] K) :
    projectMatrixLinear W X = projectMatrix W X := rfl

def jointProjection (W : Submodule 𝕜 H) :
    ((Module.Dual 𝕜 H →ₗ[𝕜] K) × H) →ₗ[𝕜]
      ((Module.Dual 𝕜 (H ⧸ W) →ₗ[𝕜] K) × (H ⧸ W)) :=
  (projectMatrixLinear W).prodMap W.mkQ

@[simp] theorem jointProjection_apply (W : Submodule 𝕜 H)
    (p : (Module.Dual 𝕜 H →ₗ[𝕜] K) × H) :
    jointProjection W p = (projectMatrix W p.1, W.mkQ p.2) := rfl

end
end PerfectCompleteness.MatrixRowQuotientLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_QuotientTableAgreementLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.MixedSupport

open ClauseSupport

variable {I C Y Z : Type*}

theorem localKey_kernel_invariant (s : Slot)
    (f : C → s.Domain → Y) (g : C → s.Domain → Z)
    (hkernel : ∀ c u v, f c u = f c v ↔ g c u = g c v) :
    localKey s f = localKey s g := by
  classical
  cases s with
  | clause occurrence variableIDs signs =>
    change clauseKey occurrence variableIDs f = clauseKey occurrence variableIDs g
    simp only [clauseKey, clauseMode_kernel_invariant f g hkernel]
  | bit variableID =>
    change C → Bool → Y at f
    change C → Bool → Z at g
    change bitKey variableID f = bitKey variableID g
    simp only [bitKey, unused_kernel_invariant f g hkernel]

theorem localReduction_kernel_invariant (s : Slot)
    (f : C → s.Domain → Y) (g : C → s.Domain → Z)
    (hkernel : ∀ c u v, f c u = f c v ↔ g c u = g c v) :
    localReduction s f = localReduction s g := by
  classical
  cases s with
  | clause occurrence variableIDs signs =>
    change clauseReduction f = clauseReduction g
    simp only [clauseReduction, clauseMode_kernel_invariant f g hkernel]
  | bit variableID =>
    change C → Bool → Y at f
    change C → Bool → Z at g
    funext b
    change bitReduction f b = bitReduction g b
    simp only [bitReduction, unused_kernel_invariant f g hkernel]

variable [DecidableEq I]

theorem sectionFunction_kernel_invariant (slots : I → Slot)
    (f : Assignment slots → Y) (g : Assignment slots → Z)
    (hkernel : ∀ x x', f x = f x' ↔ g x = g x') (i : I) :
    ∀ context u v,
      sectionFunction slots f i context u = sectionFunction slots f i context v ↔
      sectionFunction slots g i context u = sectionFunction slots g i context v := by
  intro context u v
  exact hkernel (Function.update context i u) (Function.update context i v)

theorem keyFields_kernel_invariant (slots : I → Slot)
    (f : Assignment slots → Y) (g : Assignment slots → Z)
    (hkernel : ∀ x x', f x = f x' ↔ g x = g x') :
    keyFields slots f = keyFields slots g := by
  funext i
  exact localKey_kernel_invariant (slots i)
    (sectionFunction slots f i) (sectionFunction slots g i)
    (sectionFunction_kernel_invariant slots f g hkernel i)

theorem coordinateReduction_kernel_invariant (slots : I → Slot)
    (f : Assignment slots → Y) (g : Assignment slots → Z)
    (hkernel : ∀ x x', f x = f x' ↔ g x = g x') :
    coordinateReduction slots f = coordinateReduction slots g := by
  funext i
  exact localReduction_kernel_invariant (slots i)
    (sectionFunction slots f i) (sectionFunction slots g i)
    (sectionFunction_kernel_invariant slots f g hkernel i)

theorem reduction_kernel_invariant (slots : I → Slot)
    (f : Assignment slots → Y) (g : Assignment slots → Z)
    (hkernel : ∀ x x', f x = f x' ↔ g x = g x') :
    reduction slots f = reduction slots g := by
  unfold reduction
  rw [coordinateReduction_kernel_invariant slots f g hkernel]

theorem retainedKeys_kernel_invariant {n : Nat} (slots : Fin n → Slot)
    (f : Assignment slots → Y) (g : Assignment slots → Z)
    (hkernel : ∀ x x', f x = f x' ↔ g x = g x') :
    retainedKeys slots f = retainedKeys slots g := by
  simp only [retainedKeys, keyFields_kernel_invariant slots f g hkernel]

end PerfectCompleteness.MixedSupport

namespace PerfectCompleteness.MixedSupport

variable {I Y Z : Type*} [DecidableEq I]

theorem reducedParts_kernel_invariant (slots : I → Slot)
    (f : Assignment slots → Y) (g : Assignment slots → Z)
    (hkernel : ∀ x x', f x = f x' ↔ g x = g x') :
    ReducedPartition.parts (reduction slots f) f =
      ReducedPartition.parts (reduction slots g) g := by
  rw [reduction_kernel_invariant slots f g hkernel]
  exact ReducedPartition.parts_kernel_invariant (reduction slots g) f g hkernel

end PerfectCompleteness.MixedSupport

end

section

namespace PerfectCompleteness.CanonicalKeys

open MixedSupport

variable {n : Nat} {Y Z : Type*}

theorem partition_kernel_invariant (slots : Fin n → Slot)
    (f : Assignment slots → Y) (g : Assignment slots → Z)
    (hkernel : ∀ x x', f x = f x' ↔ g x = g x') :
    partition slots f = partition slots g :=
  reducedParts_kernel_invariant slots f g hkernel

theorem key_kernel_invariant (side : Side) (slots : Fin n → Slot)
    (f : Assignment slots → Y) (g : Assignment slots → Z)
    (hkernel : ∀ x x', f x = f x' ↔ g x = g x') :
    key side slots f = key side slots g := by
  simp only [key, retainedKeys_kernel_invariant slots f g hkernel,
    partition_kernel_invariant slots f g hkernel]

theorem key_postcomp_injective (side : Side) (slots : Fin n → Slot)
    (f : Assignment slots → Y) (e : Y → Z) (he : Function.Injective e) :
    key side slots (e ∘ f) = key side slots f := by
  apply key_kernel_invariant
  intro x x'
  exact ⟨fun h => he h, fun h => congrArg e h⟩

theorem key_postcomp_equiv (side : Side) (slots : Fin n → Slot)
    (f : Assignment slots → Y) (e : Y ≃ Z) :
    key side slots (e ∘ f) = key side slots f :=
  key_postcomp_injective side slots f e e.injective

noncomputable def transportKernel (slots : Fin n → Slot)
    (f : Assignment slots → Y) (g : Assignment slots → Z)
    (hkernel : ∀ x x', f x = f x' ↔ g x = g x') (P : Label slots f) :
    Label slots g :=
  ⟨P.val, by
    change P.val ∈ partition slots g
    rw [← partition_kernel_invariant slots f g hkernel]
    exact P.property⟩

theorem transportKernel_evaluateLabel (slots : Fin n → Slot)
    (f : Assignment slots → Y) (g : Assignment slots → Z)
    (hkernel : ∀ x x', f x = f x' ↔ g x = g x') (x : Assignment slots) :
    transportKernel slots f g hkernel (evaluateLabel slots f x) =
      evaluateLabel slots g x := by
  apply Subtype.ext
  change ReducedPartition.fiber (reduction slots f) f x =
    ReducedPartition.fiber (reduction slots g) g x
  rw [reduction_kernel_invariant slots f g hkernel]
  exact ReducedPartition.fiber_kernel_invariant (reduction slots g) f g hkernel x

theorem restore_transportKernel (slots : Fin n → Slot)
    (f : Assignment slots → Y) (g : Assignment slots → Z)
    (hkernel : ∀ x x', f x = f x' ↔ g x = g x')
    (e : Y → Z) (he : ∀ x, g x = e (f x)) (P : Label slots f) :
    restore slots g (transportKernel slots f g hkernel P) = e (restore slots f P) := by
  obtain ⟨x, hx⟩ := ReducedPartition.label_surjective (reduction slots f) f P
  change evaluateLabel slots f x = P at hx
  rw [← hx, transportKernel_evaluateLabel, restore_evaluateLabel, restore_evaluateLabel]
  exact he x

end PerfectCompleteness.CanonicalKeys

end

section

namespace PerfectCompleteness.KeyStrategy

noncomputable section

open scoped Classical
open ClauseSupport MixedSupport CanonicalKeys

variable {n : Nat} {Y Z : Type*}

def queryKey (side : Side) (slots : Fin n → Slot) (f : Assignment slots → Y) :
    NonemptyKey n :=
  ⟨key side slots f, by
    obtain ⟨x⟩ := (inferInstance : Nonempty (Assignment slots))
    exact ⟨(evaluateLabel slots f x).val, (evaluateLabel slots f x).property⟩⟩

def label (σ : Strategy n) (side : Side) (slots : Fin n → Slot)
    (f : Assignment slots → Y) : Label slots f :=
  σ (queryKey side slots f)

def response (σ : Strategy n) (side : Side) (slots : Fin n → Slot)
    (f : Assignment slots → Y) : Y :=
  restore slots f (label σ side slots f)

end
end PerfectCompleteness.KeyStrategy

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_CanonicalMatrixTable
attribute [-instance] _root_.OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CanonicalMatrixTable

noncomputable section

open scoped Classical
open ClauseSupport MixedSupport CanonicalKeys
open DirectionQuotient (F2)

variable {n : Nat} {K Z : Type*} [AddCommGroup K] [Module F2 K]
  (slots : Fin n → Slot) (H : Submodule F2 (Assignment slots → F2))
  (other : Assignment slots → Z) (σ : KeyStrategy.Strategy n)

abbrev Matrix := Module.Dual F2 H →ₗ[F2] K

def query (X : Matrix (K := K) slots H) : Assignment slots → K × Z :=
  EvaluationMatrix.joint H other X

def response (X : Matrix (K := K) slots H) : K × Z :=
  KeyStrategy.response σ .left slots (query slots H other X)

def rightQuery (a : K) (X : Matrix (K := K) slots H) : Assignment slots → DirectionQuotient.Space a × Z :=
  DirectionQuotient.projectWithSide a ∘ query slots H other X

def Accepts (a : K) (X : Matrix (K := K) slots H) : Prop :=
  CanonicalEdges.coarsen slots (query slots H other X) (DirectionQuotient.projectWithSide a)
    (KeyStrategy.label σ .left slots (query slots H other X)) =
      KeyStrategy.label σ .right slots (rightQuery slots H other a X)

end
end PerfectCompleteness.CanonicalMatrixTable

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_TreeSourceSpaces
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyDomainFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalEdges.coarsen_evaluateLabel _root_.OAI.PerfectCompleteness.CanonicalEdges.restore_coarsen _root_.OAI.PerfectCompleteness.CanonicalKeyShape.assignmentEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalKeyShape.transport_apply _root_.OAI.PerfectCompleteness.CanonicalKeys.restore_evaluateLabel _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.restriction_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.restriction_refl _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_refl _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_step _root_.OAI.PerfectCompleteness.RecursiveSampler.combine_zero _root_.OAI.PerfectCompleteness.RecursiveSampler.evaluate_refl _root_.OAI.PerfectCompleteness.RecursiveSampler.evaluate_zeroTape _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RecursiveSpaceEquiv.spaceEquiv_apply _root_.OAI.PerfectCompleteness.RecursiveSpaceEquiv.squareEquiv_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.TreeSourceSpaces

open MixedSupport

variable {branch : Nat → Nat} {n t : Nat}

abbrev LeafDomain (slots : RecursiveSpaces.Slots branch n → Fin t → Slot)
    (s : RecursiveSpaces.Slots branch n) := MixedSupport.Assignment (slots s)

abbrev Domain (slots : RecursiveSpaces.Slots branch n → Fin t → Slot) :=
  RecursiveSpaces.Assignment (LeafDomain slots)

abbrev H (slots : RecursiveSpaces.Slots branch n → Fin t → Slot) :
    Submodule F2 (Domain slots → F2) :=
  RecursiveSpaces.space F2 branch n (LeafDomain slots)

def sourceProjection {slots projected : RecursiveSpaces.Slots branch n → Fin t → Slot}
    (p : ∀ s k, Projection (slots s k) (projected s k)) :
    Domain slots → Domain projected :=
  RecursiveSpaces.project (fun s => MixedSupport.projectionMap (p s))

@[simp] theorem sourceProjection_apply
    {slots projected : RecursiveSpaces.Slots branch n → Fin t → Slot}
    (p : ∀ s k, Projection (slots s k) (projected s k))
    (x : Domain slots) (s : RecursiveSpaces.Slots branch n) (k : Fin t) :
    sourceProjection p x s k = (p s k).map (x s k) := rfl

theorem H_pullback_le {slots projected : RecursiveSpaces.Slots branch n → Fin t → Slot}
    (p : ∀ s k, Projection (slots s k) (projected s k)) :
    (H projected).map (PointwiseSpaces.pullback F2 (sourceProjection p)) ≤ H slots :=
  RecursiveSpaces.space_project_le branch n (LeafDomain slots) (LeafDomain projected)
    (fun s => MixedSupport.projectionMap (p s))

theorem squareSpace_pullback_le
    {slots projected : RecursiveSpaces.Slots branch n → Fin t → Slot}
    (p : ∀ s k, Projection (slots s k) (projected s k)) :
    (PointwiseSpaces.squareSpace (H projected)).map
        (PointwiseSpaces.pullback F2 (sourceProjection p)) ≤
      PointwiseSpaces.squareSpace (H slots) :=
  PointwiseSpaces.squareSpace_pullback_le _ _ _ (H_pullback_le p)

def HPullback {slots projected : RecursiveSpaces.Slots branch n → Fin t → Slot}
    (p : ∀ s k, Projection (slots s k) (projected s k)) : H projected →ₗ[F2] H slots :=
  RecursiveSpaces.spacePullback (LeafDomain slots) (LeafDomain projected)
    (fun s => MixedSupport.projectionMap (p s))

@[simp] theorem HPullback_apply
    {slots projected : RecursiveSpaces.Slots branch n → Fin t → Slot}
    (p : ∀ s k, Projection (slots s k) (projected s k))
    (f : H projected) (x : Domain slots) :
    (HPullback p f).val x = f.val (sourceProjection p x) := rfl

abbrev childSlots (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → Slot)
    (i : Fin (branch n)) : RecursiveSpaces.Slots branch n → Fin t → Slot :=
  fun s => slots (i, s)

def restrictChild (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → Slot)
    (i : Fin (branch n)) : Domain slots → Domain (childSlots slots i) :=
  RecursiveSpaces.childRestriction (LeafDomain slots) i

theorem child_square_le_H (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → Slot)
    (i : Fin (branch n)) :
    (PointwiseSpaces.squareSpace (H (childSlots slots i))).map
        (PointwiseSpaces.pullback F2 (restrictChild slots i)) ≤ H slots :=
  RecursiveSpaces.child_square_le_space (LeafDomain slots) i

def flatSlots (slots : RecursiveSpaces.Slots branch n → Fin t → Slot) :
    RecursiveSpaces.Slots branch n × Fin t → Slot := fun sk => slots sk.1 sk.2

def flattenAssignment (slots : RecursiveSpaces.Slots branch n → Fin t → Slot) :
    Domain slots ≃ MixedSupport.Assignment (flatSlots slots) where
  toFun x sk := x sk.1 sk.2
  invFun x s k := x (s, k)
  left_inv x := by
    funext s k
    rfl
  right_inv x := by
    funext sk
    cases sk
    rfl

end PerfectCompleteness.TreeSourceSpaces

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_TreeCanonical
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyDomainFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalEdges.coarsen_evaluateLabel _root_.OAI.PerfectCompleteness.CanonicalEdges.restore_coarsen _root_.OAI.PerfectCompleteness.CanonicalKeyShape.assignmentEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalKeyShape.transport_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.restriction_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.restriction_refl _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_refl _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_step _root_.OAI.PerfectCompleteness.RecursiveSampler.combine_zero _root_.OAI.PerfectCompleteness.RecursiveSampler.evaluate_refl _root_.OAI.PerfectCompleteness.RecursiveSampler.evaluate_zeroTape _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.TreeCanonical

open MixedSupport TreeSourceSpaces

noncomputable section

abbrev Location (branch : Nat → Nat) (n t : Nat) := RecursiveSpaces.Slots branch n × Fin t

def locationCount (branch : Nat → Nat) (n t : Nat) : Nat :=
  Fintype.card (Location branch n t)

def numbering (branch : Nat → Nat) (n t : Nat) :
    Location branch n t ≃ Fin (locationCount branch n t) :=
  Fintype.equivFin (Location branch n t)

variable {branch : Nat → Nat} {n t : Nat} {Y : Type*}

def numberedSlots (slots : RecursiveSpaces.Slots branch n → Fin t → Slot) :
    Fin (locationCount branch n t) → Slot :=
  fun j => flatSlots slots ((numbering branch n t).symm j)

def assignmentEquiv (slots : RecursiveSpaces.Slots branch n → Fin t → Slot) :
    Domain slots ≃ MixedSupport.Assignment (numberedSlots slots) :=
  (flattenAssignment slots).trans
    (Equiv.piCongrLeft' (fun sk : Location branch n t => (flatSlots slots sk).Domain)
      (numbering branch n t))

@[simp] theorem assignmentEquiv_apply
    (slots : RecursiveSpaces.Slots branch n → Fin t → Slot) (x : Domain slots)
    (j : Fin (locationCount branch n t)) :
    assignmentEquiv slots x j =
      x ((numbering branch n t).symm j).1 ((numbering branch n t).symm j).2 := rfl

def numberedFunction (slots : RecursiveSpaces.Slots branch n → Fin t → Slot)
    (f : Domain slots → Y) : MixedSupport.Assignment (numberedSlots slots) → Y :=
  f ∘ (assignmentEquiv slots).symm

end

end PerfectCompleteness.TreeCanonical

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_DomainEncoding
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.KeyMetadataEncoding.entryWords_length _root_.OAI.PerfectCompleteness.KeyMetadataEncoding.metadataWords_cons _root_.OAI.PerfectCompleteness.KeyMetadataEncoding.metadataWords_length _root_.OAI.PerfectCompleteness.KeyMetadataEncoding.metadataWords_nil _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.DomainEncoding

open ClauseSupport ReducedDomains

variable {I C Y Z : Type*}

theorem lookupField_eq_of_mem [DecidableEq I] (fields : List (I × SlotKey))
    (i : I) (key : SlotKey) :
    (i, key) ∈ fields → (∀ key', (i, key') ∈ fields → key' = key) →
      lookupField fields i = key := by
  induction fields with
  | nil => simp
  | cons head rest ih =>
      rcases head with ⟨j, k⟩
      intro hmem hunique
      by_cases hij : i = j
      · subst i
        simp only [lookupField]
        exact hunique k (by simp)
      · simp only [lookupField, ite_eq_right hij]
        apply ih
        · apply (List.mem_cons.mp hmem).resolve_left
          intro hpair
          exact hij (congrArg Prod.fst hpair)
        · intro key' hkey'
          exact hunique key' (List.mem_cons_of_mem _ hkey')

theorem lookupField_eq_dropped [DecidableEq I] (fields : List (I × SlotKey)) (i : I) :
    (∀ key, (i, key) ∉ fields) → lookupField fields i = .dropped := by
  induction fields with
  | nil => intro _; rfl
  | cons head rest ih =>
      rcases head with ⟨j, k⟩
      intro hnone
      have hij : i ≠ j := by
        intro hij
        subst i
        exact hnone k (by simp)
      simp only [lookupField, ite_eq_right hij]
      apply ih
      intro key hkey
      exact hnone key (List.mem_cons_of_mem _ hkey)

theorem lookupField_retainedFields {n : Nat} (keys : Fin n → SlotKey) (i : Fin n) :
    lookupField (retainedFields keys) i = keys i := by
  by_cases hdropped : keys i = .dropped
  · calc
      lookupField (retainedFields keys) i = .dropped := by
        apply lookupField_eq_dropped
        intro key hkey
        obtain ⟨hkey, hretained⟩ := (mem_retainedFields keys i key).mp hkey
        exact hretained (hkey.trans hdropped)
      _ = keys i := hdropped.symm
  · apply lookupField_eq_of_mem
    · exact (mem_retainedFields keys i (keys i)).mpr ⟨rfl, hdropped⟩
    · intro key hkey
      exact ((mem_retainedFields keys i key).mp hkey).1

theorem retainedFields_injective {n : Nat} :
    Function.Injective (retainedFields (n := n)) := by
  intro keys keys' h
  funext i
  have hlookup := congrArg (fun fields => lookupField fields i) h
  simpa only [lookupField_retainedFields] using hlookup

theorem keyFields_eq_of_retainedKeys_eq {n : Nat}
    (slots projected : Fin n → MixedSupport.Slot)
    (f : MixedSupport.Assignment slots → Y)
    (g : MixedSupport.Assignment projected → Z)
    (h : MixedSupport.retainedKeys slots f = MixedSupport.retainedKeys projected g) :
    MixedSupport.keyFields slots f = MixedSupport.keyFields projected g :=
  retainedFields_injective h

end PerfectCompleteness.DomainEncoding

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceStrategy
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.clause_eval_extend _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.clause_eval_restrict _root_.OAI.PerfectCompleteness.CanonicalLabelEncoding.labelEmbedding_val _root_.OAI.PerfectCompleteness.KeyMetadataEncoding.entryWords_length _root_.OAI.PerfectCompleteness.KeyMetadataEncoding.metadataWords_cons _root_.OAI.PerfectCompleteness.KeyMetadataEncoding.metadataWords_length _root_.OAI.PerfectCompleteness.KeyMetadataEncoding.metadataWords_nil _root_.OAI.PerfectCompleteness.TreeCanonical.assignmentEquiv_apply _root_.OAI.PerfectCompleteness.TreeSourceSpaces.sourceProjection_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ReducedPartition

variable {X W R Y Z : Type*}

theorem fiber_eq_of_parts_eq_of_reduction_eq
    (rX : X → R) (rW : W → R) (f : X → Y) (g : W → Z)
    (hg : ConstantOnFibers rW g) (hparts : parts rX f = parts rW g)
    (x : X) (w : W) (hpoint : rX x = rW w) :
    fiber rX f x = fiber rW g w := by
  have hmem : fiber rX f x ∈ parts rW g := by
    rw [← hparts]
    exact ⟨x, rfl⟩
  obtain ⟨w', hw'⟩ := hmem
  have hw : rW w ∈ fiber rW g w' := by
    rw [hw', ← hpoint]
    exact self_mem_fiber rX f x
  have hvalue : g w = g w' := (mem_fiber_iff rW g hg w w').mp hw
  exact hw'.symm.trans (fiber_eq_of_output_eq rW g hvalue).symm

end PerfectCompleteness.ReducedPartition

namespace PerfectCompleteness.SourceKeys

open SourceClause ClauseSupport MixedSupport CanonicalKeys

variable {v m n : Nat} {C Y Z : Type*}

def valueOfKey (clauses : Fin m → NormalizedClause v) (assignment : Fin v → Bool) :
    SlotKey → ReducedValue
  | .dropped => .dropped
  | .bit j => .bit (assignmentAt assignment j)
  | .full c _ =>
      .full (if h : c < m then (clauses ⟨c, h⟩).restrict assignment else (false, false, false))

theorem localReduction_endpointValue (clauses : Fin m → NormalizedClause v)
    (assignment : Fin v → Bool) (hsat : ∀ c, (clauses c).clause.eval assignment = true)
    (s : Endpoint v m) (f : C → (slot clauses s).Domain → Y) :
    localReduction (slot clauses s) f (endpointValue clauses assignment hsat s) =
      valueOfKey clauses assignment (localKey (slot clauses s) f) := by
  classical
  cases s with
  | clause c =>
    change C → Answer (clauses c).signs → Y at f
    change clauseReduction f (endpointValue clauses assignment hsat (.clause c)) =
      valueOfKey clauses assignment
        (clauseKey c.val (fun i => ((clauses c).variable i).val) f)
    cases hm : clauseMode f with
    | dropped => simp [clauseReduction, clauseKey, hm, reduceByMode, valueOfKey]
    | bit i =>
      simp only [clauseReduction, clauseKey, hm, reduceByMode, valueOfKey, assignmentAt_fin]
      change ReducedValue.bit (((clauses c).restrict assignment).at i) =
        ReducedValue.bit (assignment ((clauses c).variable i))
      exact congrArg ReducedValue.bit (coordinate_restrict (clauses c) assignment i)
    | full =>
      simp [clauseReduction, clauseKey, hm, reduceByMode, valueOfKey, c.isLt, endpointValue]
  | «variable» j =>
    change C → Bool → Y at f
    change bitReduction f (assignment j) = valueOfKey clauses assignment (bitKey j.val f)
    by_cases hu : Unused f
    · simp [bitReduction, bitKey, hu, valueOfKey]
    · simp [bitReduction, bitKey, hu, valueOfKey]

theorem reduction_realizingAssignment (clauses : Fin m → NormalizedClause v)
    (assignment : Fin v → Bool) (hsat : ∀ c, (clauses c).clause.eval assignment = true)
    (endpoints : Fin n → Endpoint v m)
    (f : Assignment (slot clauses ∘ endpoints) → Y) :
    reduction (slot clauses ∘ endpoints) f (realizingAssignment clauses assignment hsat endpoints) =
      fun i => valueOfKey clauses assignment (keyFields (slot clauses ∘ endpoints) f i) := by
  funext i
  exact localReduction_endpointValue clauses assignment hsat (endpoints i)
    (sectionFunction (slot clauses ∘ endpoints) f i)

theorem evaluated_label_eq_of_key_eq (clauses : Fin m → NormalizedClause v)
    (assignment : Fin v → Bool) (hsat : ∀ c, (clauses c).clause.eval assignment = true)
    (side side' : Side) (source target : Fin n → Endpoint v m)
    (f : Assignment (slot clauses ∘ source) → Y)
    (g : Assignment (slot clauses ∘ target) → Z)
    (hkey : key side (slot clauses ∘ source) f = key side' (slot clauses ∘ target) g) :
    (evaluateLabel (slot clauses ∘ source) f
      (realizingAssignment clauses assignment hsat source)).val =
    (evaluateLabel (slot clauses ∘ target) g
      (realizingAssignment clauses assignment hsat target)).val := by
  have hfields : keyFields (slot clauses ∘ source) f = keyFields (slot clauses ∘ target) g :=
    DomainEncoding.keyFields_eq_of_retainedKeys_eq _ _ f g
      (congrArg (fun k : Key n => k.retained) hkey)
  have hparts : partition (slot clauses ∘ source) f = partition (slot clauses ∘ target) g :=
    congrArg (fun k : Key n => k.partition) hkey
  have hpoint :
      reduction (slot clauses ∘ source) f (realizingAssignment clauses assignment hsat source) =
      reduction (slot clauses ∘ target) g (realizingAssignment clauses assignment hsat target) := by
    rw [reduction_realizingAssignment, reduction_realizingAssignment, hfields]
  exact ReducedPartition.fiber_eq_of_parts_eq_of_reduction_eq
    (reduction (slot clauses ∘ source) f) (reduction (slot clauses ∘ target) g) f g
    (constantOnFibers (slot clauses ∘ target) g) hparts _ _ hpoint

end PerfectCompleteness.SourceKeys

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_SourceCompleteness
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceCompleteness

open SourceClause ClauseSupport MixedSupport CanonicalKeys SourceKeys

variable {v m n : Nat} {Y Z : Type*}

structure Presentation (clauses : Fin m → NormalizedClause v) (n : Nat) (Y : Type*) where
  endpoints : Fin n → Endpoint v m
  joint : Assignment (slot clauses ∘ endpoints) → Y

variable {clauses : Fin m → NormalizedClause v} {side : Side}

noncomputable def presentationKey (side : Side) (P : Presentation clauses n Y) : Key n :=
  key side (slot clauses ∘ P.endpoints) P.joint

noncomputable def generatedKeys (side : Side) (clauses : Fin m → NormalizedClause v)
    (n : Nat) (Y : Type*) : Set (Key n) :=
  Set.range (presentationKey (clauses := clauses) (n := n) (Y := Y) side)

abbrev Vertex (side : Side) (clauses : Fin m → NormalizedClause v) (n : Nat) (Y : Type*) :=
  ↥(generatedKeys side clauses n Y)

abbrev VertexLabel (vertex : Vertex side clauses n Y) :=
  {part : Set (Fin n → ReducedValue) // part ∈ vertex.val.partition}

noncomputable def representation (vertex : Vertex side clauses n Y) :
    Presentation clauses n Y :=
  vertex.property.choose

theorem representation_key (vertex : Vertex side clauses n Y) :
    presentationKey side (representation vertex) = vertex.val :=
  vertex.property.choose_spec

noncomputable def evaluatedLabel (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true)
    (P : Presentation clauses n Y) : Label (slot clauses ∘ P.endpoints) P.joint :=
  evaluateLabel (slot clauses ∘ P.endpoints) P.joint
    (realizingAssignment clauses assignment hsat P.endpoints)

noncomputable def strategy (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true)
    (vertex : Vertex side clauses n Y) : VertexLabel vertex := by
  refine ⟨(evaluatedLabel assignment hsat (representation vertex)).val, ?_⟩
  rw [← representation_key vertex]
  exact (evaluatedLabel assignment hsat (representation vertex)).property

theorem strategy_value_eq (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true)
    (vertex : Vertex side clauses n Y) (P : Presentation clauses n Z)
    (hkey : presentationKey side P = vertex.val) :
    (strategy assignment hsat vertex).val = (evaluatedLabel assignment hsat P).val := by
  change (evaluatedLabel assignment hsat (representation vertex)).val =
    (evaluatedLabel assignment hsat P).val
  exact evaluated_label_eq_of_key_eq clauses assignment hsat side side
    (representation vertex).endpoints P.endpoints
    (representation vertex).joint P.joint
    ((representation_key vertex).trans hkey.symm)

def Presentation.postcompose (P : Presentation clauses n Y) (p : Y → Z) :
    Presentation clauses n Z where
  endpoints := P.endpoints
  joint := p ∘ P.joint

end PerfectCompleteness.SourceCompleteness

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalArrays
attribute [-instance] _root_.OAI.PerfectCompleteness.RecursiveSampler.drawIndexDecidableEq _root_.OAI.PerfectCompleteness.RecursiveSampler.drawIndexFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.RecursiveSampler.combine_zero _root_.OAI.PerfectCompleteness.RecursiveSampler.evaluate_refl _root_.OAI.PerfectCompleteness.RecursiveSampler.evaluate_zeroTape _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HierarchicalArrays

open TreeSourceSpaces

namespace Nodes

variable {branch : Nat → Nat}

def path : {n : Nat} → (node : Nodes branch n) →
    DescendantSpaces.Path branch n (height node)
  | 0, node => nomatch node
  | n + 1, .inl _ => .refl (n + 1)
  | _ + 1, .inr (i, node) => .step i (path node)

theorem height_le {n : Nat} (node : Nodes branch n) : height node ≤ n :=
  (path node).height_le

end Nodes

variable {branch : Nat → Nat} {n t : Nat}

def nodeSlots (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (node : Nodes branch n) : RecursiveSpaces.Slots branch (Nodes.height node) →
      Fin t → MixedSupport.Slot :=
  fun s => slots ((Nodes.path node).slotEmbedding s)

def restrictNode (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (node : Nodes branch n) : Domain slots → Domain (nodeSlots slots node) :=
  (Nodes.path node).restriction (LeafDomain slots)

theorem restrictNode_surjective
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (node : Nodes branch n) : Function.Surjective (restrictNode slots node) :=
  (Nodes.path node).restriction_surjective (LeafDomain slots) (fun _ => inferInstance)

abbrev Block (rows : Nat → Nat) (node : Nodes branch n) := Fin (rows (Nodes.height node)) → F2

abbrev Arrays (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (rows : Nat → Nat) :=
  ∀ node : Nodes branch n, Fin (rows (Nodes.height node)) → H (nodeSlots slots node)

def joint {slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot}
    {rows : Nat → Nat} (arrays : Arrays slots rows) :
    Domain slots → ∀ node : Nodes branch n, Block rows node :=
  fun x node row => (arrays node row).val (restrictNode slots node x)

@[simp] theorem joint_component
    {slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot}
    {rows : Nat → Nat} (arrays : Arrays slots rows) (x : Domain slots)
    (node : Nodes branch n) (row : Fin (rows (Nodes.height node))) :
    joint arrays x node row = (arrays node row).val (restrictNode slots node x) := rfl

abbrev Output (branch : Nat → Nat) (n : Nat) (rows : Nat → Nat) : Type :=
  BlockQuotient.JointOutput (fun node : Nodes branch n => Block rows node) PUnit

def fullJoint {slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot}
    {rows : Nat → Nat} (arrays : Arrays slots rows) : Domain slots → Output branch n rows :=
  fun x => (joint arrays x, PUnit.unit)

variable {v m : Nat}

def sourceSlots (clauses : Fin m → SourceClause.NormalizedClause v)
    (endpoints : RecursiveSpaces.Slots branch n → Fin t → SourceKeys.Endpoint v m) :
    RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot :=
  fun s k => SourceKeys.slot clauses (endpoints s k)

end PerfectCompleteness.HierarchicalArrays

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_NodeEmbedding
attribute [-instance] _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.RecursiveSampler.combine_zero _root_.OAI.PerfectCompleteness.RecursiveSampler.evaluate_refl _root_.OAI.PerfectCompleteness.RecursiveSampler.evaluate_zeroTape _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.NodeEmbedding

open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

abbrev NumberedDomain (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :=
  MixedSupport.Assignment (TreeCanonical.numberedSlots slots)

abbrev NodeH (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (node : Nodes branch n) := H (nodeSlots slots node)

variable (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (node : Nodes branch n)

def numberedRestriction : NumberedDomain slots → Domain (nodeSlots slots node) :=
  restrictNode slots node ∘ (TreeCanonical.assignmentEquiv slots).symm

theorem numberedRestriction_surjective : Function.Surjective (numberedRestriction slots node) :=
  (restrictNode_surjective slots node).comp (TreeCanonical.assignmentEquiv slots).symm.surjective

theorem pullback_injective :
    Function.Injective (PointwiseSpaces.pullback F2 (numberedRestriction slots node)) :=
  PointwiseSpaces.pullback_injective _ (numberedRestriction_surjective slots node)

def RowSpace : Submodule F2 (NumberedDomain slots → F2) :=
  (NodeH slots node).map (PointwiseSpaces.pullback F2 (numberedRestriction slots node))

def equiv : NodeH slots node ≃ₗ[F2] RowSpace slots node :=
  Submodule.equivMapOfInjective
    (PointwiseSpaces.pullback F2 (numberedRestriction slots node))
    (pullback_injective slots node) (NodeH slots node)

def embed : NodeH slots node →ₗ[F2] RowSpace slots node :=
  (equiv slots node).toLinearMap

@[simp] theorem equiv_apply (f : NodeH slots node) (x : NumberedDomain slots) :
    (equiv slots node f).val x = f.val (numberedRestriction slots node x) := rfl

@[simp] theorem embed_apply (f : NodeH slots node) (x : NumberedDomain slots) :
    (embed slots node f).val x = f.val (numberedRestriction slots node x) := rfl

def rowsEquiv (ℓ : Nat) :
    (Fin ℓ → NodeH slots node) ≃ₗ[F2] (Fin ℓ → RowSpace slots node) :=
  LinearEquiv.piCongrRight (fun _ : Fin ℓ => equiv slots node)

@[simp] theorem rowsEquiv_apply (ℓ : Nat) (f : Fin ℓ → NodeH slots node) (i : Fin ℓ) :
    rowsEquiv slots node ℓ f i = embed slots node (f i) := rfl

theorem squareSpace_eq :
    PointwiseSpaces.squareSpace (RowSpace slots node) =
      (PointwiseSpaces.squareSpace (NodeH slots node)).map
        (PointwiseSpaces.pullback F2 (numberedRestriction slots node)) :=
  (PointwiseSpaces.squareSpace_map_pullback
    (numberedRestriction slots node) (NodeH slots node)).symm


variable {slots} {rows : Nat → Nat}

def embeddedRows (arrays : Arrays slots rows) (node : Nodes branch n) :
    Fin (rows (Nodes.height node)) → RowSpace slots node :=
  fun i => embed slots node (arrays node i)

@[simp] theorem embeddedRows_apply (arrays : Arrays slots rows) (node : Nodes branch n)
    (i : Fin (rows (Nodes.height node))) (x : NumberedDomain slots) :
    (embeddedRows arrays node i).val x =
      (TreeCanonical.numberedFunction slots (fullJoint arrays) x).1 node i := rfl

def matrix (arrays : Arrays slots rows) (node : Nodes branch n) :
    Module.Dual F2 (RowSpace slots node) →ₗ[F2] Block rows node :=
  EvaluationMatrix.ofRows (RowSpace slots node) (embeddedRows arrays node)

@[simp] theorem matrix_evaluate (arrays : Arrays slots rows) (node : Nodes branch n)
    (x : NumberedDomain slots) :
    EvaluationMatrix.evaluate (RowSpace slots node) (matrix arrays node) x =
      (TreeCanonical.numberedFunction slots (fullJoint arrays) x).1 node := rfl

end
end PerfectCompleteness.NodeEmbedding

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_HierarchicalMatrixTable
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.RecursiveSampler.combine_zero _root_.OAI.PerfectCompleteness.RecursiveSampler.evaluate_refl _root_.OAI.PerfectCompleteness.RecursiveSampler.evaluate_zeroTape _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val
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

abbrev Background := (j : {j : Nodes branch n // j ≠ node}) →
  Fin (rows (Nodes.height j.val)) → NodeEmbedding.NodeH slots j.val

abbrev SideOutput : Type :=
  BlockQuotient.OtherBlocks (fun j : Nodes branch n => Block rows j) node × PUnit.{1}

abbrev Matrix := Module.Dual F2 (NodeEmbedding.RowSpace slots node) →ₗ[F2] Block rows node

def nativeRows (X : Matrix (rows := rows) slots node) :
    Fin (rows (Nodes.height node)) → NodeEmbedding.NodeH slots node :=
  fun i => (NodeEmbedding.equiv slots node).symm
    (EvaluationMatrix.rows (NodeEmbedding.RowSpace slots node) X i)

def assemble (background : Background (rows := rows) slots node)
    (X : Matrix (rows := rows) slots node) : Arrays slots rows :=
  fun j => if h : j = node then h.symm ▸ nativeRows slots node X else background ⟨j, h⟩

@[simp] theorem assemble_selected (background : Background (rows := rows) slots node)
    (X : Matrix (rows := rows) slots node) :
    assemble slots node background X node = nativeRows slots node X := by
  simp [assemble]

@[simp] theorem assemble_other (background : Background (rows := rows) slots node)
    (X : Matrix (rows := rows) slots node) (j : {j : Nodes branch n // j ≠ node}) :
    assemble slots node background X j.val = background j := by
  simp only [assemble, dite_eq_right j.property]

def other (background : Background (rows := rows) slots node)
    (x : NodeEmbedding.NumberedDomain slots) : SideOutput (rows := rows) node :=
  (fun j i => (background j i).val (NodeEmbedding.numberedRestriction slots j.val x), PUnit.unit)

end
end PerfectCompleteness.HierarchicalMatrixTable

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_BucketQuotientAgreement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.BucketQuotientAgreement

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open BucketSampler (F2 Direction Tape)

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

variable {Ω Y : Type*} [Fintype Y]
  (V : Submodule F2 (Ω → F2)) [Fintype V] [FiniteDimensional F2 V]
  (ℓ : Nat) (W : Submodule F2 V)

def directionCollision
    (f : (Module.Dual F2 (V ⧸ W) →ₗ[F2] (Fin ℓ → F2)) → Option Y)
    (a : Direction ℓ) : ℝ :=
  ((BucketSampler.tapeLaw ℓ (FiniteDistribution.uniform V)).product
    (FiniteDistribution.uniform V)).probability
      (fun p => TwoResponseCollision.collision f
        (MatrixRowQuotient.projectMatrix W (BucketMatrixResampling.assembledMatrix V ℓ p.1),
          MatrixRowQuotient.projectMatrix W
            (BucketMatrixResampling.assembledMatrix V ℓ (Function.update p.1 a p.2))))

def agreement
    (f : (Module.Dual F2 (V ⧸ W) →ₗ[F2] (Fin ℓ → F2)) → Option Y) : ℝ :=
  𝔼 a : Direction ℓ, directionCollision V ℓ W f a

end
end PerfectCompleteness.BucketQuotientAgreement

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_SourceGame
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceGame

open SourceClause UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

theorem decodeLabel_legal (signs : Triple) (label : Fin 7) :
    localEval signs (decodeLabel signs label) = true :=
  (mem_satisfyingTriples signs _).mp (decodeLabel_mem signs label)

def encodeLabel (signs label : Triple) (legal : localEval signs label = true) : Fin 7 :=
  ⟨(satisfyingTriples signs).idxOf label, by
    have h := List.idxOf_lt_length_of_mem ((mem_satisfyingTriples signs label).mpr legal)
    simpa using h⟩

@[simp] theorem decodeLabel_encodeLabel (signs label : Triple)
    (legal : localEval signs label = true) :
    decodeLabel signs (encodeLabel signs label legal) = label := by
  exact List.getElem_idxOf _

def projection {n m : Nat} (clauses : Fin m → NormalizedClause n)
    (e : Occurrence m) (answer : Fin 7) : Bool :=
  (decodeLabel (clauses e.1).signs answer).at e.2

noncomputable section

def game {n m : Nat} [NeZero m] (clauses : Fin m → NormalizedClause n) :
    OccurrenceGame (Occurrence m) (Fin m) (Fin n) (Fin 7) Bool :=
  OccurrenceGame.ofProjection (FiniteDistribution.uniform (Occurrence m))
    Prod.fst (occurrenceVariable clauses) (projection clauses)

def endpointPredicate {n m : Nat} (clauses : Fin m → NormalizedClause n)
    (c : Fin m) (v : Fin n) (a : Fin 7) (b : Bool) : Bool :=
  decide (∃ i : Fin 3, (clauses c).variable i = v ∧
    (decodeLabel (clauses c).signs a).at i = b)

theorem endpointPredicate_eq_true {n m : Nat} (clauses : Fin m → NormalizedClause n)
    (c : Fin m) (v : Fin n) (a : Fin 7) (b : Bool) :
    endpointPredicate clauses c v a b = true ↔
      ∃ i : Fin 3, (clauses c).variable i = v ∧
        (decodeLabel (clauses c).signs a).at i = b := by
  exact decide_eq_true_iff

def presentation {n m : Nat} [NeZero m]
    (clauses : Fin m → NormalizedClause n) : (game clauses).EndpointPresentation where
  predicate := endpointPredicate clauses
  agrees e a b := by
    apply Bool.eq_iff_iff.mpr
    rw [endpointPredicate_eq_true]
    simp only [game, OccurrenceGame.ofProjection, occurrenceVariable, decide_eq_true_eq]
    constructor
    · intro h
      exact ⟨e.2, rfl, h⟩
    · rintro ⟨i, sameVariable, h⟩
      have samePosition : i = e.2 := (clauses e.1).distinct i e.2 sameVariable
      simpa [projection, samePosition] using h

def questionGame {n m : Nat} [NeZero m] (clauses : Fin m → NormalizedClause n) :
    Game (Fin m) (Fin n) (Fin 7) Bool :=
  (game clauses).toGame (presentation clauses)

@[simp] theorem questionGame_success {n m : Nat} [NeZero m]
    (clauses : Fin m → NormalizedClause n) (strategy : Strategy (Fin m) (Fin n) (Fin 7) Bool) :
    (questionGame clauses).success strategy = (game clauses).success strategy :=
  (game clauses).toGame_success (presentation clauses) strategy

end
end PerfectCompleteness.SourceGame

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_KeyFiniteness
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyDomainFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CanonicalKeys

open ClauseSupport MixedSupport
open scoped BigOperators

variable {n : Nat} {Y : Type*}

instance keyLabel_nonempty (side : Side) (slots : Fin n → Slot)
    (f : Assignment slots → Y) : Nonempty (KeyLabel (key side slots f)) := by
  change Nonempty (Label slots f)
  infer_instance

def answerEquivFinSeven (signs : SourceClause.Triple) : Answer signs ≃ Fin 7 where
  toFun u := SourceGame.encodeLabel signs u.val
    ((SourceClause.mem_satisfyingTriples signs u.val).mp u.property)
  invFun i := ⟨SourceGame.decodeLabel signs i, SourceGame.decodeLabel_mem signs i⟩
  left_inv u := by
    apply Subtype.ext
    exact SourceGame.decodeLabel_encodeLabel signs u.val _
  right_inv i := by
    apply SourceGame.decodeLabel_injective signs
    exact SourceGame.decodeLabel_encodeLabel signs (SourceGame.decodeLabel signs i) _

end PerfectCompleteness.CanonicalKeys

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_CanonicalGameLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CanonicalGame

open SourceClause MixedSupport CanonicalKeys BlockQuotient SourceCompleteness
open UniqueGamesTheorem.Foundations.Games CompletionSoundness

noncomputable section

variable {v m n : Nat} {E I B : Type*} {V : I → Type*}
  [DecidableEq I] [∀ i, AddCommGroup (V i)] [∀ i, Module DirectionQuotient.F2 (V i)]

structure BlockFamily (clauses : Fin m → NormalizedClause v) (n : Nat)
    (E I : Type*) (V : I → Type*) (B : Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module DirectionQuotient.F2 (V i)] where
  presentation : E → Presentation clauses n (JointOutput V B)
  selected : E → I
  direction : ∀ e, V (selected e)
  nonzero : ∀ e, direction e ≠ 0

variable {clauses : Fin m → NormalizedClause v}
  (F : BlockFamily clauses n E I V B)

abbrev RightOutput (e : E) :=
  DirectionQuotient.Space (F.direction e) × (OtherBlocks V (F.selected e) × B)

def rightPresentation (e : E) : Presentation clauses n (RightOutput F e) :=
  (F.presentation e).postcompose (projectBlock (F.selected e) (F.direction e))

def leftKey (e : E) : Key n := presentationKey .left (F.presentation e)

def rightKey (e : E) : Key n := presentationKey .right (rightPresentation F e)

abbrev LeftVertex := ↥(Set.range (leftKey F))
abbrev RightVertex := ↥(Set.range (rightKey F))

def leftAt (e : E) : LeftVertex F := ⟨leftKey F e, ⟨e, rfl⟩⟩
def rightAt (e : E) : RightVertex F := ⟨rightKey F e, ⟨e, rfl⟩⟩

abbrev LeftLabel (q : LeftVertex F) := KeyLabel q.val
abbrev RightLabel (q : RightVertex F) := KeyLabel q.val

instance leftVertex_finite [Finite E] : Finite (LeftVertex F) := by
  apply Finite.of_surjective (leftAt F)
  rintro ⟨k, e, rfl⟩
  exact ⟨e, rfl⟩

instance rightVertex_finite [Finite E] : Finite (RightVertex F) := by
  apply Finite.of_surjective (rightAt F)
  rintro ⟨k, e, rfl⟩
  exact ⟨e, rfl⟩

instance leftLabel_nonempty (q : LeftVertex F) : Nonempty (LeftLabel F q) := by
  rcases q with ⟨k, e, rfl⟩
  exact keyLabel_nonempty .left _ (F.presentation e).joint

instance rightLabel_nonempty (q : RightVertex F) : Nonempty (RightLabel F q) := by
  rcases q with ⟨k, e, rfl⟩
  exact keyLabel_nonempty .right _ (rightPresentation F e).joint

def edge (e : E) (P : LeftLabel F (leftAt F e)) : RightLabel F (rightAt F e) :=
  CanonicalEdges.coarsen
    (SourceKeys.slot clauses ∘ (F.presentation e).endpoints) (F.presentation e).joint
    (projectBlock (F.selected e) (F.direction e)) P

theorem edge_at_most_two [Finite I] [∀ i, Finite (V i)] [Finite B]
    (e : E) (Q : RightLabel F (rightAt F e)) :
    Nat.card {P : LeftLabel F (leftAt F e) // edge F e P = Q} ≤ 2 :=
  coarsenBlock_at_most_two
    (SourceKeys.slot clauses ∘ (F.presentation e).endpoints) (F.presentation e).joint
    (F.selected e) (F.direction e) (F.nonzero e) Q

def game [Fintype E] (μ : FiniteDistribution E) :
    LegalProjectionGame E (LeftVertex F) (RightVertex F) (LeftLabel F) (RightLabel F) where
  occurrences := μ
  left := leftAt F
  right := rightAt F
  projection := edge F

def leftAmbientVertex (q : LeftVertex F) :
    SourceCompleteness.Vertex .left clauses n (JointOutput V B) :=
  ⟨q.val, by
    obtain ⟨e, he⟩ := q.property
    exact ⟨F.presentation e, he⟩⟩

def rightAmbientVertex (q : RightVertex F) :
    SourceCompleteness.Vertex .right clauses n (RightOutput F q.property.choose) :=
  ⟨q.val, ⟨rightPresentation F q.property.choose, q.property.choose_spec⟩⟩

def leftStrategy (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true) (q : LeftVertex F) : LeftLabel F q :=
  SourceCompleteness.strategy assignment hsat (leftAmbientVertex F q)

def rightStrategy (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true) (q : RightVertex F) : RightLabel F q :=
  SourceCompleteness.strategy assignment hsat (rightAmbientVertex F q)

omit [DecidableEq I] in
theorem leftStrategy_at (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true) (e : E) :
    leftStrategy F assignment hsat (leftAt F e) =
      SourceCompleteness.evaluatedLabel assignment hsat (F.presentation e) := by
  apply Subtype.ext
  exact SourceCompleteness.strategy_value_eq assignment hsat
    (leftAmbientVertex F (leftAt F e)) (F.presentation e) rfl

theorem rightStrategy_at (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true) (e : E) :
    rightStrategy F assignment hsat (rightAt F e) =
      SourceCompleteness.evaluatedLabel assignment hsat (rightPresentation F e) := by
  apply Subtype.ext
  exact SourceCompleteness.strategy_value_eq assignment hsat
    (rightAmbientVertex F (rightAt F e)) (rightPresentation F e) rfl

def satisfyingStrategy (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true) :
    LegalStrategy (LeftLabel F) (RightLabel F) :=
  ⟨leftStrategy F assignment hsat, rightStrategy F assignment hsat⟩

theorem edge_strategy (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true) (e : E) :
    edge F e (leftStrategy F assignment hsat (leftAt F e)) =
      rightStrategy F assignment hsat (rightAt F e) := by
  apply Subtype.ext
  have hc := CanonicalEdges.coarsen_evaluateLabel
    (SourceKeys.slot clauses ∘ (F.presentation e).endpoints) (F.presentation e).joint
    (projectBlock (F.selected e) (F.direction e))
    (SourceKeys.realizingAssignment clauses assignment hsat (F.presentation e).endpoints)
  calc
    (edge F e (leftStrategy F assignment hsat (leftAt F e))).val =
        (edge F e (SourceCompleteness.evaluatedLabel assignment hsat (F.presentation e))).val :=
      congrArg (fun P : LeftLabel F (leftAt F e) => (edge F e P).val)
        (leftStrategy_at F assignment hsat e)
    _ = (SourceCompleteness.evaluatedLabel assignment hsat (rightPresentation F e)).val :=
      congrArg (fun P : RightLabel F (rightAt F e) => P.val) hc
    _ = (rightStrategy F assignment hsat (rightAt F e)).val :=
      congrArg (fun P : RightLabel F (rightAt F e) => P.val)
        (rightStrategy_at F assignment hsat e).symm

theorem success_satisfyingStrategy [Fintype E] (μ : FiniteDistribution E)
    (assignment : Fin v → Bool) (hsat : ∀ c, (clauses c).clause.eval assignment = true) :
    (game F μ).success (satisfyingStrategy F assignment hsat) = 1 := by
  have hw : (game F μ).wins (satisfyingStrategy F assignment hsat) = fun _ => true := by
    funext e
    change @decide (edge F e (leftStrategy F assignment hsat (leftAt F e)) =
      rightStrategy F assignment hsat (rightAt F e)) (Classical.propDecidable _) = true
    exact (@decide_eq_true_iff _ (Classical.propDecidable _)).mpr
      (edge_strategy F assignment hsat e)
  change μ.probability ((game F μ).wins (satisfyingStrategy F assignment hsat)) = 1
  rw [hw]
  exact μ.probability_true

end

end PerfectCompleteness.CanonicalGame


namespace PerfectCompleteness.CanonicalGameStrategy

open SourceClause MixedSupport CanonicalKeys BlockQuotient CanonicalGame
open CompletionSoundness
open scoped Classical

noncomputable section

variable {v m n : Nat} {E I B : Type*} {V : I → Type*}
  [DecidableEq I] [∀ i, AddCommGroup (V i)] [∀ i, Module DirectionQuotient.F2 (V i)]
  {clauses : Fin m → NormalizedClause v} (F : BlockFamily clauses n E I V B)

def support : Set (Key n) := Set.range (leftKey F) ∪ Set.range (rightKey F)

def onSupport (s : LegalStrategy (LeftLabel F) (RightLabel F))
    (k : ↥(support F)) : KeyLabel k.val :=
  if h : k.val ∈ Set.range (leftKey F) then s.1 ⟨k.val, h⟩
  else s.2 ⟨k.val, k.property.resolve_left h⟩

def extend (s : LegalStrategy (LeftLabel F) (RightLabel F)) : KeyStrategy.Strategy n :=
  KeyStrategy.extend (support F) (onSupport F s)

end

end PerfectCompleteness.CanonicalGameStrategy


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_LocalCompletionFamily
attribute [-simp] _root_.OAI.PerfectCompleteness.LocalCompletionSerialization.projection_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LocalCompletionFamily

open scoped Classical
open CompletionProbability

noncomputable section

theorem table_packSampler {q n : Nat} (hn : 0 < n) (hbound : n ≤ 2 * q)
    (sampler : Fin n → Fin (2 * q) → Fin q)
    (seed : Fin (activeCount (packSampler hn hbound sampler))) :
    table (packSampler hn hbound sampler) seed =
      sampler (packedSeedEquiv hn hbound sampler seed) := by
  have hs : seed.val < n := (packedSeedEquiv hn hbound sampler seed).isLt
  change (if h : seed.val < n then sampler ⟨seed.val, h⟩ else sampler ⟨0, hn⟩) =
    sampler ⟨seed.val, hs⟩
  rw [dite_eq_left hs]

theorem uniformProbability_packSampler {q n : Nat}
    (hn : 0 < n) (hbound : n ≤ 2 * q)
    (sampler : Fin n → Fin (2 * q) → Fin q) (a : Fin (2 * q)) (b : Fin q) :
    uniformProbability (fun seed : Fin (activeCount (packSampler hn hbound sampler)) =>
      table (packSampler hn hbound sampler) seed a = b) =
    uniformProbability (fun seed : Fin n => sampler seed a = b) := by
  have hevent :
      (fun seed : Fin (activeCount (packSampler hn hbound sampler)) =>
        table (packSampler hn hbound sampler) seed a = b) =
      (fun seed : Fin (activeCount (packSampler hn hbound sampler)) =>
        sampler (packedSeedEquiv hn hbound sampler seed) a = b) := by
    funext seed
    exact congrArg (fun f : Fin (2 * q) → Fin q => f a = b)
      (table_packSampler hn hbound sampler seed)
  exact (congrArg
    (uniformProbability (Ω := Fin (activeCount (packSampler hn hbound sampler))))
    hevent).trans
      (uniformProbability_equiv
        (Ω := Fin (activeCount (packSampler hn hbound sampler))) (Γ := Fin n)
        (packedSeedEquiv hn hbound sampler) (fun seed : Fin n => sampler seed a = b))

theorem correct_packSampler {q n : Nat} (input : Input q)
    (hn : 0 < n) (hbound : n ≤ 2 * q)
    (sampler : Fin n → Fin (2 * q) → Fin q)
    (hext : ∀ seed l, sampler seed (legalEmbedding input l) = legalProjection input l)
    (hexact : ∀ seed b, Fintype.card {a : Fin (2 * q) // sampler seed a = b} = 2)
    (hprob : ∀ (a : Illegal (legalEmbedding input)) (b : Fin q),
      uniformProbability (fun seed : Fin n => sampler seed a.val = b) ≤
        2 / (2 * q - Fintype.card (Legal input) : Nat)) :
    Correct input (packSampler hn hbound sampler) := by
  constructor
  · intro seed a ha
    rw [table_packSampler]
    exact hext (packedSeedEquiv hn hbound sampler seed) ⟨a, ha⟩
  · intro seed b
    rw [table_packSampler]
    have hb := hexact (packedSeedEquiv hn hbound sampler seed) b
    simp only [← Nat.card_eq_fintype_card] at hb ⊢
    exact hb
  · intro a ha b
    rw [uniformProbability_packSampler]
    have hillegal : a ∉ Set.range (legalEmbedding input) := by
      rintro ⟨l, hl⟩
      have hval : l.val = a := hl
      exact ha (hval ▸ l.property)
    exact hprob ⟨a, hillegal⟩ b

theorem exists_correct {q : Nat} (hq : 0 < q) (input : Input q)
    (hadmissible : Admissible input) : ∃ result : Result q, Correct input result := by
  obtain ⟨n, hn, hsize, sampler, hext, hexact, hprob⟩ :=
    exists_completion_sampler_bounded (legalEmbedding input) (legalProjection input)
      (by
        intro b
        rw [Fintype.card_eq_nat_card]
        change Nat.card {l : Legal input // input.2 l.val = b} ≤ 2
        have hb := hadmissible b
        rw [Fintype.card_eq_nat_card] at hb
        exact hb)
      (by simp)
  have hfull : 0 < 2 * q := Nat.mul_pos (by decide) hq
  have hbound : n ≤ 2 * q := by
    have hsize' : n ≤ max 1 (2 * q - Fintype.card (Legal input)) := by
      simpa only [Fintype.card_fin] using hsize
    exact hsize'.trans (max_le (Nat.succ_le_of_lt hfull) (Nat.sub_le _ _))
  refine ⟨packSampler hn hbound sampler,
    correct_packSampler input hn hbound sampler hext ?_ ?_⟩
  · intro seed b
    have hb := hexact seed b
    simp only [← Nat.card_eq_fintype_card] at hb ⊢
    exact hb
  · intro a b
    simpa only [Fintype.card_fin] using (hprob a b).2

def lookup {q : Nat} (hq : 0 < q) (input : Input q) : Result q :=
  if h : Admissible input then Classical.choose (exists_correct hq input h) else fallback hq

theorem lookup_correct {q : Nat} (hq : 0 < q) (input : Input q)
    (hadmissible : Admissible input) : Correct input (lookup hq input) := by
  unfold lookup
  rw [dite_eq_left hadmissible]
  exact Classical.choose_spec (exists_correct hq input hadmissible)

end
end PerfectCompleteness.LocalCompletionFamily

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_FlexibleLocalCompletionLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.LocalCompletionSerialization.projection_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.FlexibleLocalCompletion

open scoped Classical
open CompletionSoundness CompletionSoundness.LegalProjectionGame

noncomputable section

variable {E Q₁ Q₂ : Type*} [Fintype E]
  {L : Q₁ → Type*} {R : Q₂ → Type*} [∀ x, Fintype (L x)]
  {q : Nat}
  (G : LegalProjectionGame E Q₁ Q₂ L R)
  (legalL : ∀ x, L x ↪ Fin (2 * q)) (legalR : ∀ y, R y ↪ Fin q)

structure Compatible (data : E → LocalCompletionFamily.Input q) : Prop where
  mask : ∀ e a, (data e).1 a = true ↔ a ∈ Set.range (legalL (G.left e))
  image : ∀ e l, (data e).2 (legalL (G.left e) l) =
    legalR (G.right e) (G.projection e l)

variable (data : E → LocalCompletionFamily.Input q)
  (compatible : Compatible G legalL legalR data)

def localLegalEquiv (e : E) : L (G.left e) ≃ LocalCompletionFamily.Legal (data e) :=
  (Equiv.ofInjective (legalL (G.left e)) (legalL (G.left e)).injective).trans
    (Equiv.subtypeEquivRight (fun a => (compatible.mask e a).symm))

omit [∀ x, Fintype (L x)] in
@[simp] theorem localLegalEquiv_apply_val (e : E) (l : L (G.left e)) :
    (localLegalEquiv G legalL legalR data compatible e l).val = legalL (G.left e) l := rfl

include legalL legalR compatible in
theorem card_legal (e : E) :
    Fintype.card (LocalCompletionFamily.Legal (data e)) = Fintype.card (L (G.left e)) :=
  (Fintype.card_congr (localLegalEquiv G legalL legalR data compatible e)).symm

include legalL legalR compatible in

theorem input_admissible
    (hsmall : ∀ e b, Fintype.card {l : L (G.left e) // G.projection e l = b} ≤ 2)
    (e : E) : LocalCompletionFamily.Admissible (data e) := by
  intro b
  rw [Fintype.card_eq_nat_card]
  have hmatch (l : L (G.left e)) :
      (data e).2 (localLegalEquiv G legalL legalR data compatible e l).val =
        legalR (G.right e) (G.projection e l) := by
    rw [localLegalEquiv_apply_val]
    exact compatible.image e l
  let fibers : {l : L (G.left e) // legalR (G.right e) (G.projection e l) = b} ≃
      {a : LocalCompletionFamily.Legal (data e) // (data e).2 a.val = b} :=
    (localLegalEquiv G legalL legalR data compatible e).subtypeEquiv
      (fun l => by rw [hmatch l])
  have hcard := Nat.card_congr fibers
  have hbound := embedded_fiber_le_two (legalR (G.right e)) (G.projection e) (hsmall e) b
  rw [Fintype.card_eq_nat_card] at hbound
  exact hcard.symm.le.trans hbound

def result (hq : 0 < q) (e : E) : LocalCompletionFamily.Result q :=
  LocalCompletionFamily.lookup hq (data e)

include legalL legalR compatible in
theorem result_correct (hq : 0 < q)
    (hsmall : ∀ e b, Fintype.card {l : L (G.left e) // G.projection e l = b} ≤ 2)
    (e : E) : LocalCompletionFamily.Correct (data e) (result data hq e) :=
  LocalCompletionFamily.lookup_correct hq (data e)
    (input_admissible G legalL legalR data compatible hsmall e)

def family (hq : 0 < q)
    (hsmall : ∀ e b, Fintype.card {l : L (G.left e) // G.projection e l = b} ≤ 2) :
    G.CompletionFamily legalL legalR where
  size e := LocalCompletionFamily.activeCount (result data hq e)
  positive e := LocalCompletionFamily.activeCount_positive _
  map e := LocalCompletionFamily.table (result data hq e)
  agrees e seed l :=
    ((result_correct G legalL legalR data compatible hq hsmall e).agrees seed
      (legalL (G.left e) l) ((compatible.mask e _).2 ⟨l, rfl⟩)).trans
      (compatible.image e l)
  exact_two e seed b := by
    rw [Fintype.card_eq_nat_card]
    have h := (result_correct G legalL legalR data compatible hq hsmall e).exact_two seed b
    rw [Fintype.card_eq_nat_card] at h
    exact h
  illegal_probability e a b := by
    have hmask : (data e).1 a.val ≠ true := by
      intro h
      exact a.property ((compatible.mask e a.val).1 h)
    have h := (result_correct G legalL legalR data compatible hq hsmall e).illegal_probability
      a.val hmask b
    simpa only [Fintype.card_fin, card_legal G legalL legalR data compatible] using h

@[simp] theorem family_size (hq : 0 < q)
    (hsmall : ∀ e b, Fintype.card {l : L (G.left e) // G.projection e l = b} ≤ 2) (e : E) :
    (family G legalL legalR data compatible hq hsmall).size e =
      LocalCompletionFamily.activeCount (LocalCompletionFamily.lookup hq (data e)) := rfl

@[simp] theorem family_map (hq : 0 < q)
    (hsmall : ∀ e b, Fintype.card {l : L (G.left e) // G.projection e l = b} ≤ 2) (e : E) :
    (family G legalL legalR data compatible hq hsmall).map e =
      LocalCompletionFamily.table (LocalCompletionFamily.lookup hq (data e)) := rfl

end
end PerfectCompleteness.FlexibleLocalCompletion


namespace PerfectCompleteness.LocalCompletionGame

open scoped Classical
open UniqueGamesTheorem.Foundations.Games
open CompletionSoundness CompletionSoundness.LegalProjectionGame

noncomputable section

variable {E Q₁ Q₂ : Type*} [Fintype E]
  {L : Q₁ → Type*} {R : Q₂ → Type*} [∀ x, Fintype (L x)]
  {q : Nat}
  (G : LegalProjectionGame E Q₁ Q₂ L R)
  (legalL : ∀ x, L x ↪ Fin (2 * q)) (legalR : ∀ y, R y ↪ Fin q)
  (defaultL : ∀ x, L x)

def input (e : E) : LocalCompletionFamily.Input q :=
  (fun a => decide (a ∈ Set.range (legalL (G.left e))),
    fun a => legalR (G.right e)
      (G.projection e (roundLabel (legalL (G.left e)) (defaultL (G.left e)) a)))

theorem input_mask_true (e : E) (a : Fin (2 * q)) :
    (input G legalL legalR defaultL e).1 a = true ↔
      a ∈ Set.range (legalL (G.left e)) := by
  simp only [input, decide_eq_true_iff]

theorem input_image_legal (e : E) (l : L (G.left e)) :
    (input G legalL legalR defaultL e).2 (legalL (G.left e) l) =
      legalR (G.right e) (G.projection e l) := by
  simp only [input, roundLabel_legal]

def localLegalEquiv (e : E) :
    L (G.left e) ≃ LocalCompletionFamily.Legal (input G legalL legalR defaultL e) where
  toFun l := ⟨legalL (G.left e) l,
    (input_mask_true G legalL legalR defaultL e _).2 ⟨l, rfl⟩⟩
  invFun a := roundLabel (legalL (G.left e)) (defaultL (G.left e)) a.val
  left_inv l := roundLabel_legal (legalL (G.left e)) (defaultL (G.left e)) l
  right_inv a := by
    apply Subtype.ext
    obtain ⟨l, hl⟩ := (input_mask_true G legalL legalR defaultL e a.val).1 a.property
    change legalL (G.left e)
      (roundLabel (legalL (G.left e)) (defaultL (G.left e)) a.val) = a.val
    rw [← hl, roundLabel_legal]

@[simp] theorem localLegalEquiv_apply_val (e : E) (l : L (G.left e)) :
    (localLegalEquiv G legalL legalR defaultL e l).val = legalL (G.left e) l := rfl

theorem card_legal (e : E) :
    Fintype.card (LocalCompletionFamily.Legal (input G legalL legalR defaultL e)) =
      Fintype.card (L (G.left e)) :=
  (Fintype.card_congr (localLegalEquiv G legalL legalR defaultL e)).symm

theorem input_admissible
    (hsmall : ∀ e b, Fintype.card {l : L (G.left e) // G.projection e l = b} ≤ 2)
    (e : E) : LocalCompletionFamily.Admissible (input G legalL legalR defaultL e) := by
  intro b
  have hmatch (l : L (G.left e)) :
      (input G legalL legalR defaultL e).2
        (localLegalEquiv G legalL legalR defaultL e l).val =
        legalR (G.right e) (G.projection e l) := by
    rw [localLegalEquiv_apply_val]
    exact input_image_legal G legalL legalR defaultL e l
  let fibers : {l : L (G.left e) // legalR (G.right e) (G.projection e l) = b} ≃
      {a : LocalCompletionFamily.Legal (input G legalL legalR defaultL e) //
        (input G legalL legalR defaultL e).2 a.val = b} :=
    (localLegalEquiv G legalL legalR defaultL e).subtypeEquiv
      (fun l => by rw [hmatch l])
  have hcard := Fintype.card_congr fibers
  have hbound := embedded_fiber_le_two (legalR (G.right e)) (G.projection e) (hsmall e) b
  simp only [← Nat.card_eq_fintype_card] at hcard hbound ⊢
  exact hcard.symm.le.trans hbound

def result (hq : 0 < q) (e : E) : LocalCompletionFamily.Result q :=
  LocalCompletionFamily.lookup hq (input G legalL legalR defaultL e)

theorem result_correct (hq : 0 < q)
    (hsmall : ∀ e b, Fintype.card {l : L (G.left e) // G.projection e l = b} ≤ 2)
    (e : E) : LocalCompletionFamily.Correct (input G legalL legalR defaultL e)
      (result G legalL legalR defaultL hq e) :=
  LocalCompletionFamily.lookup_correct hq _
    (input_admissible G legalL legalR defaultL hsmall e)

def family (hq : 0 < q)
    (hsmall : ∀ e b, Fintype.card {l : L (G.left e) // G.projection e l = b} ≤ 2) :
    G.CompletionFamily legalL legalR where
  size e := LocalCompletionFamily.activeCount (result G legalL legalR defaultL hq e)
  positive e := LocalCompletionFamily.activeCount_positive _
  map e := LocalCompletionFamily.table (result G legalL legalR defaultL hq e)
  agrees e seed l :=
    ((result_correct G legalL legalR defaultL hq hsmall e).agrees seed
      (legalL (G.left e) l)
      ((input_mask_true G legalL legalR defaultL e _).2 ⟨l, rfl⟩)).trans
      (input_image_legal G legalL legalR defaultL e l)
  exact_two e seed b := by
    simpa only [← Nat.card_eq_fintype_card] using
      (result_correct G legalL legalR defaultL hq hsmall e).exact_two seed b
  illegal_probability e a b := by
    have hmask : (input G legalL legalR defaultL e).1 a.val ≠ true := by
      intro h
      exact a.property ((input_mask_true G legalL legalR defaultL e a.val).1 h)
    have h := (result_correct G legalL legalR defaultL hq hsmall e).illegal_probability
      a.val hmask b
    simpa only [Fintype.card_fin, card_legal] using h

@[simp] theorem family_size (hq : 0 < q)
    (hsmall : ∀ e b, Fintype.card {l : L (G.left e) // G.projection e l = b} ≤ 2) (e : E) :
    (family G legalL legalR defaultL hq hsmall).size e =
      LocalCompletionFamily.activeCount
        (LocalCompletionFamily.lookup hq (input G legalL legalR defaultL e)) := rfl

@[simp] theorem family_map (hq : 0 < q)
    (hsmall : ∀ e b, Fintype.card {l : L (G.left e) // G.projection e l = b} ≤ 2) (e : E) :
    (family G legalL legalR defaultL hq hsmall).map e =
      LocalCompletionFamily.table
        (LocalCompletionFamily.lookup hq (input G legalL legalR defaultL e)) := rfl

end
end PerfectCompleteness.LocalCompletionGame

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanConditioning
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype
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


variable {E T R : Type*} [Fintype E] [Fintype T] [Fintype R]

def kernelJoint (μ : FiniteDistribution E) (kernel : E → FiniteDistribution T) :
    FiniteDistribution (E × T) where
  weight x := μ.weight x.1 * (kernel x.1).weight x.2
  nonnegative x := mul_nonneg (μ.nonnegative _) ((kernel x.1).nonnegative _)
  normalized := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, FiniteDistribution.normalized, mul_one]
    exact μ.normalized


end
end PerfectCompleteness.CleanConditioning

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OccurrenceStochasticLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.SourceGame.questionGame_success _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.OccurrenceVertexEmbedding

open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {E Q₁ Q₂ N₁ N₂ A₁ A₂ : Type*}
  [Fintype E] [Fintype Q₁] [Fintype Q₂] [Fintype N₁] [Fintype N₂]
  [Fintype A₁] [Fintype A₂]

def rename (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) (left : Q₁ ↪ N₁) (right : Q₂ ↪ N₂) :
    OccurrenceGame E N₁ N₂ A₁ A₂ where
  occurrences := G.occurrences
  left e := left (G.left e)
  right e := right (G.right e)
  accepts := G.accepts

def restrict (left : Q₁ ↪ N₁) (right : Q₂ ↪ N₂) (strategy : Strategy N₁ N₂ A₁ A₂) :
    Strategy Q₁ Q₂ A₁ A₂ :=
  (fun x => strategy.1 (left x), fun y => strategy.2 (right y))

@[simp] theorem wins_restrict (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (left : Q₁ ↪ N₁) (right : Q₂ ↪ N₂) (strategy : Strategy N₁ N₂ A₁ A₂) (e : E) :
    (rename G left right).wins strategy e = G.wins (restrict left right strategy) e := rfl

@[simp] theorem success_restrict (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (left : Q₁ ↪ N₁) (right : Q₂ ↪ N₂) (strategy : Strategy N₁ N₂ A₁ A₂) :
    (rename G left right).success strategy = G.success (restrict left right strategy) := rfl

def extend (left : Q₁ ↪ N₁) (right : Q₂ ↪ N₂) (defaultLeft : A₁) (defaultRight : A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) : Strategy N₁ N₂ A₁ A₂ :=
  (Function.extend left strategy.1 (fun _ => defaultLeft),
    Function.extend right strategy.2 (fun _ => defaultRight))

omit [Fintype Q₁] [Fintype Q₂] [Fintype N₁] [Fintype N₂] [Fintype A₁] [Fintype A₂] in
@[simp] theorem restrict_extend (left : Q₁ ↪ N₁) (right : Q₂ ↪ N₂)
    (defaultLeft : A₁) (defaultRight : A₂) (strategy : Strategy Q₁ Q₂ A₁ A₂) :
    restrict left right (extend left right defaultLeft defaultRight strategy) = strategy := by
  apply Prod.ext
  · funext x
    exact left.injective.extend_apply strategy.1 (fun _ => defaultLeft) x
  · funext y
    exact right.injective.extend_apply strategy.2 (fun _ => defaultRight) y

theorem success_extend (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (left : Q₁ ↪ N₁) (right : Q₂ ↪ N₂) (defaultLeft : A₁) (defaultRight : A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) :
    (rename G left right).success (extend left right defaultLeft defaultRight strategy) =
      G.success strategy := by
  rw [success_restrict, restrict_extend]

theorem value_eq [Nonempty A₁] [Nonempty A₂]
    (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) (left : Q₁ ↪ N₁) (right : Q₂ ↪ N₂) :
    (rename G left right).value = G.value := by
  apply le_antisymm
  · apply ((rename G left right).value_le_iff _).2
    intro strategy
    rw [success_restrict]
    exact G.success_le_value _
  · apply (G.value_le_iff _).2
    intro strategy
    let s := extend left right (Classical.choice inferInstance) (Classical.choice inferInstance)
      strategy
    have h := (rename G left right).success_le_value s
    simpa only [s, success_extend] using h

end
end PerfectCompleteness.OccurrenceVertexEmbedding

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_FiniteListSampling
attribute [-simp] _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
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

def uniformList (L : Finset A) (nonempty : L.Nonempty) : FiniteDistribution A where
  weight a := if a ∈ L then 1 / (L.card : ℝ) else 0
  nonnegative a := by
    split
    · exact one_div_nonneg.mpr (Nat.cast_nonneg _)
    · exact le_rfl
  normalized := by
    have hcard : (L.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt nonempty.card_pos)
    simp only [Finset.sum_ite_mem_eq, Finset.sum_const, nsmul_eq_mul, mul_one_div]
    exact div_self hcard

@[simp] theorem uniformList_weight_mem (L : Finset A) (hne : L.Nonempty)
    (a : A) (ha : a ∈ L) : (uniformList L hne).weight a = 1 / (L.card : ℝ) := by
  simp [uniformList, ha]

end
end PerfectCompleteness.FiniteListSampling

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_BoundedListSamplingLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.BoundedListSampling

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {Index A : Type*} [Fintype A]

def listLaw (L : Finset A) (default : A) : FiniteDistribution A :=
  if h : L.Nonempty then FiniteListSampling.uniformList L h
  else FiniteListSampling.uniformList {default} (Finset.singleton_nonempty default)

@[simp] theorem listLaw_empty_weight (default a : A) :
    (listLaw ∅ default).weight a = if a = default then 1 else 0 := by
  simp [listLaw, FiniteListSampling.uniformList]

variable [Fintype Index] [Nonempty Index]

def jointLaw (L : Index → Finset A) (default : A) : FiniteDistribution (Index × A) :=
  CleanConditioning.kernelJoint (FiniteDistribution.uniform Index) (fun σ => listLaw (L σ) default)

@[simp] theorem jointLaw_weight (L : Index → Finset A) (default : A) (σ : Index) (a : A) :
    (jointLaw L default).weight (σ, a) =
      (1 / (Fintype.card Index : ℝ)) * (listLaw (L σ) default).weight a := rfl

def outputLaw {B : Type*} [Fintype B] (L : Index → Finset A) (default : A)
    (decode : Index → A → B) : FiniteDistribution B :=
  (jointLaw L default).pushforward (fun p => decode p.1 p.2)

end
end PerfectCompleteness.BoundedListSampling



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_FiniteBlockMachineLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CanonicalKeyEncoding

open ClauseSupport CanonicalKeys
open UniqueGamesTheorem.Foundations.Complexity
open scoped Classical

noncomputable section

def bits {n : Nat} (key : Key n) : List Bool := encodeWords (words key)

theorem bits_length_le {n : Nat} (key : Key n) (bound : Nat)
    (hIDs : ∀ entry ∈ key.retained, KeyMetadataEncoding.entryID entry.2 ≤ bound) :
    (bits key).length ≤
      (1 + partitionWidth n + 6 * key.retained.length) * (max n (max bound 2) + 1) := by
  have htwo : 2 ≤ max n (max bound 2) := (le_max_right bound 2).trans (le_max_right n _)
  have hbound : ∀ word ∈ words key, word ≤ max n (max bound 2) := by
    intro word hword
    rcases List.mem_cons.mp hword with hside | htail
    · have hs : sideWord key.side ≤ 1 := by cases key.side <;> decide
      omega
    · rcases List.mem_append.mp htail with hpart | hmeta
      · obtain ⟨i, hi⟩ := List.mem_ofFn.mp hpart
        have hb := boolWord_le_one (partitionMask key.partition i)
        omega
      · exact KeyMetadataEncoding.metadataWords_le key.retained bound hIDs word hmeta
  simpa only [bits, words_length] using encodeWords_length_le (words key) _ hbound

theorem bits_injective (n : Nat) : Function.Injective (bits (n := n)) := by
  intro a b h
  exact words_injective n (encodeWords_injective h)

end
end PerfectCompleteness.CanonicalKeyEncoding

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_CanonicalLabelEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CanonicalLabelEncoding

open CanonicalKeys CanonicalKeyEncoding
open scoped Classical

noncomputable section

theorem paddedMask_eq_true_iff {n q : Nat} (key : Key n)
    (large : partitionWidth n ≤ q) (a : Fin q) :
    paddedMask key a = true ↔ a ∈ Set.range (labelEmbedding key large) := by
  by_cases h : a.val < partitionWidth n
  · rw [paddedMask, dite_eq_left h]
    change decide ((partEnum n).symm ⟨a.val, h⟩ ∈ key.partition) = true ↔ _
    rw [decide_eq_true_iff]
    constructor
    · intro hpart
      refine ⟨⟨(partEnum n).symm ⟨a.val, h⟩, hpart⟩, ?_⟩
      apply Fin.ext
      simp only [labelEmbedding_val, Equiv.apply_symm_apply]
    · rintro ⟨label, heq⟩
      have hi : partEnum n label.val = (⟨a.val, h⟩ : Fin (partitionWidth n)) := by
        apply Fin.ext
        exact congrArg (fun x : Fin q => x.val) heq
      simpa only [← hi, Equiv.symm_apply_apply] using label.property
  · rw [paddedMask, dite_eq_right h]
    constructor
    · simp
    · rintro ⟨label, heq⟩
      have hval : (partEnum n label.val).val = a.val := congrArg (fun x : Fin q => x.val) heq
      exact (h (hval ▸ (partEnum n label.val).isLt)).elim

end
end PerfectCompleteness.CanonicalLabelEncoding

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_CanonicalLocalCompletion
attribute [-simp] _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CanonicalLocalCompletion

open scoped Classical
open Turing UniqueGamesTheorem.Foundations.Complexity UniqueGamesTheorem.Foundations.Games
open SourceClause CanonicalKeys CanonicalGame CanonicalKeyEncoding CanonicalLabelEncoding
open CompletionSoundness CompletionSoundness.LegalProjectionGame

noncomputable section

variable {v m n : Nat} {E I B : Type*} {V : I → Type*}
  [DecidableEq I] [∀ i, AddCommGroup (V i)]
  [∀ i, Module DirectionQuotient.F2 (V i)]
  [Finite I] [∀ i, Finite (V i)] [Finite B]
  {clauses : Fin m → NormalizedClause v}
  (F : BlockFamily clauses n E I V B)

local instance rightAlphabet_nonempty_rc6598c_1 (n : Nat) (δ : ℚ) : Nonempty (Fin (alphabet n δ)) :=
  ⟨⟨0, alphabet_positive n δ⟩⟩
local instance leftAlphabet_nonempty_rc6598c_1 (n : Nat) (δ : ℚ) : Nonempty (Fin (2 * alphabet n δ)) :=
  ⟨⟨0, Nat.mul_pos (by decide) (alphabet_positive n δ)⟩⟩
def legalL (δ : ℚ) (x : LeftVertex F) : LeftLabel F x ↪ Fin (2 * alphabet n δ) :=
  labelEmbedding x.val (partitionWidth_le_leftAlphabet n δ)

def legalR (δ : ℚ) (y : RightVertex F) : RightLabel F y ↪ Fin (alphabet n δ) :=
  labelEmbedding y.val (partitionWidth_le_alphabet n δ)

omit [DecidableEq I] [Finite I] [∀ index, Finite (V index)] [Finite B] in
@[simp] theorem legalL_val (δ : ℚ) (x : LeftVertex F) (label : LeftLabel F x) :
    (legalL F δ x label).val = (partEnum n label.val).val := rfl

omit [Finite I] [∀ index, Finite (V index)] [Finite B] in
@[simp] theorem legalR_val (δ : ℚ) (y : RightVertex F) (label : RightLabel F y) :
    (legalR F δ y label).val = (partEnum n label.val).val := rfl

def defaultL (x : LeftVertex F) : LeftLabel F x := Classical.choice inferInstance

variable [Fintype E] [Fintype (LeftVertex F)] [Fintype (RightVertex F)]
  [∀ x, Fintype (LeftLabel F x)] [∀ y, Fintype (RightLabel F y)]

omit [DecidableEq I] [Finite I] [∀ index, Finite (V index)] [Finite B] [Fintype E]
  [Fintype (LeftVertex F)] [Fintype (RightVertex F)]
  [∀ vertex, Fintype (RightLabel F vertex)] in
theorem leftLabel_card_le (δ : ℚ) (x : LeftVertex F) :
    Fintype.card (LeftLabel F x) ≤ alphabet n δ := by
  let : Fintype (KeyLabel x.val) := inferInstanceAs (Fintype (LeftLabel F x))
  exact (label_card_le x.val).trans (partitionWidth_le_alphabet n δ)

omit [Fintype (LeftVertex F)] [Fintype (RightVertex F)]
  [∀ vertex, Fintype (RightLabel F vertex)] in
theorem small (μ : FiniteDistribution E) :
    ∀ e b, Fintype.card
      {a : LeftLabel F ((game F μ).left e) // (game F μ).projection e a = b} ≤ 2 := by
  intro e b
  rw [Fintype.card_eq_nat_card]
  change Nat.card {a : LeftLabel F (leftAt F e) // edge F e a = b} ≤ 2
  exact edge_at_most_two F e b

def input (μ : FiniteDistribution E) (δ : ℚ) (e : E) :
    LocalCompletionFamily.Input (alphabet n δ) :=
  LocalCompletionGame.input (game F μ) (legalL F δ) (legalR F δ) (defaultL F) e

def result (μ : FiniteDistribution E) (δ : ℚ) (e : E) :
    LocalCompletionFamily.Result (alphabet n δ) :=
  LocalCompletionFamily.lookup (alphabet_positive n δ) (input F μ δ e)

def family (μ : FiniteDistribution E) (δ : ℚ) :
    (game F μ).CompletionFamily (legalL F δ) (legalR F δ) :=
  LocalCompletionGame.family (game F μ) (legalL F δ) (legalR F δ) (defaultL F)
    (alphabet_positive n δ) (by
      intro occurrence label
      rw [Fintype.card_eq_nat_card]
      have h := small F μ occurrence label
      rw [Fintype.card_eq_nat_card] at h
      exact h)

omit [Fintype (LeftVertex F)] [Fintype (RightVertex F)]
  [∀ vertex, Fintype (RightLabel F vertex)] in
@[simp] theorem family_size (μ : FiniteDistribution E) (δ : ℚ) (e : E) :
    (family F μ δ).size e = LocalCompletionFamily.activeCount (result F μ δ e) := rfl

omit [Fintype (LeftVertex F)] [Fintype (RightVertex F)]
  [∀ vertex, Fintype (RightLabel F vertex)] in
@[simp] theorem family_map (μ : FiniteDistribution E) (δ : ℚ) (e : E) :
    (family F μ δ).map e = LocalCompletionFamily.table (result F μ δ e) := rfl

end
end PerfectCompleteness.CanonicalLocalCompletion

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_UniformChildSum
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.RecursiveSampler.combine_zero _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.squareProduct_val _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.UniformChildSum

open scoped BigOperators
open PointwiseSpaces RecursiveSpaces
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {𝕜 X J : Type*} [Field 𝕜] [Fintype J]
  {D : J → Type*}

def childSum (r : ∀ i, X → D i) (H : ∀ i, Submodule 𝕜 (D i → 𝕜)) :
    (∀ i, squareSpace (H i)) →ₗ[𝕜] childSpace r H where
  toFun f := ⟨∑ i, pullback 𝕜 (r i) (f i),
    Submodule.sum_mem_iSup (fun i => Submodule.mem_map_of_mem (f i).property)⟩
  map_add' f g := by
    apply Subtype.ext
    simp only [Pi.add_apply, Submodule.coe_add, map_add, Finset.sum_add_distrib]
  map_smul' c f := by
    apply Subtype.ext
    simp only [Pi.smul_apply, Submodule.coe_smul, map_smul, Finset.smul_sum,
      RingHom.id_apply]

@[simp] theorem childSum_apply (r : ∀ i, X → D i)
    (H : ∀ i, Submodule 𝕜 (D i → 𝕜)) (f : ∀ i, squareSpace (H i)) :
    (childSum r H f).val = ∑ i, pullback 𝕜 (r i) (f i) := rfl


variable {branch : Nat → Nat} {n : Nat}

def recursiveSum (A : Slots branch (n + 1) → Type*) :
    (∀ i : Fin (branch n), squareSpace (space 𝕜 branch n (childFamily A i))) →ₗ[𝕜]
      space 𝕜 branch (n + 1) A :=
  childSum (childRestriction A) (fun i => space 𝕜 branch n (childFamily A i))

end
end PerfectCompleteness.UniformChildSum

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_CutChildGrouping
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.NodeEmbedding.embed_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.embeddedRows_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.equiv_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.matrix_evaluate _root_.OAI.PerfectCompleteness.NodeEmbedding.rowsEquiv_apply _root_.OAI.PerfectCompleteness.RecursiveSampler.combine_zero _root_.OAI.PerfectCompleteness.RecursiveSampler.evaluate_refl _root_.OAI.PerfectCompleteness.RecursiveSampler.evaluate_zeroTape _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.squareProduct_val
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

abbrev Child (i : Fin (branch n)) :=
  (C → squareSpace (H (childSlots slots i))) × Arrays (childSlots slots i) rows

abbrev Raw := (i : Fin (branch n)) → Child (C := C) slots rows i

abbrev Assembled :=
  (C → H slots) × ((i : Fin (branch n)) → Arrays (childSlots slots i) rows)

def assemble : Raw (C := C) slots rows →ₗ[F2] Assembled (C := C) slots rows where
  toFun x :=
    (fun q => UniformChildSum.recursiveSum (TreeSourceSpaces.LeafDomain slots)
      (fun i => (x i).1 q), fun i => (x i).2)
  map_add' x y := by
    apply Prod.ext
    · funext q
      exact map_add (UniformChildSum.recursiveSum (TreeSourceSpaces.LeafDomain slots))
        (fun i => (x i).1 q) (fun i => (y i).1 q)
    · rfl
  map_smul' c x := by
    apply Prod.ext
    · funext q
      exact map_smul (UniformChildSum.recursiveSum (TreeSourceSpaces.LeafDomain slots)) c
        (fun i => (x i).1 q)
    · rfl

omit [Fintype C] in
@[simp] theorem assemble_calls (x : Raw (C := C) slots rows) (q : C) :
    (assemble slots rows x).1 q =
      UniformChildSum.recursiveSum (TreeSourceSpaces.LeafDomain slots)
        (fun i => (x i).1 q) := rfl

omit [Fintype C] in
@[simp] theorem assemble_arrays (x : Raw (C := C) slots rows) (i : Fin (branch n)) :
    (assemble slots rows x).2 i = (x i).2 := rfl

end
end PerfectCompleteness.CutChildGrouping

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_RepetitionRateLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.RepetitionRate

open scoped BigOperators
open UniqueGamesTheorem.Foundations Games

noncomputable section

def bernoulli (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) : FiniteDistribution Bool where
  weight b := if b = true then p else 1 - p
  nonnegative b := by
    cases b
    · simpa using sub_nonneg.mpr hp'
    · simpa using hp
  normalized := by simp

end

end PerfectCompleteness.RepetitionRate



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_GeometricPathLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.drawIndexDecidableEq _root_.OAI.PerfectCompleteness.RecursiveSampler.drawIndexFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.RecursiveSampler.combine_zero _root_.OAI.PerfectCompleteness.RecursiveSampler.evaluate_refl _root_.OAI.PerfectCompleteness.RecursiveSampler.evaluate_zeroTape _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.GeometricPath

open RecursiveSpaces DescendantSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat}

def leafPath : {n : Nat} → Slots branch n → Path branch n 0
  | 0, _ => .refl 0
  | _ + 1, leaf => .step leaf.1 (leafPath leaf.2)

def nodeAtLevel : {n : Nat} → Slots branch n → Fin n → Nodes branch n
  | 0, _, level => Fin.elim0 level
  | _ + 1, leaf, level =>
      Fin.lastCases (.inl ()) (fun lower => .inr (leaf.1, nodeAtLevel leaf.2 lower)) level

@[simp] theorem nodeAtLevel_last {n : Nat} (leaf : Slots branch (n + 1)) :
    nodeAtLevel leaf (Fin.last n) = (.inl () : Nodes branch (n + 1)) := by
  exact Fin.lastCases_last (n := n) (motive := fun _ => Nodes branch (n + 1))
    (last := (.inl () : Nodes branch (n + 1)))
    (cast := fun lower : Fin n => (.inr (leaf.1, nodeAtLevel leaf.2 lower) : Nodes branch (n + 1)))

@[simp] theorem nodeAtLevel_castSucc {n : Nat} (leaf : Slots branch (n + 1))
    (lower : Fin n) :
    nodeAtLevel leaf lower.castSucc =
      (.inr (leaf.1, nodeAtLevel leaf.2 lower) : Nodes branch (n + 1)) := by
  exact Fin.lastCases_castSucc (n := n) (motive := fun _ => Nodes branch (n + 1))
    (last := (.inl () : Nodes branch (n + 1)))
    (cast := fun j : Fin n => (.inr (leaf.1, nodeAtLevel leaf.2 j) : Nodes branch (n + 1))) lower

theorem nodeAtLevel_height : ∀ {n : Nat} (leaf : Slots branch n) (level : Fin n),
    Nodes.height (nodeAtLevel leaf level) = level.val + 1 := by
  intro n
  induction n with
  | zero => intro leaf level; exact Fin.elim0 level
  | succ n ih =>
    intro leaf level
    refine Fin.lastCases ?_ (fun lower => ?_) level
    · simp only [nodeAtLevel_last, Nodes.height, Fin.val_last]
    · simpa only [nodeAtLevel_castSucc, Nodes.height, Fin.val_castSucc]
        using ih leaf.2 lower

theorem slots_nonempty : ∀ (n : Nat), (∀ k < n, 0 < branch k) → Nonempty (Slots branch n) := by
  intro n
  induction n with
  | zero => intro _; exact ⟨()⟩
  | succ n ih =>
    intro hbranch
    obtain ⟨leaf⟩ := ih (fun k hk => hbranch k (Nat.lt_trans hk (Nat.lt_succ_self n)))
    exact ⟨(⟨0, hbranch n (Nat.lt_succ_self n)⟩, leaf)⟩

noncomputable def law (n : Nat) (hbranch : ∀ k < n, 0 < branch k) :
    FiniteDistribution (Slots branch n) := by
  letI := slots_nonempty n hbranch
  exact FiniteDistribution.uniform (Slots branch n)

end PerfectCompleteness.GeometricPath



namespace PerfectCompleteness.HierarchicalKnownRows

noncomputable section

open TreeSourceSpaces HierarchicalArrays

variable {branch rows : Nat → Nat} {n t : Nat} {D : Type*}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n)
  (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)
  (descendant : D → {j : Nodes branch n // j ≠ upper})

def lower (x : NodeEmbedding.NumberedDomain slots) (d : D) :
    Fin (rows (Nodes.height (descendant d).val)) → F2 :=
  (HierarchicalMatrixTable.other slots upper background x).1 (descendant d)

@[simp] theorem lower_apply (x : NodeEmbedding.NumberedDomain slots)
    (d : D) (i : Fin (rows (Nodes.height (descendant d).val))) :
    lower slots upper background descendant x d i =
      (background (descendant d) i).val
        (NodeEmbedding.numberedRestriction slots (descendant d).val x) := rfl

end
end PerfectCompleteness.HierarchicalKnownRows

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_WholeArraySampler
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_castSucc _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_last _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.NodeEmbedding.embed_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.embeddedRows_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.equiv_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.matrix_evaluate _root_.OAI.PerfectCompleteness.NodeEmbedding.rowsEquiv_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val
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

abbrev StepIndex (i : Fin (branch n)) :=
  Unit ⊕ (Unit ⊕ RecursiveSampler.OffPath i)

def StepFactor {i : Fin (branch n)} (Root Selected : Type)
    (Ordinary : RecursiveSampler.OffPath i → Type) : StepIndex i → Type
  | .inl _ => Root
  | .inr (.inl _) => Selected
  | .inr (.inr j) => Ordinary j

instance stepFactorFintype {i : Fin (branch n)} (Root Selected : Type)
    (Ordinary : RecursiveSampler.OffPath i → Type)
    [Fintype Root] [Fintype Selected] [∀ j, Fintype (Ordinary j)]
    (k : StepIndex i) : Fintype (StepFactor Root Selected Ordinary k) := by
  rcases k with _ | (_ | j) <;> dsimp only [StepFactor] <;> infer_instance

abbrev StepTape {i : Fin (branch n)} (Root Selected : Type)
    (Ordinary : RecursiveSampler.OffPath i → Type) :=
  (k : StepIndex i) → StepFactor Root Selected Ordinary k

noncomputable instance spaceFintype
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (H slots) := Fintype.ofFinite _

abbrev RootTape (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :=
  BucketSampler.RecursiveTape (rows n) repeats p (LeafDomain slots)

def Tape (rows repeats : Nat → Nat) :
    {n m : Nat} → Path branch n m →
      (RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) → Type
  | _, _, .refl _, slots => Arrays slots rows
  | _, _, .step i p, slots =>
      StepTape (i := i) (RootTape rows repeats (.step i p) slots)
        (Tape rows repeats p (childSlots slots i))
        (fun j => Arrays (childSlots slots j.val) rows)

@[instance_reducible] def tapeFintypeAux (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) →
      (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) →
        Fintype (Tape rows repeats p slots)
  | _, _, .refl _, slots => inferInstanceAs (Fintype (Arrays slots rows))
  | _, _, .step i p, slots =>
      letI : Fintype (Tape rows repeats p (childSlots slots i)) :=
        tapeFintypeAux rows repeats p (childSlots slots i)
      letI : (k : StepIndex i) → Fintype
          (StepFactor (RootTape rows repeats (.step i p) slots)
            (Tape rows repeats p (childSlots slots i))
            (fun j => Arrays (childSlots slots j.val) rows) k) :=
        fun k => stepFactorFintype _ _ _ k
      inferInstanceAs (Fintype
        (StepTape (i := i) (RootTape rows repeats (.step i p) slots)
          (Tape rows repeats p (childSlots slots i))
          (fun j => Arrays (childSlots slots j.val) rows)))

instance tapeFintype (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (Tape rows repeats p slots) := tapeFintypeAux rows repeats p slots

def assemble (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (rows : Nat → Nat) (root : Fin (rows (n + 1)) → H slots)
    (children : ∀ j, Arrays (childSlots slots j) rows) : Arrays slots rows
  | .inl _ => root
  | .inr (j, node) => children j node

def childrenAt (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (rows : Nat → Nat) (i : Fin (branch n))
    (selected : Arrays (childSlots slots i) rows)
    (ordinary : ∀ j : RecursiveSampler.OffPath i, Arrays (childSlots slots j.val) rows)
    (j : Fin (branch n)) : Arrays (childSlots slots j) rows :=
  if h : j = i then h.symm ▸ selected else ordinary ⟨j, h⟩

@[simp] theorem childrenAt_selected
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (rows : Nat → Nat) (i : Fin (branch n))
    (selected : Arrays (childSlots slots i) rows)
    (ordinary : ∀ j : RecursiveSampler.OffPath i, Arrays (childSlots slots j.val) rows) :
    childrenAt slots rows i selected ordinary i = selected := by simp [childrenAt]

@[simp] theorem childrenAt_ordinary
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (rows : Nat → Nat) (i : Fin (branch n))
    (selected : Arrays (childSlots slots i) rows)
    (ordinary : ∀ j : RecursiveSampler.OffPath i, Arrays (childSlots slots j.val) rows)
    (j : RecursiveSampler.OffPath i) :
    childrenAt slots rows i selected ordinary j.val = ordinary j := by
  simp [childrenAt, j.property]

def evaluate (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) →
      (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) →
        Tape rows repeats p slots → Arrays slots rows
  | _, _, .refl _, _, ω => ω
  | n + 1, _, .step i p, slots, ω =>
      assemble slots rows
        (BucketSampler.recursiveEvaluate (rows (n + 1)) repeats (.step i p)
          (LeafDomain slots) (ω (.inl ())))
        (childrenAt slots rows i
          (evaluate rows repeats p (childSlots slots i) (ω (.inr (.inl ()))))
          (fun j => ω (.inr (.inr j))))

@[simp] theorem evaluate_refl (rows repeats : Nat → Nat)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (ω : Tape rows repeats (.refl n) slots) :
    evaluate rows repeats (.refl n) slots ω = ω := rfl

@[simp] theorem evaluate_root (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : Tape rows repeats (.step i p) slots) :
    evaluate rows repeats (.step i p) slots ω (.inl ()) =
      BucketSampler.recursiveEvaluate (rows (n + 1)) repeats (.step i p)
        (LeafDomain slots) (ω (.inl ())) := rfl

@[simp] theorem evaluate_selected (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : Tape rows repeats (.step i p) slots) (node : Nodes branch n) :
    evaluate rows repeats (.step i p) slots ω (.inr (i, node)) =
      evaluate rows repeats p (childSlots slots i) (ω (.inr (.inl ()))) node := by
  exact congrFun (childrenAt_selected slots rows i
    (evaluate rows repeats p (childSlots slots i) (ω (.inr (.inl ()))))
    (fun j => ω (.inr (.inr j)))) node

@[simp] theorem evaluate_ordinary (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : Tape rows repeats (.step i p) slots) (j : RecursiveSampler.OffPath i)
    (node : Nodes branch n) :
    evaluate rows repeats (.step i p) slots ω (.inr (j.val, node)) =
      ω (.inr (.inr j)) node := by
  exact congrFun (childrenAt_ordinary slots rows i
    (evaluate rows repeats p (childSlots slots i) (ω (.inr (.inl ()))))
    (fun j => ω (.inr (.inr j))) j) node

def tapeLaw (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) →
      (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) →
        FiniteDistribution (Tape rows repeats p slots)
  | _, _, .refl _, slots => FiniteDistribution.uniform (Arrays slots rows)
  | n + 1, _, .step i p, slots => by
      letI : (k : StepIndex i) → Fintype
          (StepFactor (RootTape rows repeats (.step i p) slots)
            (Tape rows repeats p (childSlots slots i))
            (fun j => Arrays (childSlots slots j.val) rows) k) :=
        fun k => stepFactorFintype _ _ _ k
      exact FiniteProduct.law
        (Ω := fun k : StepIndex i => StepFactor (RootTape rows repeats (.step i p) slots)
          (Tape rows repeats p (childSlots slots i))
          (fun j => Arrays (childSlots slots j.val) rows) k)
        (fun k : StepIndex i => match k with
          | .inl _ => BucketSampler.recursiveTapeLaw (rows (n + 1)) repeats (.step i p)
              (LeafDomain slots)
          | .inr (.inl _) => tapeLaw rows repeats p (childSlots slots i)
          | .inr (.inr j) => FiniteDistribution.uniform (Arrays (childSlots slots j.val) rows))

def law (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (Arrays slots rows) :=
  (tapeLaw rows repeats p slots).pushforward (evaluate rows repeats p slots)

end

end PerfectCompleteness.WholeArraySampler

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_PreliminarySampler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.PreliminarySampler

open RecursiveSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {v m n t : Nat} {branch rows repeats : Nat → Nat}

abbrev Questions (branch : Nat → Nat) (n t m : Nat) :=
  Slots branch n → Fin t → Fin m

def endpoints (E : Questions branch n t m) :
    Slots branch n → Fin t → SourceKeys.Endpoint v m :=
  fun leaf coordinate => .clause (E leaf coordinate)

abbrev Base (branch : Nat → Nat) (n t m : Nat) :=
  Questions branch n t m × Slots branch n

abbrev Choice (rows : Nat → Nat) (leaf : Slots branch n) :=
  (level : Fin n) × BucketSampler.Direction
    (rows (Nodes.height (GeometricPath.nodeAtLevel leaf level)))

theorem directionNonempty (width : Nat) (positive : 0 < width) :
    Nonempty (BucketSampler.Direction width) := by
  refine ⟨⟨fun _ => 1, ?_⟩⟩
  intro hz
  have h := congrFun hz ⟨0, positive⟩
  change (1 : BucketSampler.F2) = 0 at h
  exact one_ne_zero h

def questionsLaw [NeZero m] : FiniteDistribution (Questions branch n t m) :=
  FiniteDistribution.uniform _

def baseLaw [NeZero m] (hbranch : ∀ k < n, 0 < branch k) :
    FiniteDistribution (Base branch n t m) :=
  questionsLaw.product (GeometricPath.law n hbranch)

end
end PerfectCompleteness.PreliminarySampler

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceQuestionOrderLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceQuestionOrder

open Turing UniqueGamesTheorem.Foundations.Complexity
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t m : Nat}

def questionToTuple (question : PreliminarySampler.Questions branch n t m) :
    Fin (TreeCanonical.locationCount branch n t) → Fin m :=
  fun j => question ((TreeCanonical.numbering branch n t).symm j).1
    ((TreeCanonical.numbering branch n t).symm j).2

def tupleToQuestion (tuple : Fin (TreeCanonical.locationCount branch n t) → Fin m) :
    PreliminarySampler.Questions branch n t m :=
  fun leaf coordinate => tuple (TreeCanonical.numbering branch n t (leaf, coordinate))

@[simp] theorem tupleToQuestion_questionToTuple
    (question : PreliminarySampler.Questions branch n t m) :
    tupleToQuestion (questionToTuple question) = question := by
  funext leaf coordinate
  simp only [tupleToQuestion, questionToTuple, Equiv.symm_apply_apply]

@[simp] theorem questionToTuple_tupleToQuestion
    (tuple : Fin (TreeCanonical.locationCount branch n t) → Fin m) :
    questionToTuple (tupleToQuestion (branch := branch) (n := n) (t := t) tuple) = tuple := by
  funext j
  simp only [questionToTuple, tupleToQuestion, Prod.mk.eta, Equiv.apply_symm_apply]

def sourceOrder (branch : Nat → Nat) (n t m : Nat) :
    List (PreliminarySampler.Questions branch n t m) :=
  (MachineTupleOdometer.tupleOrder m (TreeCanonical.locationCount branch n t)).reverse.map
    tupleToQuestion

@[simp] theorem sourceOrder_length (branch : Nat → Nat) (n t m : Nat) :
    (sourceOrder branch n t m).length = m ^ TreeCanonical.locationCount branch n t := by
  simp only [sourceOrder, List.length_map, List.length_reverse,
    MachineTupleOdometer.tupleOrder_length]

theorem mem_sourceOrder (question : PreliminarySampler.Questions branch n t m) :
    question ∈ sourceOrder branch n t m := by
  apply List.mem_map.mpr
  refine ⟨questionToTuple question, ?_, tupleToQuestion_questionToTuple question⟩
  rw [List.mem_reverse]
  change questionToTuple question ∈ List.ofFn
    (finFunctionFinEquiv (m := m) (n := TreeCanonical.locationCount branch n t)).symm
  apply List.mem_ofFn.mpr
  exact ⟨finFunctionFinEquiv (questionToTuple question), Equiv.symm_apply_apply _ _⟩

@[simp] theorem sourceOrder_toFinset (branch : Nat → Nat) (n t m : Nat) :
    (sourceOrder branch n t m).toFinset = Finset.univ := by
  ext question
  simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
  exact mem_sourceOrder question

end

end PerfectCompleteness.SourceQuestionOrder


namespace PerfectCompleteness.ChildBlockCardinality

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

abbrev Raw (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  (Fin calls → squareSpace (H slots)) × Arrays slots rows

end
end PerfectCompleteness.ChildBlockCardinality


namespace PerfectCompleteness.ChildBlockMixture

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

noncomputable section

section General

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]

def component (Q : (i : I) → FiniteDistribution (Ω i)) (chosen i : I) :
    FiniteDistribution (Ω i) :=
  if h : chosen = i then h ▸ Q chosen else FiniteDistribution.uniform (Ω i)

end General

end
end PerfectCompleteness.ChildBlockMixture


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_OriginalChildScalars
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem
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

abbrev Square (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (child : Fin (branch n)) := squareSpace (H (childSlots slots child))

instance squareFintype (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (child : Fin (branch n)) : Fintype (Square slots child) := Fintype.ofFinite _

def squareSum (repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) (chosen : Fin (branch n))
    (values : RecursiveSampler.CallIndex repeats n → H (childSlots slots chosen)) :
    Square slots chosen :=
  ∑ pair : Fin (repeats (n + 1)),
    RecursiveSamplerBiasAlgebra.squareProduct F2 (H (childSlots slots chosen))
      (values (pair, false)) (values (pair, true))

def specialSquareLaw (repeats : Nat → Nat) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) (chosen : Fin (branch n)) :
    FiniteDistribution (Square slots chosen) :=
  (RecursiveSampler.callScalarLaw F2 repeats chosen q (LeafDomain slots)).pushforward
    (squareSum repeats slots chosen)

def squareComponent (repeats : Nat → Nat) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) (chosen : Fin (branch n)) :
    (child : Fin (branch n)) → FiniteDistribution (Square slots child) :=
  ChildBlockMixture.component (specialSquareLaw repeats q slots) chosen

@[simp] theorem squareComponent_self (repeats : Nat → Nat) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) (chosen : Fin (branch n)) :
    squareComponent repeats q slots chosen chosen = specialSquareLaw repeats q slots chosen :=
  dite_eq_left rfl

@[simp] theorem squareComponent_other (repeats : Nat → Nat) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (chosen : Fin (branch n)) (child : RecursiveSampler.OffPath chosen) :
    squareComponent repeats q slots chosen child.val = FiniteDistribution.uniform (Square slots child.val) :=
  dite_eq_right (Ne.symm child.property)

abbrev ScalarTape (repeats : Nat → Nat) (chosen : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :=
  RecursiveSampler.Tape F2 repeats (.step chosen q) (LeafDomain slots)

def selectedAndOthers (repeats : Nat → Nat) (chosen : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : ScalarTape repeats chosen q slots) :
    Square slots chosen × ((child : RecursiveSampler.OffPath chosen) → Square slots child.val) :=
  let split := RecursiveSampler.splitEvaluatedTape F2 repeats chosen q (LeafDomain slots) ω
  (squareSum repeats slots chosen split.2, split.1)

def stepSquareMap (repeats : Nat → Nat) (chosen : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : ScalarTape repeats chosen q slots) : (child : Fin (branch n)) → Square slots child :=
  (Equiv.piSplitAt chosen (fun child => ↥(Square slots child))).symm
    (selectedAndOthers repeats chosen q slots ω)

end
end PerfectCompleteness.OriginalChildScalars

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceOddListsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.TreeCanonical.assignmentEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceOddLists

open SourceClause OddLists
open UniqueGamesTheorem.Foundations.Games

noncomputable section

abbrev Occurrences (m t : Nat) := Fin t → Occurrence m

def left {m t : Nat} (e : Occurrences m t) : Fin t → Fin m :=
  fun i => (e i).1

def right {n m t : Nat} (clauses : Fin m → NormalizedClause n)
    (e : Occurrences m t) : Fin t → Fin n :=
  fun i => occurrenceVariable clauses (e i)

end
end PerfectCompleteness.SourceOddLists



namespace PerfectCompleteness.SourceAnswerEquiv

open SourceClause

variable {v m t : Nat}

def clauseAnswerEquiv (signs : Triple) : ClauseSupport.Answer signs ≃ Fin 7 where
  toFun a := SourceGame.encodeLabel signs a.val ((mem_satisfyingTriples signs a.val).mp a.property)
  invFun a := ⟨SourceGame.decodeLabel signs a, SourceGame.decodeLabel_mem signs a⟩
  left_inv a := by
    apply Subtype.ext
    exact SourceGame.decodeLabel_encodeLabel signs a.val
      ((mem_satisfyingTriples signs a.val).mp a.property)
  right_inv a := by
    apply SourceGame.decodeLabel_injective signs
    exact SourceGame.decodeLabel_encodeLabel signs (SourceGame.decodeLabel signs a)
      (SourceGame.decodeLabel_legal signs a)

@[simp] theorem clauseAnswerEquiv_symm_val (signs : Triple) (a : Fin 7) :
    ((clauseAnswerEquiv signs).symm a).val = SourceGame.decodeLabel signs a := rfl

@[simp] theorem clauseAnswerEquiv_decode (signs : Triple) (a : ClauseSupport.Answer signs) :
    SourceGame.decodeLabel signs (clauseAnswerEquiv signs a) = a.val :=
  SourceGame.decodeLabel_encodeLabel signs a.val
    ((mem_satisfyingTriples signs a.val).mp a.property)

def leftSlots (clauses : Fin m → NormalizedClause v) (question : Fin t → Fin m) :
    Fin t → MixedSupport.Slot :=
  fun i => SourceKeys.slot clauses (.clause (question i))

def rightSlots (clauses : Fin m → NormalizedClause v) (question : Fin t → Fin v) :
    Fin t → MixedSupport.Slot :=
  fun i => SourceKeys.slot clauses (.variable (question i))

abbrev LeftDomain (clauses : Fin m → NormalizedClause v) (question : Fin t → Fin m) :=
  MixedSupport.Assignment (leftSlots clauses question)

abbrev RightDomain (clauses : Fin m → NormalizedClause v) (question : Fin t → Fin v) :=
  MixedSupport.Assignment (rightSlots clauses question)

def leftEquiv (clauses : Fin m → NormalizedClause v) (question : Fin t → Fin m) :
    LeftDomain clauses question ≃ SourceOddLists.LeftLabels t where
  toFun a i := clauseAnswerEquiv (clauses (question i)).signs (a i)
  invFun a i := (clauseAnswerEquiv (clauses (question i)).signs).symm (a i)
  left_inv a := by
    funext i
    exact (clauseAnswerEquiv (clauses (question i)).signs).symm_apply_apply (a i)
  right_inv a := by
    funext i
    exact (clauseAnswerEquiv (clauses (question i)).signs).apply_symm_apply (a i)

def rightEquiv (clauses : Fin m → NormalizedClause v) (question : Fin t → Fin v) :
    RightDomain clauses question ≃ SourceOddLists.RightLabels t :=
  Equiv.refl _

@[simp] theorem leftEquiv_apply (clauses : Fin m → NormalizedClause v)
    (question : Fin t → Fin m) (a : LeftDomain clauses question) (i : Fin t) :
    leftEquiv clauses question a i = clauseAnswerEquiv (clauses (question i)).signs (a i) := rfl

@[simp] theorem leftEquiv_symm_apply (clauses : Fin m → NormalizedClause v)
    (question : Fin t → Fin m) (a : SourceOddLists.LeftLabels t) (i : Fin t) :
    (leftEquiv clauses question).symm a i =
      (clauseAnswerEquiv (clauses (question i)).signs).symm (a i) := rfl

@[simp] theorem rightEquiv_apply (clauses : Fin m → NormalizedClause v)
    (question : Fin t → Fin v) (a : RightDomain clauses question) :
    rightEquiv clauses question a = a := rfl

def slotProjection (clauses : Fin m → NormalizedClause v)
    (e : SourceOddLists.Occurrences m t) :
    ∀ i, MixedSupport.Projection (leftSlots clauses (SourceOddLists.left e) i)
      (rightSlots clauses (SourceOddLists.right clauses e) i) :=
  fun i => (SourceKeys.Step.select (clauses := clauses) (e i).1 (e i).2).projection

def actualProjection (clauses : Fin m → NormalizedClause v)
    (e : SourceOddLists.Occurrences m t) :
    LeftDomain clauses (SourceOddLists.left e) →
      RightDomain clauses (SourceOddLists.right clauses e) :=
  MixedSupport.projectionMap (slotProjection clauses e)

@[simp] theorem actualProjection_apply (clauses : Fin m → NormalizedClause v)
    (e : SourceOddLists.Occurrences m t)
    (a : LeftDomain clauses (SourceOddLists.left e)) (i : Fin t) :
    actualProjection clauses e a i = (a i).val.at (e i).2 := rfl


end PerfectCompleteness.SourceAnswerEquiv

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineFiniteAlphabet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finiteness of every alphabet of the actual machines used by the reduction.
`FinTM2` already bundles finitely many tapes, control labels and register states,
but its alphabet field only requires the input tape alphabet to be finite.
This additional property is preserved by the actual sequential and repetition
constructors; it does not replace or alter their execution certificates.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet

open Turing

/-! Every physical tape has a finite alphabet. Together with `M.kFin`, this
also makes the disjoint union of all physical tape alphabets finite. -/

/-- The first two tape groups retain their original alphabets. The sole new
bridge tape uses the second machine's already finite input alphabet. -/
theorem sequential_machine (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀)
    (hfirst : FiniteAlphabet first) (hsecond : FiniteAlphabet second) :
    FiniteAlphabet (MachineSequential.machine first second relabel fallback) := by
  intro tape
  rcases tape with tape | tape | tape
  · exact hfirst tape
  · exact hsecond tape
  · exact input_finite second

/-- Preservation for the machine actually stored in the polynomial-time
composition certificate, with its actual relabeling bridge. -/
theorem compose {α β γ αΓ βΓ γΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {ec : γ → List γΓ}
    {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime ea eb f)
    (second : TM2ComputableInPolyTime eb ec g) (fallback : βΓ)
    (hfirst : FiniteAlphabet first.tm) (hsecond : FiniteAlphabet second.tm) :
    FiniteAlphabet (MachineSequential.compose first second fallback).tm := by
  exact sequential_machine first.tm second.tm
    (fun symbol => second.inputAlphabet.symm (first.outputAlphabet symbol))
    (second.inputAlphabet.symm fallback) hfirst hsecond

theorem composeBits {α β γ : Type}
    {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
    {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime ea eb f)
    (second : TM2ComputableInPolyTime eb ec g)
    (hfirst : FiniteAlphabet first.tm) (hsecond : FiniteAlphabet second.tm) :
    FiniteAlphabet (MachineSequential.composeBits first second).tm :=
  compose first second false hfirst hsecond

end UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_BinaryOccurrenceRename
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryRenameWords.literals_cons _root_.OAI.PerfectCompleteness.BinaryRenameWords.literals_length _root_.OAI.PerfectCompleteness.BinaryRenameWords.literals_nil _root_.OAI.PerfectCompleteness.BinaryRenameWords.tokens_length _root_.OAI.PerfectCompleteness.BinaryTokenMachine.tokens_cons _root_.OAI.PerfectCompleteness.BinaryTokenMachine.tokens_length _root_.OAI.PerfectCompleteness.BinaryTokenMachine.tokens_nil _root_.OAI.PerfectCompleteness.SourceClause.localEval_restrict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.BinaryOccurrenceRename

open BinaryFormula UniqueGamesTheorem.Foundations

theorem renamed_satisfiable_iff (F : Formula) : (renamed F).Satisfiable ↔ F.Satisfiable := by
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨extendAssignment F A, ?_⟩
    intro c mem
    have hc : clause F c mem ∈ (renamed F).clauses :=
      List.mem_map.mpr ⟨⟨c, mem⟩, by simp, rfl⟩
    exact (clause_eval_extend F c mem A).symm.trans (hA _ hc)
  · rintro ⟨A, hA⟩
    refine ⟨restrictAssignment F A, ?_⟩
    intro c mem
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp mem
    exact (clause_eval_restrict F original.val original.property A).trans
      (hA original.val original.property)

end PerfectCompleteness.BinaryOccurrenceRename

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_BinaryParsingLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryRenameWords.literals_cons _root_.OAI.PerfectCompleteness.BinaryRenameWords.literals_length _root_.OAI.PerfectCompleteness.BinaryRenameWords.literals_nil _root_.OAI.PerfectCompleteness.BinaryRenameWords.tokens_length _root_.OAI.PerfectCompleteness.BinaryTokenMachine.tokens_cons _root_.OAI.PerfectCompleteness.BinaryTokenMachine.tokens_length _root_.OAI.PerfectCompleteness.BinaryTokenMachine.tokens_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.BinaryLanguage

open UniqueGamesTheorem.Foundations

theorem rejectBinary_unsatisfiable : ¬rejectBinary.Satisfiable := by
  rintro ⟨assignment, satisfied⟩
  have positive := satisfied #v[⟨0, true⟩, ⟨0, true⟩, ⟨0, true⟩]
    (by simp [rejectBinary])
  have negative := satisfied #v[⟨0, false⟩, ⟨0, false⟩, ⟨0, false⟩]
    (by simp [rejectBinary])
  cases h : assignment 0 <;>
    simp [BinaryFormula.Clause.eval, BinaryFormula.Literal.eval, h] at positive negative

theorem totalParsed_satisfiable_iff (input : List Bool) :
    (totalParsed input).Satisfiable ↔ language input := by
  cases parsed : BinaryEncoding.decodeFormula input with
  | none => simp [totalParsed, parsed, rejectBinary_unsatisfiable, language]
  | some formula => simp [totalParsed, parsed, language]

theorem totalRename_satisfiable_iff (input : List Bool) :
    (totalRename input).Satisfiable ↔ language input := by
  exact (BinaryOccurrenceRename.renamed_satisfiable_iff (totalParsed input)).trans
    (totalParsed_satisfiable_iff input)

end PerfectCompleteness.BinaryLanguage

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_BinaryRenameMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.BinaryRenameMachine


open Turing UniqueGamesTheorem.Foundations
open Complexity Complexity.MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

theorem computation_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computableInPolyTime.tm :=
  MachineFiniteAlphabet.composeBits preprocessing tokenComputation
    BinaryTokenMachine.machine_finiteAlphabet machine_finiteAlphabet

end PerfectCompleteness.BinaryRenameMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_BinaryValidatorMachine
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryRenameWords.literals_cons _root_.OAI.PerfectCompleteness.BinaryRenameWords.literals_length _root_.OAI.PerfectCompleteness.BinaryRenameWords.literals_nil _root_.OAI.PerfectCompleteness.BinaryRenameWords.tokens_length _root_.OAI.PerfectCompleteness.BinaryTokenMachine.tokens_cons _root_.OAI.PerfectCompleteness.BinaryTokenMachine.tokens_length _root_.OAI.PerfectCompleteness.BinaryTokenMachine.tokens_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.BinaryValidatorMachine


open BinaryEncoding BinaryFormula

theorem frame_inverse (slot : Fin 3) (last : Bool) (input : List Bool)
    (accepted : run (.name slot last) input = .done) :
    ∃ bits rest, input = frame bits ++ rest ∧
      BinaryNameMachine.finalDigit bits (some last) = some true ∧
      run (afterName slot) rest = .done := by
  induction input using List.twoStepInduction generalizing last with
  | nil => simp [run] at accepted
  | singleton flag =>
      cases flag with
      | false =>
          cases last with
          | false => simp [run, nextMode] at accepted
          | true =>
              exact ⟨[], [], rfl, rfl, by simpa [run, nextMode] using accepted⟩
      | true => simp [run, nextMode] at accepted
  | cons_cons flag bit input ih _ =>
      cases flag with
      | false =>
          cases last with
          | false => simp [run, nextMode] at accepted
          | true =>
              exact ⟨[], bit :: input, rfl, rfl,
                by simpa [run, nextMode] using accepted⟩
      | true =>
          have haccepted : run (.name slot bit) input = .done := by
            simpa only [run, nextMode] using accepted
          obtain ⟨bits, rest, hinput, hvalid, hrest⟩ := ih bit haccepted
          refine ⟨bit :: bits, rest, ?_, hvalid, hrest⟩
          simp [frame, hinput]

theorem name_inverse (slot : Fin 3) (input : List Bool)
    (accepted : run (.name slot true) input = .done) :
    ∃ name rest, input = nameBits name ++ rest ∧ run (afterName slot) rest = .done := by
  obtain ⟨bits, rest, hinput, hvalid, hrest⟩ := frame_inverse slot true input accepted
  have hcanonical := (finalDigit_true_iff bits).mp hvalid
  have hbits := (BinaryParsing.canonical_iff bits).mp hcanonical
  refine ⟨bitsValue bits, rest, ?_, hrest⟩
  simpa only [nameBits, hbits] using hinput

theorem literal_inverse (slot : Fin 3) (input : List Bool)
    (accepted : run (.sign slot) input = .done) :
    ∃ literal rest, input = literalBits literal ++ rest ∧ run (afterName slot) rest = .done := by
  cases input with
  | nil => simp [run] at accepted
  | cons sign input =>
      have haccepted : run (.name slot true) input = .done := accepted
      obtain ⟨name, rest, hinput, hrest⟩ := name_inverse slot input haccepted
      refine ⟨⟨name, sign⟩, rest, ?_, hrest⟩
      simp [literalBits, hinput]

theorem clause_inverse (input : List Bool) (accepted : run (.sign 0) input = .done) :
    ∃ clause rest, input = clauseBits clause ++ rest ∧ run .clause rest = .done := by
  obtain ⟨a, afterA, hA, acceptedA⟩ := literal_inverse 0 input accepted
  have hacceptedA : run (.sign 1) afterA = .done := by
    simpa [afterName] using acceptedA
  obtain ⟨b, afterB, hB, acceptedB⟩ := literal_inverse 1 afterA hacceptedA
  have hacceptedB : run (.sign 2) afterB = .done := by
    simpa [afterName] using acceptedB
  obtain ⟨c, rest, hC, acceptedC⟩ := literal_inverse 2 afterB hacceptedB
  have hrest : run .clause rest = .done := by simpa [afterName] using acceptedC
  refine ⟨#v[a, b, c], rest, ?_, hrest⟩
  simp [clauseBits, hA, hB, hC, List.append_assoc]

theorem clauses_inverse_aux (fuel : Nat) (input : List Bool)
    (enough : input.length < fuel) (accepted : run .clause input = .done) :
    ∃ clauses, input = clausesBits clauses := by
  induction fuel generalizing input with
  | zero => omega
  | succ fuel ih =>
      cases input with
      | nil => simp [run] at accepted
      | cons flag input =>
          cases flag with
          | false =>
              have hdone : run .done input = .done := accepted
              have hempty := (run_done_iff input).mp hdone
              subst input
              exact ⟨[], rfl⟩
          | true =>
              have haccepted : run (.sign 0) input = .done := accepted
              obtain ⟨clause, rest, hinput, hrest⟩ := clause_inverse input haccepted
              have hlength := congrArg List.length hinput
              simp only [List.length_append] at hlength
              have henough : rest.length < fuel := by
                simp only [List.length_cons] at enough
                omega
              obtain ⟨clauses, hclauses⟩ := ih rest henough hrest
              refine ⟨clause :: clauses, ?_⟩
              simp [clausesBits, hinput, hclauses]

theorem run_clause_iff (input : List Bool) :
    run .clause input = .done ↔ ∃ formula, input = formulaBits formula := by
  constructor
  · intro accepted
    obtain ⟨clauses, hclauses⟩ :=
      clauses_inverse_aux (input.length + 1) input (by omega) accepted
    exact ⟨⟨clauses⟩, hclauses⟩
  · rintro ⟨formula, rfl⟩
    exact run_formula formula

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition

end PerfectCompleteness.BinaryValidatorMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_BinaryTotalInputMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.BinaryTotalInputMachine


open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer
open UniqueGamesTheorem.Reduction.MachineSubstitution
open BinaryValidatorMachine (Mode nextMode run)

theorem totalTrace (input : List Bool) :
    (advance machine.step)^[steps input] (some (initList machine input)) =
      some (haltList machine (BinaryEncoding.formulaBits (BinaryLanguage.totalParsed input))) := by
  rw [initList_eq, haltList_eq]
  cases parsed : BinaryEncoding.decodeFormula input with
  | none =>
      have rejected : run .clause input ≠ .done := by
        intro accepted
        obtain ⟨formula, encoded⟩ := (BinaryValidatorMachine.run_clause_iff input).mp accepted
        have roundtrip := BinaryEncoding.decodeFormula_encoded formula
        rw [← encoded, parsed] at roundtrip
        cases roundtrip
      simpa only [steps, rejected, ↓reduceIte, BinaryLanguage.totalParsed, parsed,
        Option.getD_none, rejectedWord] using rejectedTrace input rejected
  | some formula =>
      have encoded := BinaryParsing.decodeFormula_sound input formula parsed
      have accepted := (BinaryValidatorMachine.run_clause_iff input).mpr ⟨formula, encoded⟩
      simp only [steps, accepted, ↓reduceIte, BinaryLanguage.totalParsed, parsed,
        Option.getD_some]
      rw [← encoded]
      exact acceptedTrace input accepted

def outputsInTime (input : List Bool) :
    TM2OutputsInTime machine input
      (some (BinaryEncoding.formulaBits (BinaryLanguage.totalParsed input)))
      (2 * input.length + 3) where
  steps := steps input
  evals_in_steps := totalTrace input
  steps_le_m := steps_le input

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime (id : List Bool → List Bool) BinaryEncoding.formulaBits
      BinaryLanguage.totalParsed where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 3
  outputsFun input := by
    change TM2OutputsInTime machine (input.map id)
      (some ((BinaryEncoding.formulaBits (BinaryLanguage.totalParsed input)).map id))
      ((2 * Polynomial.X + 3 : Polynomial Nat).eval input.length)
    simpa only [List.map_id_fun, id_eq, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_ofNat] using outputsInTime input

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

theorem computation_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computableInPolyTime.tm :=
  machine_finiteAlphabet

end PerfectCompleteness.BinaryTotalInputMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_BinaryInputReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.BinaryInputReduction

open Turing UniqueGamesTheorem.Foundations.Complexity

noncomputable def computation :
    TM2ComputableInPolyTime (id : List Bool → List Bool) formulaBits BinaryLanguage.totalRename := by
  change TM2ComputableInPolyTime (id : List Bool → List Bool) formulaBits
    (fun input => BinaryOccurrenceRename.renamed (BinaryLanguage.totalParsed input))
  exact MachineSequential.composeBits BinaryTotalInputMachine.computableInPolyTime
    BinaryRenameMachine.computableInPolyTime

theorem computation_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm :=
  MachineFiniteAlphabet.composeBits BinaryTotalInputMachine.computableInPolyTime
    BinaryRenameMachine.computableInPolyTime
    BinaryTotalInputMachine.computation_finiteAlphabet
    BinaryRenameMachine.computation_finiteAlphabet

end PerfectCompleteness.BinaryInputReduction

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_OriginalChildScalarAssemblyLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.OriginalChildScalarAssembly

open PointwiseSpaces RecursiveSpaces DescendantSpaces TreeSourceSpaces
open OriginalChildScalars RecursiveSamplerBiasAlgebra
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

@[simp] theorem stepSquareMap_self (repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : ScalarTape repeats chosen q slots) :
    stepSquareMap repeats chosen q slots ω chosen =
      squareSum repeats slots chosen
        (RecursiveSampler.splitEvaluatedTape F2 repeats chosen q (LeafDomain slots) ω).2 := by
  exact congrArg Prod.fst
    ((Equiv.piSplitAt chosen (fun child => ↥(Square slots child))).apply_symm_apply
      (selectedAndOthers repeats chosen q slots ω))

@[simp] theorem stepSquareMap_other (repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : ScalarTape repeats chosen q slots) (child : RecursiveSampler.OffPath chosen) :
    stepSquareMap repeats chosen q slots ω child.val = ω (.inl child) := by
  exact congrArg
    (fun z : Square slots chosen ×
      ((j : RecursiveSampler.OffPath chosen) → Square slots j.val) => z.2 child)
    ((Equiv.piSplitAt chosen (fun child => ↥(Square slots child))).apply_symm_apply
      (selectedAndOthers repeats chosen q slots ω))

end
end PerfectCompleteness.OriginalChildScalarAssembly


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OddListExtraction
attribute [-simp] _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.RecursiveSampler.combine_zero _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.squareProduct_val _root_.OAI.PerfectCompleteness.RecursiveSpaceEquiv.squareEquiv_apply _root_.OAI.PerfectCompleteness.UniformChildSum.childSum_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
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

def productElement (f g : H) : squareSpace H :=
  ⟨f.val * g.val, mul_mem_squareSpace H f.property g.property⟩

def multiplicationForm (z : Module.Dual F2 (squareSpace H)) : H →ₗ[F2] H →ₗ[F2] F2 :=
  LinearMap.mk₂ F2 (fun f g => z (productElement H f g))
    (by
      intro f g h
      rw [← map_add]
      congr 1
      apply Subtype.ext
      exact add_mul _ _ _)
    (by
      intro c f g
      rw [← map_smul]
      congr 1
      apply Subtype.ext
      exact smul_mul_assoc _ _ _)
    (by
      intro f g h
      rw [← map_add]
      congr 1
      apply Subtype.ext
      exact mul_add _ _ _)
    (by
      intro c f g
      rw [← map_smul]
      congr 1
      apply Subtype.ext
      exact mul_smul_comm _ _ _)

@[simp] theorem multiplicationForm_apply (z : Module.Dual F2 (squareSpace H))
    (f g : H) : multiplicationForm H z f g = z (productElement H f g) := rfl

variable (q : X → A) (hmem : ∀ a, indicator q a ∈ H)

noncomputable def atom (a : A) : H := ⟨indicator q a, hmem a⟩

noncomputable def diagonal (z : Module.Dual F2 (squareSpace H)) (a : A) : F2 :=
  multiplicationForm H z (atom H q hmem a) (atom H q hmem a)

@[simp] theorem form_atom_self (z : Module.Dual F2 (squareSpace H)) (a : A) :
    multiplicationForm H z (atom H q hmem a) (atom H q hmem a) =
      diagonal H q hmem z a := rfl

end Form

end PerfectCompleteness.OddListExtraction

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_ChildBlockProjection
attribute [-instance] _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.squareProduct_val _root_.OAI.PerfectCompleteness.UniformChildSum.childSum_apply
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

def nodeProjection
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (node : Nodes branch n) :
    ∀ s k, MixedSupport.Projection (nodeSlots slots node s k) (nodeSlots projected node s k) :=
  fun s k => p ((Nodes.path node).slotEmbedding s) k

def squarePullback
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) :
    squareSpace (H projected) →ₗ[F2] squareSpace (H slots) where
  toFun f := ⟨PointwiseSpaces.pullback F2 (sourceProjection p) f.val,
    TreeSourceSpaces.squareSpace_pullback_le p (Submodule.mem_map_of_mem f.property)⟩
  map_add' f g := by apply Subtype.ext; rfl
  map_smul' c f := by apply Subtype.ext; rfl

@[simp] theorem squarePullback_apply
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (f : squareSpace (H projected)) (x : Domain slots) :
    (squarePullback p f).val x = f.val (sourceProjection p x) := rfl

def arraysPullback (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) :
    Arrays projected rows →ₗ[F2] Arrays slots rows where
  toFun arrays node row := HPullback (nodeProjection p node) (arrays node row)
  map_add' a b := by
    funext node row
    exact map_add (HPullback (nodeProjection p node)) (a node row) (b node row)
  map_smul' c a := by
    funext node row
    exact map_smul (HPullback (nodeProjection p node)) c (a node row)

@[simp] theorem arraysPullback_apply (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (arrays : Arrays projected rows) (node : Nodes branch n)
    (row : Fin (rows (Nodes.height node))) :
    arraysPullback rows p arrays node row =
      HPullback (nodeProjection p node) (arrays node row) := rfl

end
end PerfectCompleteness.ChildBlockProjection

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_TerminalCalls
attribute [-instance] _root_.OAI.PerfectCompleteness.WholeArraySampler.stepFactorFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_selected _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected
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

def TerminalIndex (repeats : Nat → Nat) : {n m : Nat} → Path branch n m → Type
  | _, _, .refl _ => Unit
  | n + 1, _, .step _ p =>
      (Fin (repeats (n + 1)) × Bool) × TerminalIndex repeats p

noncomputable instance terminalIndexFintype (repeats : Nat → Nat) (p : Path branch n m) :
    Fintype (TerminalIndex repeats p) := by
  induction p with
  | refl n => exact inferInstanceAs (Fintype Unit)
  | @step n m i p ih =>
      letI : Fintype (TerminalIndex repeats p) := ih
      exact inferInstanceAs (Fintype
        ((Fin (repeats (n + 1)) × Bool) × TerminalIndex repeats p))

def drawIndex (repeats : Nat → Nat) : {n m : Nat} → (p : Path branch n m) →
    TerminalIndex repeats p → DrawIndex repeats p
  | _, _, .refl _, terminal => terminal
  | _, _, .step _ p, terminal => .inr (terminal.1, drawIndex repeats p terminal.2)

@[simp] theorem drawIndex_refl (repeats : Nat → Nat)
    (terminal : TerminalIndex (branch := branch) repeats (.refl n)) :
    drawIndex (branch := branch) repeats (.refl n) terminal = terminal := rfl

@[simp] theorem drawIndex_step (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (terminal : TerminalIndex repeats (.step i p)) :
    drawIndex repeats (.step i p) terminal =
      .inr (terminal.1, drawIndex repeats p terminal.2) := rfl

theorem drawIndex_injective (repeats : Nat → Nat) (p : Path branch n m) :
    Function.Injective (drawIndex repeats p) := by
  induction p with
  | refl n => exact fun _ _ h => h
  | @step n m i p ih =>
      intro a b h
      have heq := Sum.inr.inj h
      apply Prod.ext
      · exact congrArg
          (fun z : (Fin (repeats (n + 1)) × Bool) × DrawIndex repeats p => z.1) heq
      · exact ih (congrArg
          (fun z : (Fin (repeats (n + 1)) × Bool) × DrawIndex repeats p => z.2) heq)

def IsTerminal (repeats : Nat → Nat) : {n m : Nat} → (p : Path branch n m) →
    DrawIndex repeats p → Prop
  | _, _, .refl _, _ => True
  | _, _, .step _ p, j =>
      match j with
      | .inl _ => False
      | .inr j => IsTerminal repeats p j.2

@[simp] theorem isTerminal_refl (repeats : Nat → Nat)
    (j : DrawIndex (branch := branch) repeats (.refl n)) :
    IsTerminal (branch := branch) repeats (.refl n) j := True.intro

@[simp] theorem not_isTerminal_ordinary (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (j : OffPath i) :
    ¬ IsTerminal repeats (.step i p) (.inl j) := id

@[simp] theorem isTerminal_recursive (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (call : Fin (repeats (n + 1)) × Bool)
    (j : DrawIndex repeats p) :
    IsTerminal repeats (.step i p) (.inr (call, j)) ↔ IsTerminal repeats p j := Iff.rfl

theorem isTerminal_iff_exists (repeats : Nat → Nat) (p : Path branch n m) :
    ∀ j : DrawIndex repeats p,
      IsTerminal repeats p j ↔ ∃ terminal, drawIndex repeats p terminal = j := by
  induction p with
  | refl n =>
      intro j
      constructor
      · intro _
        exact ⟨j, rfl⟩
      · intro _
        exact True.intro
  | step i p ih =>
      intro j
      cases j with
      | inl j =>
          constructor
          · intro h
            exact False.elim h
          · rintro ⟨terminal, h⟩
            change (Sum.inr (terminal.1, drawIndex repeats p terminal.2) :
              DrawIndex repeats (.step i p)) = Sum.inl j at h
            exact Sum.inr_ne_inl h
      | inr j =>
          constructor
          · intro h
            obtain ⟨terminal, heq⟩ := (ih j.2).mp h
            refine ⟨(j.1, terminal), ?_⟩
            exact congrArg Sum.inr (Prod.ext rfl heq)
          · rintro ⟨terminal, h⟩
            exact (ih j.2).mpr
              ⟨terminal.2, congrArg Prod.snd (Sum.inr.inj h)⟩

theorem isTerminal_drawIndex (repeats : Nat → Nat) (p : Path branch n m)
    (terminal : TerminalIndex repeats p) :
    IsTerminal repeats p (drawIndex repeats p terminal) :=
  (isTerminal_iff_exists repeats p _).mpr ⟨terminal, rfl⟩

noncomputable def terminalSubtypeEquiv (repeats : Nat → Nat) (p : Path branch n m) :
    TerminalIndex repeats p ≃ {j : DrawIndex repeats p // IsTerminal repeats p j} :=
  Equiv.ofBijective
    (fun terminal => ⟨drawIndex repeats p terminal, isTerminal_drawIndex repeats p terminal⟩)
    ⟨fun _ _ h => drawIndex_injective repeats p (congrArg Subtype.val h), by
      rintro ⟨j, hj⟩
      obtain ⟨terminal, heq⟩ := (isTerminal_iff_exists repeats p j).mp hj
      exact ⟨terminal, Subtype.ext heq⟩⟩

@[simp] theorem terminalSubtypeEquiv_apply (repeats : Nat → Nat) (p : Path branch n m)
    (terminal : TerminalIndex repeats p) :
    (terminalSubtypeEquiv repeats p terminal).val = drawIndex repeats p terminal := rfl

@[simp] theorem card_refl (repeats : Nat → Nat) :
    Fintype.card (TerminalIndex (branch := branch) repeats (.refl n)) = 1 := by
  change Fintype.card Unit = 1
  exact Fintype.card_unit

end PerfectCompleteness.TerminalCalls

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_CutSamplerRefinement
attribute [-instance] _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.stepFactorFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
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

def RefinedSpace (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) → (A : Slots branch n → Type u) →
      DrawIndex repeats p → Type (max u w)
  | 0, _, .refl _, A, _ => space 𝕜 branch 0 A
  | n + 1, _, .refl _, A, _ =>
      (i : Fin (branch n)) → squareSpace (space 𝕜 branch n (childFamily A i))
  | n + 1, _, .step i p, A, j =>
      match j with
      | Sum.inl j => squareSpace (space 𝕜 branch n (childFamily A j.val))
      | Sum.inr j => RefinedSpace 𝕜 repeats p (childFamily A i) j.2

abbrev Tape (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) (A : Slots branch n → Type u) :=
  (j : DrawIndex repeats p) → RefinedSpace 𝕜 repeats p A j

end
end PerfectCompleteness.CutSamplerRefinement

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_CutTerminalSplit
attribute [-instance] _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_castSucc _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_last _root_.OAI.PerfectCompleteness.HierarchicalArrays.joint_component _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.NodeEmbedding.embed_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.embeddedRows_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.equiv_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.matrix_evaluate _root_.OAI.PerfectCompleteness.NodeEmbedding.rowsEquiv_apply _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset _root_.OAI.PerfectCompleteness.TreeCanonical.assignmentEquiv_apply _root_.OAI.PerfectCompleteness.TreeSourceSpaces.HPullback_apply _root_.OAI.PerfectCompleteness.TreeSourceSpaces.sourceProjection_apply _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_selected _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutTerminalSplit

open PointwiseSpaces RecursiveSpaces DescendantSpaces RecursiveSampler TerminalCalls
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m : Nat}

theorem refinedSpace_eq_terminal (𝕜 : Type w) [Field 𝕜]
    (repeats : Nat → Nat) (p : Path branch n m) :
    ∀ (A : Slots branch n → Type u) (terminal : TerminalIndex repeats p),
      CutSamplerRefinement.RefinedSpace 𝕜 repeats p A (drawIndex repeats p terminal) =
        CutSamplerRefinement.RefinedSpace 𝕜 repeats (.refl m) (p.family A) () := by
  induction p with
  | refl n =>
      intro A terminal
      cases terminal
      rfl
  | step i p ih =>
      intro A terminal
      exact ih (childFamily A i) terminal.2

variable (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
  (p : Path branch n (m + 1)) (A : Slots branch n → Type u)

abbrev TerminalFactor :=
  (i : Fin (branch m)) → squareSpace (space 𝕜 branch m (childFamily (p.family A) i))

abbrev TerminalTape := TerminalIndex repeats p → TerminalFactor 𝕜 p A

abbrev ExteriorIndex := {j : DrawIndex repeats p // ¬ IsTerminal repeats p j}

abbrev ExteriorTape :=
  (j : ExteriorIndex repeats p) → CutSamplerRefinement.RefinedSpace 𝕜 repeats p A j.val

def terminalFactorEquiv (terminal : TerminalIndex repeats p) :
    CutSamplerRefinement.RefinedSpace 𝕜 repeats p A (drawIndex repeats p terminal) ≃
      TerminalFactor 𝕜 p A :=
  Equiv.cast (refinedSpace_eq_terminal 𝕜 repeats p A terminal)

def terminalTapeEquiv :
    ((j : {j : DrawIndex repeats p // IsTerminal repeats p j}) →
      CutSamplerRefinement.RefinedSpace 𝕜 repeats p A j.val) ≃
        TerminalTape 𝕜 repeats p A :=
  ((Equiv.piCongrLeft
    (fun j : {j : DrawIndex repeats p // IsTerminal repeats p j} =>
      CutSamplerRefinement.RefinedSpace 𝕜 repeats p A j.val)
    (terminalSubtypeEquiv repeats p)).symm).trans
      (Equiv.piCongrRight (terminalFactorEquiv 𝕜 repeats p A))

def splitTape :
    CutSamplerRefinement.Tape 𝕜 repeats p A ≃
      TerminalTape 𝕜 repeats p A × ExteriorTape 𝕜 repeats p A :=
  (Equiv.piEquivPiSubtypeProd (IsTerminal repeats p)
    (CutSamplerRefinement.RefinedSpace 𝕜 repeats p A)).trans
      (Equiv.prodCongr (terminalTapeEquiv 𝕜 repeats p A) (Equiv.refl _))

@[simp] theorem splitTape_terminal_apply
    (x : CutSamplerRefinement.Tape 𝕜 repeats p A) (terminal : TerminalIndex repeats p) :
    (splitTape 𝕜 repeats p A x).1 terminal =
      terminalFactorEquiv 𝕜 repeats p A terminal (x (drawIndex repeats p terminal)) := rfl

@[simp] theorem splitTape_exterior_apply
    (x : CutSamplerRefinement.Tape 𝕜 repeats p A) (j : ExteriorIndex repeats p) :
    (splitTape 𝕜 repeats p A x).2 j = x j.val := rfl

end
end PerfectCompleteness.CutTerminalSplit

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_ManyGoodRowsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.HierarchicalArrays.joint_component _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.NodeEmbedding.embed_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.embeddedRows_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.equiv_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.matrix_evaluate _root_.OAI.PerfectCompleteness.NodeEmbedding.rowsEquiv_apply _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.TreeCanonical.assignmentEquiv_apply _root_.OAI.PerfectCompleteness.TreeSourceSpaces.HPullback_apply _root_.OAI.PerfectCompleteness.TreeSourceSpaces.sourceProjection_apply _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_selected _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.ProductEvaluation

open MixedSupport CanonicalKeys

variable {X C Z : Type*} {Row : C → Type*}


variable {n : Nat}
variable (slots : Fin n → Slot)
variable (H : Submodule F2 (Assignment slots → F2))
variable (rows : (c : C) → Row c → Assignment slots → F2)
variable (other : Assignment slots → Z)
variable (hone : (1 : Assignment slots → F2) ∈ H)
variable (hproducts : ∀ c u v, rows c u * rows c v ∈ H)

noncomputable def realizingPoint (P : Label slots (displayedJoint rows other)) :
    Assignment slots :=
  ReducedPartition.representative (reduction slots (displayedJoint rows other))
    (displayedJoint rows other) P

noncomputable def restoredRows (P : Label slots (displayedJoint rows other)) :
    (c : C) → Row c → F2 :=
  (restore slots (displayedJoint rows other) P).1

@[simp] theorem restoredRows_apply (P : Label slots (displayedJoint rows other))
    (c : C) (u : Row c) :
    restoredRows slots rows other P c u = rows c u (realizingPoint slots rows other P) := rfl

end PerfectCompleteness.ProductEvaluation

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_RelativeDescendantProductsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawIndexDecidableEq _root_.OAI.PerfectCompleteness.RecursiveSampler.drawIndexFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.RelativeDescendantProducts

open TreeSourceSpaces HierarchicalArrays

variable {branch : Nat → Nat} {n t : Nat}

inductive Below (branch : Nat → Nat) :
    {n : Nat} → Nodes branch n → Nodes branch n → Prop
  | root {n : Nat} (i : Fin (branch n)) (lower : Nodes branch n) :
      Below branch (n := n + 1) (.inl ()) (.inr (i, lower))
  | child {n : Nat} {upper lower : Nodes branch n} (i : Fin (branch n)) :
      Below branch upper lower →
        Below branch (n := n + 1) (.inr (i, upper)) (.inr (i, lower))

theorem Below.height_lt {upper lower : Nodes branch n}
    (h : Below branch upper lower) : Nodes.height lower < Nodes.height upper := by
  induction h with
  | root i lower => exact Nat.lt_succ_of_le (Nodes.height_le lower)
  | child i h ih => exact ih

theorem Below.ne {upper lower : Nodes branch n}
    (h : Below branch upper lower) : lower ≠ upper := by
  intro heq
  have hlt := h.height_lt
  rw [heq] at hlt
  exact Nat.lt_irrefl _ hlt

def relativeNode : {n : Nat} → (upper : Nodes branch n) →
    Nodes branch (Nodes.height upper) → Nodes branch n
  | 0, upper, _ => nomatch upper
  | _ + 1, .inl _, lower => lower
  | _ + 1, .inr (i, upper), lower => .inr (i, relativeNode upper lower)

theorem relativeNode_height : ∀ {n : Nat} (upper : Nodes branch n)
    (lower : Nodes branch (Nodes.height upper)),
    Nodes.height (relativeNode upper lower) = Nodes.height lower := by
  intro n
  induction n with
  | zero => intro upper; exact nomatch upper
  | succ n ih =>
      intro upper lower
      cases upper with
      | inl _ => rfl
      | inr pair => exact ih pair.2 lower

theorem relativeNode_below : ∀ {n : Nat} (upper : Nodes branch n)
    (lower : Nodes branch (Nodes.height upper)),
    Nodes.height lower < Nodes.height upper →
      Below branch upper (relativeNode upper lower) := by
  intro n
  induction n with
  | zero => intro upper; exact nomatch upper
  | succ n ih =>
      intro upper lower hproper
      cases upper with
      | inl u =>
          cases u
          cases lower with
          | inl _ => exact False.elim (Nat.lt_irrefl _ hproper)
          | inr pair => exact Below.root pair.1 pair.2
      | inr pair => exact Below.child pair.1 (ih pair.2 lower hproper)

abbrev RelativeDescendant (upper : Nodes branch n) :=
  {lower : Nodes branch (Nodes.height upper) // Nodes.height lower < Nodes.height upper}

def descendantIndex (upper : Nodes branch n) (lower : RelativeDescendant upper) :
    {j : Nodes branch n // j ≠ upper} :=
  ⟨relativeNode upper lower.val, (relativeNode_below upper lower.val lower.property).ne⟩

theorem descendantIndex_below (upper : Nodes branch n)
    (lower : RelativeDescendant upper) :
    Below branch upper (descendantIndex upper lower).val :=
  relativeNode_below upper lower.val lower.property

theorem pullback_square_exists {upper lower : Nodes branch n}
    (h : Below branch upper lower) :
    ∀ (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
      (_ : ∀ k < n, 0 < branch k)
      (f : Domain (nodeSlots slots lower) → F2),
      f ∈ PointwiseSpaces.squareSpace (NodeEmbedding.NodeH slots lower) →
        ∃ g ∈ NodeEmbedding.NodeH slots upper,
          PointwiseSpaces.pullback F2 (restrictNode slots upper) g =
            PointwiseSpaces.pullback F2 (restrictNode slots lower) f := by
  induction h with
  | @root n i lower =>
      intro slots hbranch f hf
      refine ⟨PointwiseSpaces.pullback F2 (restrictNode slots (.inr (i, lower))) f, ?_, rfl⟩
      exact DescendantSpaces.descendant_square_le_space
        (.step i (Nodes.path lower)) (LeafDomain slots) hbranch
        (Nat.lt_succ_of_le (Nodes.height_le lower)) (Submodule.mem_map_of_mem hf)
  | @child n upper lower i h ih =>
      intro slots hbranch f hf
      let childSlots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot :=
        fun s => slots (i, s)
      have hb : ∀ k < n, 0 < branch k :=
        fun k hk => hbranch k (Nat.lt_trans hk (Nat.lt_succ_self n))
      obtain ⟨g, hg, heq⟩ := ih childSlots hb f hf
      refine ⟨g, hg, ?_⟩
      exact congrArg
        (PointwiseSpaces.pullback F2 (RecursiveSpaces.childRestriction (LeafDomain slots) i)) heq

noncomputable section

theorem squareSpace_le_rowSpace
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (hbranch : ∀ k < n, 0 < branch k) {upper lower : Nodes branch n}
    (h : Below branch upper lower) :
    PointwiseSpaces.squareSpace (NodeEmbedding.RowSpace slots lower) ≤
      NodeEmbedding.RowSpace slots upper := by
  rw [NodeEmbedding.squareSpace_eq]
  intro f hf
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hf
  obtain ⟨u, hu, heq⟩ := pullback_square_exists h slots hbranch g hg
  refine Submodule.mem_map.mpr ⟨u, hu, ?_⟩
  funext x
  exact congrFun heq ((TreeCanonical.assignmentEquiv slots).symm x)

end
end PerfectCompleteness.RelativeDescendantProducts



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalFrozenTablesLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawIndexDecidableEq _root_.OAI.PerfectCompleteness.RecursiveSampler.drawIndexFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.RecursiveSampler.combine_zero _root_.OAI.PerfectCompleteness.RecursiveSampler.evaluate_refl _root_.OAI.PerfectCompleteness.RecursiveSampler.evaluate_zeroTape _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset _root_.OAI.PerfectCompleteness.TerminalCalls.card_refl _root_.OAI.PerfectCompleteness.TerminalCalls.drawIndex_refl _root_.OAI.PerfectCompleteness.TerminalCalls.drawIndex_step _root_.OAI.PerfectCompleteness.TerminalCalls.isTerminal_recursive _root_.OAI.PerfectCompleteness.TerminalCalls.isTerminal_refl _root_.OAI.PerfectCompleteness.TerminalCalls.not_isTerminal_ordinary _root_.OAI.PerfectCompleteness.TerminalCalls.terminalSubtypeEquiv_apply _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_selected _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected
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

abbrev LowerNodes := {d : RelativeDescendantProducts.RelativeDescendant upper //
  Nodes.height d.val = lowerLevel}

def lowerIndex (d : LowerNodes upper lowerLevel) : {j : Nodes branch n // j ≠ upper} :=
  RelativeDescendantProducts.descendantIndex upper d.val

end
end PerfectCompleteness.HierarchicalFrozenTables



section

namespace PerfectCompleteness.DescendantSpaces.Path

open RecursiveSpaces

universe u

variable {branch : Nat → Nat} {n m k l : Nat}

def append : {n m k : Nat} → Path branch n m → Path branch m k → Path branch n k
  | _, _, _, .refl _, q => q
  | _, _, _, .step i p, q => .step i (append p q)

@[simp] theorem append_refl (q : Path branch n m) : (Path.refl n).append q = q := rfl

@[simp] theorem append_step (i : Fin (branch n)) (p : Path branch n m)
    (q : Path branch m k) : (Path.step i p).append q = Path.step i (p.append q) := rfl

@[simp] theorem append_refl_right (p : Path branch n m) : p.append (.refl m) = p := by
  induction p with
  | refl n => rfl
  | step i p ih => exact congrArg (Path.step i) ih

@[simp] theorem slotEmbedding_append (p : Path branch n m) :
    ∀ (q : Path branch m k) (s : Slots branch k),
      (p.append q).slotEmbedding s = p.slotEmbedding (q.slotEmbedding s) := by
  induction p with
  | refl n => intro q s; rfl
  | step i p ih =>
      intro q s
      exact congrArg (fun t => (i, t)) (ih q s)

end PerfectCompleteness.DescendantSpaces.Path

end


namespace PerfectCompleteness.GeometricCutSplit

open RecursiveSpaces DescendantSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

variable {branch : Nat → Nat}

def splitDepth (cutoff : Nat) : (depth : Nat) →
    Slots branch (cutoff + depth) ≃ PrefixDepth branch cutoff depth × Slots branch cutoff
  | 0 =>
      { toFun := fun suffix => ((), suffix)
        invFun := Prod.snd
        left_inv := fun _ => rfl
        right_inv := by rintro ⟨⟨⟩, suffix⟩; rfl }
  | depth + 1 =>
      ((Equiv.refl (Fin (branch (cutoff + depth)))).prodCongr (splitDepth cutoff depth)).trans
        (Equiv.prodAssoc _ _ _).symm

variable {root cutoff : Nat}

def joinEquiv (hcut : cutoff ≤ root) :
    Prefix branch root cutoff × Slots branch cutoff ≃ Slots branch root :=
  (splitDepth cutoff (root - cutoff)).symm.trans
    (Equiv.cast (congrArg (Slots branch) (Nat.add_sub_of_le hcut)))

def splitEquiv (hcut : cutoff ≤ root) :
    Slots branch root ≃ Prefix branch root cutoff × Slots branch cutoff :=
  (joinEquiv hcut).symm

@[simp] theorem join_split (hcut : cutoff ≤ root) (leaf : Slots branch root) :
    joinEquiv hcut (splitEquiv hcut leaf) = leaf :=
  (joinEquiv hcut).apply_symm_apply leaf

end PerfectCompleteness.GeometricCutSplit



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_HierarchicalLeftDecoder
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.squareProduct_val _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_selected _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected
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

abbrev LowerNode (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :=
  (HierarchicalFrozenTables.lowerIndex upper lowerLevel d).val

variable (hbranch : ∀ k < n, 0 < branch k)

local instance rowSpaceFintype_rc6598c_1 (node : Nodes branch n) :
    Fintype (NodeEmbedding.RowSpace slots node) := Fintype.ofFinite _
local instance nodeSpaceFintype_rc6598c_1 (node : Nodes branch n) :
    Fintype (NodeEmbedding.NodeH slots node) := Fintype.ofFinite _
local instance upperDualFintype_rc6598c_1 : Fintype (Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)
def squareEmbedding (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :
    squareSpace (NodeEmbedding.NodeH slots (LowerNode upper lowerLevel d)) →ₗ[F2]
      NodeEmbedding.RowSpace slots upper where
  toFun f := ⟨PointwiseSpaces.pullback F2
    (NodeEmbedding.numberedRestriction slots (LowerNode upper lowerLevel d)) f.val, by
      apply RelativeDescendantProducts.squareSpace_le_rowSpace slots hbranch
        (RelativeDescendantProducts.descendantIndex_below upper d.val)
      rw [NodeEmbedding.squareSpace_eq]
      exact Submodule.mem_map_of_mem f.property⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp] theorem squareEmbedding_apply
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (f : squareSpace (NodeEmbedding.NodeH slots (LowerNode upper lowerLevel d)))
    (x : NodeEmbedding.NumberedDomain slots) :
    (squareEmbedding slots upper lowerLevel hbranch d f).val x =
      f.val (NodeEmbedding.numberedRestriction slots (LowerNode upper lowerLevel d) x) := rfl

end
end PerfectCompleteness.HierarchicalLeftDecoder

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_DecoderContraction
attribute [-instance] _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawIndexDecidableEq _root_.OAI.PerfectCompleteness.RecursiveSampler.drawIndexFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_refl _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_refl_right _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_step _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_castSucc _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_last _root_.OAI.PerfectCompleteness.HierarchicalArrays.joint_component _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.NodeEmbedding.embed_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.embeddedRows_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.equiv_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.matrix_evaluate _root_.OAI.PerfectCompleteness.NodeEmbedding.rowsEquiv_apply _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.RecursiveSampler.combine_zero _root_.OAI.PerfectCompleteness.RecursiveSampler.evaluate_refl _root_.OAI.PerfectCompleteness.RecursiveSampler.evaluate_zeroTape _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.squareProduct_val _root_.OAI.PerfectCompleteness.RecursiveSpaceEquiv.spaceEquiv_apply _root_.OAI.PerfectCompleteness.RecursiveSpaceEquiv.squareEquiv_apply _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset _root_.OAI.PerfectCompleteness.TerminalCalls.card_refl _root_.OAI.PerfectCompleteness.TerminalCalls.drawIndex_refl _root_.OAI.PerfectCompleteness.TerminalCalls.drawIndex_step _root_.OAI.PerfectCompleteness.TerminalCalls.isTerminal_recursive _root_.OAI.PerfectCompleteness.TerminalCalls.isTerminal_refl _root_.OAI.PerfectCompleteness.TerminalCalls.not_isTerminal_ordinary _root_.OAI.PerfectCompleteness.TerminalCalls.terminalSubtypeEquiv_apply _root_.OAI.PerfectCompleteness.TreeCanonical.assignmentEquiv_apply _root_.OAI.PerfectCompleteness.UniformChildSum.childSum_apply _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_selected _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
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

def baseFrequency (W : Submodule F2 K) (σ : Module.Dual F2 K)
    (z : Module.Dual F2 H) : Module.Dual F2 (W ⊗[F2] H) :=
  pureFrequency (σ.comp W.subtype) z

@[simp] theorem baseFrequency_tmul (W : Submodule F2 K) (σ : Module.Dual F2 K)
    (z : Module.Dual F2 H) (w : W) (h : H) :
    baseFrequency W σ z (w ⊗ₜ[F2] h) = σ w.val * z h :=
  pureFrequency_tmul (σ.comp W.subtype) z w h

def errorSpace (W : Submodule F2 K) (Q : Submodule F2 (Module.Dual F2 H)) :
    Submodule F2 (Module.Dual F2 (W ⊗[F2] H)) where
  carrier := {Ψ | ∀ w : W, scalarRestriction Ψ w ∈ Q}
  zero_mem' := by
    intro w
    rw [scalarRestriction_zero]
    exact Q.zero_mem
  add_mem' := by
    intro Φ Ψ hΦ hΨ w
    rw [scalarRestriction_add]
    exact Q.add_mem (hΦ w) (hΨ w)
  smul_mem' := by
    intro c Ψ hΨ w
    rw [scalarRestriction_smul]
    exact Q.smul_mem c (hΨ w)

@[simp] theorem mem_errorSpace (W : Submodule F2 K)
    (Q : Submodule F2 (Module.Dual F2 H)) (Ψ : Module.Dual F2 (W ⊗[F2] H)) :
    Ψ ∈ errorSpace W Q ↔ ∀ w : W, scalarRestriction Ψ w ∈ Q := Iff.rfl


variable {branch : Nat → Nat} {n m : Nat}

def descendantSquareEmbedding (p : DescendantSpaces.Path branch n m)
    (A : Slots branch n → Type*) (hbranch : ∀ k < n, 0 < branch k) (hproper : m < n) :
    squareSpace (space F2 branch m (p.family A)) →ₗ[F2] space F2 branch n A where
  toFun f := ⟨pullback F2 (p.restriction A) f.val,
    DescendantSpaces.descendant_square_le_space p A hbranch hproper
      (Submodule.mem_map_of_mem f.property)⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp] theorem descendantSquareEmbedding_apply (p : DescendantSpaces.Path branch n m)
    (A : Slots branch n → Type*) (hbranch : ∀ k < n, 0 < branch k) (hproper : m < n)
    (f : squareSpace (space F2 branch m (p.family A))) (x : Assignment A) :
    (descendantSquareEmbedding p A hbranch hproper f).val x = f.val (p.restriction A x) := rfl


end
end PerfectCompleteness.DecoderContraction

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_OwnInputReferenceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_castSucc _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_last _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_selected _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected
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

abbrev UpperSpace := H (nodeSlots slots upper)
abbrev UpperVector := Block rows upper
abbrev LowerVector := Block rows lower
abbrev OtherNodes := {node : Nodes branch n // node ≠ upper ∧ node ≠ lower}

structure Cut where
  proper : Nodes.height lower < Nodes.height upper
  path : DescendantSpaces.Path branch (Nodes.height upper) (Nodes.height lower)
  slots_agree : ∀ s,
    (Nodes.path upper).slotEmbedding (path.slotEmbedding s) =
      (Nodes.path lower).slotEmbedding s

theorem Cut.family_eq (cut : Cut upper lower) :
    cut.path.family (LeafDomain (nodeSlots slots upper)) = LeafDomain (nodeSlots slots lower) := by
  funext s
  change ((k : Fin t) →
      (slots ((Nodes.path upper).slotEmbedding (cut.path.slotEmbedding s)) k).Domain) =
    ((k : Fin t) → (slots ((Nodes.path lower).slotEmbedding s) k).Domain)
  rw [cut.slots_agree]

abbrev OtherArrays :=
  (node : OtherNodes upper lower) →
    Fin (rows (Nodes.height node.1)) → H (nodeSlots slots node.1)

structure Exterior where
  otherArrays : OtherArrays slots rows upper lower
  lowerRows : Fin (rows (Nodes.height lower)) → H (nodeSlots slots lower)

end
end PerfectCompleteness.OwnInputReference



namespace PerfectCompleteness.OwnInputCanonicalQuery

open scoped Classical
open TreeSourceSpaces HierarchicalArrays

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat) (upper lower : Nodes branch n)

def assemble (upperRows : Fin (rows (Nodes.height upper)) → H (nodeSlots slots upper))
    (external : OwnInputReference.Exterior slots rows upper lower) : Arrays slots rows :=
  fun node => if hu : node = upper then hu.symm ▸ upperRows
    else if hl : node = lower then hl.symm ▸ external.lowerRows
    else external.otherArrays ⟨node, hu, hl⟩

@[simp] theorem assemble_upper
    (upperRows : Fin (rows (Nodes.height upper)) → H (nodeSlots slots upper))
    (external : OwnInputReference.Exterior slots rows upper lower) :
    assemble slots rows upper lower upperRows external upper = upperRows := by
  simp [assemble]

@[simp] theorem assemble_lower (hne : upper ≠ lower)
    (upperRows : Fin (rows (Nodes.height upper)) → H (nodeSlots slots upper))
    (external : OwnInputReference.Exterior slots rows upper lower) :
    assemble slots rows upper lower upperRows external lower = external.lowerRows := by
  simp [assemble, Ne.symm hne]

@[simp] theorem assemble_other
    (upperRows : Fin (rows (Nodes.height upper)) → H (nodeSlots slots upper))
    (external : OwnInputReference.Exterior slots rows upper lower)
    (node : OwnInputReference.OtherNodes upper lower) :
    assemble slots rows upper lower upperRows external node.val = external.otherArrays node := by
  simp only [assemble, dite_eq_right node.property.1, dite_eq_right node.property.2]

end
end PerfectCompleteness.OwnInputCanonicalQuery

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_DesignatedLeavesLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.restriction_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.restriction_refl _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_refl _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_step _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_castSucc _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_last _root_.OAI.PerfectCompleteness.HierarchicalArrays.joint_component _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.NodeEmbedding.embed_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.embeddedRows_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.equiv_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.matrix_evaluate _root_.OAI.PerfectCompleteness.NodeEmbedding.rowsEquiv_apply _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.RecursiveSampler.combine_zero _root_.OAI.PerfectCompleteness.RecursiveSampler.evaluate_refl _root_.OAI.PerfectCompleteness.RecursiveSampler.evaluate_zeroTape _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset _root_.OAI.PerfectCompleteness.TreeCanonical.assignmentEquiv_apply _root_.OAI.PerfectCompleteness.TreeSourceSpaces.HPullback_apply _root_.OAI.PerfectCompleteness.TreeSourceSpaces.sourceProjection_apply _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_selected _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.DesignatedLeaves

open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {height : Nat}
  (designated : Fin (branch height) → Slots branch height)
  (clean : Fin (branch height) → Prop)

def selected (leaf : Slots branch (height + 1)) : Prop :=
  clean leaf.1 ∧ leaf.2 = designated leaf.1

abbrev Leaves := {leaf : Slots branch (height + 1) // selected designated clean leaf}

def equiv : Children clean ≃ Leaves designated clean where
  toFun i := ⟨(i.val, designated i.val), i.property, rfl⟩
  invFun leaf := ⟨leaf.val.1, leaf.property.1⟩
  left_inv i := rfl
  right_inv leaf := by
    apply Subtype.ext
    exact Prod.ext rfl leaf.property.2.symm

@[simp] theorem equiv_apply (i : Children clean) :
    (equiv designated clean i).val = (i.val, designated i.val) := rfl

@[simp] theorem equiv_symm_apply (leaf : Leaves designated clean) :
    (equiv designated clean).symm leaf = ⟨leaf.val.1, leaf.property.1⟩ := rfl


end
end PerfectCompleteness.DesignatedLeaves



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CutChildCleanLawLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.ProjectedCleanRate

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces UniformCleanSources

noncomputable section

def projectionFlag (cube : Nat) (hcube : 0 < cube) : FiniteDistribution Bool :=
  RepetitionRate.bernoulli (projectionDensity cube)
    (projectionDensity_bounds hcube).1 (projectionDensity_bounds hcube).2

@[simp] theorem projectionFlag_true (cube : Nat) (hcube : 0 < cube) :
    (projectionFlag cube hcube).weight true = projectionDensity cube := by
  simp [projectionFlag, RepetitionRate.bernoulli]

end
end PerfectCompleteness.ProjectedCleanRate

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_RightDecoderLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_castSucc _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_last _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset _root_.OAI.PerfectCompleteness.UniformChildSum.childSum_apply _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_selected _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected
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

local instance characterFintype : Fintype (Module.Dual F2 (UpperVector rows upper)) :=
  Fintype.ofInjective
    (fun f : Module.Dual F2 (UpperVector rows upper) =>
      (f : UpperVector rows upper → F2)) DFunLike.coe_injective

local instance scalarFintype : Fintype (Module.Dual F2 (UpperSpace slots upper)) := by
  letI : Fintype (UpperSpace slots upper) := Fintype.ofFinite _
  exact Fintype.ofInjective
    (fun f : Module.Dual F2 (UpperSpace slots upper) =>
      (f : UpperSpace slots upper → F2)) DFunLike.coe_injective

end
end PerfectCompleteness.RightDecoder



namespace PerfectCompleteness.RightDecoderDescendant

open scoped TensorProduct Classical
open UniqueGamesTheorem.Foundations.Games
open PointwiseSpaces TreeSourceSpaces HierarchicalArrays OwnInputReference

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper lower : Nodes branch n) (cut : Cut upper lower)

def leafEquiv (s : RecursiveSpaces.Slots branch (Nodes.height lower)) :
    cut.path.family (LeafDomain (nodeSlots slots upper)) s ≃
      LeafDomain (nodeSlots slots lower) s :=
  Equiv.cast (congrFun
    (Cut.family_eq (slots := slots) (upper := upper) (lower := lower) cut) s)

def restriction : Domain (nodeSlots slots upper) → Domain (nodeSlots slots lower) :=
  fun x => RecursiveSpaces.project (fun s => leafEquiv slots upper lower cut s)
    (cut.path.restriction (LeafDomain (nodeSlots slots upper)) x)

variable (hbranch : ∀ k < Nodes.height upper, 0 < branch k)

def squareEmbedding :
    squareSpace (H (nodeSlots slots lower)) →ₗ[F2] UpperSpace slots upper :=
  (DecoderContraction.descendantSquareEmbedding cut.path
    (LeafDomain (nodeSlots slots upper)) hbranch cut.proper).comp
      (RecursiveSpaceEquiv.squareEquiv (𝕜 := F2)
        (leafEquiv slots upper lower cut)).toLinearMap

@[simp] theorem squareEmbedding_apply
    (f : squareSpace (H (nodeSlots slots lower))) (x : Domain (nodeSlots slots upper)) :
    (squareEmbedding slots upper lower cut hbranch f).val x =
      f.val (restriction slots upper lower cut x) := rfl

def functional (z : Module.Dual F2 (UpperSpace slots upper)) :
    Module.Dual F2 (squareSpace (H (nodeSlots slots lower))) :=
  z.comp (squareEmbedding slots upper lower cut hbranch)

abbrev Form := H (nodeSlots slots lower) →ₗ[F2] H (nodeSlots slots lower) →ₗ[F2] F2

def form (z : Module.Dual F2 (UpperSpace slots upper)) : Form slots lower :=
  OddListExtraction.multiplicationForm (H (nodeSlots slots lower))
    (functional slots upper lower cut hbranch z)

@[simp] theorem form_apply (z : Module.Dual F2 (UpperSpace slots upper))
    (f g : H (nodeSlots slots lower)) :
    form slots upper lower cut hbranch z f g =
      z (squareEmbedding slots upper lower cut hbranch
        (OddListExtraction.productElement (H (nodeSlots slots lower)) f g)) := rfl


end
end PerfectCompleteness.RightDecoderDescendant

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_DecoderSourcePullback
attribute [-instance] _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self
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

variable (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
  (upper lower : Nodes branch n) (cut : Cut upper lower)

def upperTarget (q : Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :
    Module.Dual F2 (UpperSpace projected upper) :=
  (q.comp (NodeEmbedding.equiv slots upper).toLinearMap).comp
    (HPullback (nodeProjection p upper))

@[simp] theorem upperTarget_apply
    (q : Module.Dual F2 (NodeEmbedding.RowSpace slots upper))
    (f : UpperSpace projected upper) :
    upperTarget p upper q f =
      q (NodeEmbedding.embed slots upper (HPullback (nodeProjection p upper) f)) := rfl


end
end PerfectCompleteness.DecoderSourcePullback

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_ProjectedNodeEmbedding
attribute [-instance] _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ProjectedNodeEmbedding

noncomputable section

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays
open ChildBlockProjection (nodeProjection squarePullback)

variable {branch : Nat → Nat} {n t : Nat}
  {slots projected : Slots branch n → Fin t → MixedSupport.Slot}
  (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
  (upper : Nodes branch n)

def nativePullback :
    NodeEmbedding.NodeH projected upper →ₗ[F2] NodeEmbedding.NodeH slots upper :=
  HPullback (nodeProjection p upper)

@[simp] theorem nativePullback_apply
    (f : NodeEmbedding.NodeH projected upper) (x : Domain (nodeSlots slots upper)) :
    (nativePullback p upper f).val x =
      f.val (sourceProjection (nodeProjection p upper) x) := rfl

def intoOriginal :
    NodeEmbedding.NodeH projected upper →ₗ[F2] NodeEmbedding.RowSpace slots upper :=
  (NodeEmbedding.embed slots upper).comp (nativePullback p upper)

@[simp] theorem intoOriginal_apply
    (f : NodeEmbedding.NodeH projected upper) (x : NodeEmbedding.NumberedDomain slots) :
    (intoOriginal p upper f).val x =
      f.val (sourceProjection (nodeProjection p upper)
        (NodeEmbedding.numberedRestriction slots upper x)) := rfl

def intoOriginalSquare :
    PointwiseSpaces.squareSpace (NodeEmbedding.NodeH projected upper) →ₗ[F2]
      PointwiseSpaces.squareSpace (NodeEmbedding.RowSpace slots upper) where
  toFun f := ⟨PointwiseSpaces.pullback F2 (NodeEmbedding.numberedRestriction slots upper)
    (squarePullback (nodeProjection p upper) f).val, by
      rw [NodeEmbedding.squareSpace_eq]
      exact Submodule.mem_map_of_mem (squarePullback (nodeProjection p upper) f).property⟩
  map_add' f g := by apply Subtype.ext; rfl
  map_smul' c f := by apply Subtype.ext; rfl

@[simp] theorem intoOriginalSquare_apply
    (f : PointwiseSpaces.squareSpace (NodeEmbedding.NodeH projected upper))
    (x : NodeEmbedding.NumberedDomain slots) :
    (intoOriginalSquare p upper f).val x =
      f.val (sourceProjection (nodeProjection p upper)
        (NodeEmbedding.numberedRestriction slots upper x)) := rfl

end
end PerfectCompleteness.ProjectedNodeEmbedding

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_BucketUsefulCollision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.BucketUsefulCollision

noncomputable section

open scoped Classical
open ClauseSupport MixedSupport
open UniqueGamesTheorem.Foundations.Games
open BucketSampler (F2 Direction Tape)

section Product

variable {H : Type*} {ℓ : Nat}

def fill (a : Direction ℓ)
    (b : FiniteProductSplit.Others (Ω := fun _ : Direction ℓ => H) a)
    (h : H) : Tape ℓ H :=
  fun d => if hd : d = a then h else b ⟨d, hd⟩

@[simp] theorem fill_self (a : Direction ℓ)
    (b : FiniteProductSplit.Others (Ω := fun _ : Direction ℓ => H) a)
    (h : H) : fill a b h a = h := by
  simp [fill]

end Product


end
end PerfectCompleteness.BucketUsefulCollision

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

def childProjection
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (i : Fin (branch n)) :
    ∀ s k, MixedSupport.Projection (childSlots slots i s k) (childSlots projected i s k) :=
  fun s k => p (i, s) k

end
end PerfectCompleteness.ChildAssemblyProjection

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalAgreementMean
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
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

abbrev Background := HierarchicalMatrixTable.Background (rows := rows) slots upper

end
end PerfectCompleteness.HierarchicalAgreementMean

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_HierarchicalUsefulCollision
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
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

abbrev Background := HierarchicalAgreementMean.Background (rows := rows) slots upper

local instance backgroundFintype : Fintype (Background (rows := rows) slots upper) :=
  Fintype.ofFinite _

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _

end
end PerfectCompleteness.HierarchicalUsefulCollision

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_CanonicalCoarseningErasure
attribute [-instance] _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.HierarchicalArrays.joint_component _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.NodeEmbedding.embed_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.embeddedRows_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.equiv_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.matrix_evaluate _root_.OAI.PerfectCompleteness.NodeEmbedding.rowsEquiv_apply _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.TreeCanonical.assignmentEquiv_apply _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_selected _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CanonicalCoarseningErasure

open MixedSupport CanonicalKeys CanonicalKeyShape CanonicalEdges

noncomputable section

variable {n : Nat} {Y Z : Type*}

def transportLabel (slots : Fin n → Slot) (f : Assignment slots → Y)
    (P : Label slots f) : Label (dummySlots (shape slots)) (transport slots f) :=
  ⟨P.val, by
    change P.val ∈ CanonicalKeys.partition (dummySlots (shape slots)) (transport slots f)
    rw [← partition_erasure slots f]
    exact P.property⟩

@[simp] theorem transportLabel_val (slots : Fin n → Slot) (f : Assignment slots → Y)
    (P : Label slots f) : (transportLabel slots f P).val = P.val := rfl

theorem restore_transportLabel (slots : Fin n → Slot) (f : Assignment slots → Y)
    (P : Label slots f) :
    restore slots f P =
      restore (dummySlots (shape slots)) (transport slots f) (transportLabel slots f P) := by
  exact ReducedPartition.output_eq_of_shared_part
    (assignmentEquiv slots)
    (reduction slots f) (reduction (dummySlots (shape slots)) (transport slots f))
    f (transport slots f) (reduction_erasure slots f)
    (fun x => (transport_apply slots f x).symm)
    (constantOnFibers (dummySlots (shape slots)) (transport slots f))
    P (transportLabel slots f P) rfl

theorem coarsen_transportLabel (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (P : Label slots f) :
    transportLabel slots (p ∘ f) (coarsen slots f p P) =
      coarsen (dummySlots (shape slots)) (transport slots f) p (transportLabel slots f P) := by
  apply restore_injective (dummySlots (shape slots)) (p ∘ transport slots f)
  calc
    restore (dummySlots (shape slots)) (p ∘ transport slots f)
        (transportLabel slots (p ∘ f) (coarsen slots f p P)) =
        restore slots (p ∘ f) (coarsen slots f p P) :=
      (restore_transportLabel slots (p ∘ f) (coarsen slots f p P)).symm
    _ = p (restore slots f P) := restore_coarsen slots f p P
    _ = p (restore (dummySlots (shape slots)) (transport slots f)
        (transportLabel slots f P)) := congrArg p (restore_transportLabel slots f P)
    _ = restore (dummySlots (shape slots)) (p ∘ transport slots f)
        (coarsen (dummySlots (shape slots)) (transport slots f) p (transportLabel slots f P)) :=
      (restore_coarsen (dummySlots (shape slots)) (transport slots f) p
        (transportLabel slots f P)).symm

theorem coarsen_val (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (P : Label slots f) :
    (coarsen slots f p P).val =
      (coarsen (dummySlots (shape slots)) (transport slots f) p
        (transportLabel slots f P)).val :=
  congrArg Subtype.val (coarsen_transportLabel slots f p P)

@[simp] theorem partIndex_transportLabel (slots : Fin n → Slot)
    (f : Assignment slots → Y) (P : Label slots f) :
    CanonicalKeyEncoding.partEnum n (transportLabel slots f P).val =
      CanonicalKeyEncoding.partEnum n P.val := rfl

theorem partIndex_coarsen (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (P : Label slots f) :
    CanonicalKeyEncoding.partEnum n (coarsen slots f p P).val =
      CanonicalKeyEncoding.partEnum n
        (coarsen (dummySlots (shape slots)) (transport slots f) p
          (transportLabel slots f P)).val :=
  congrArg (CanonicalKeyEncoding.partEnum n) (coarsen_val slots f p P)

@[simp] theorem labelIndex_transportLabel (side : Side) (slots : Fin n → Slot)
    (f : Assignment slots → Y) (P : Label slots f) :
    CanonicalLabelEncoding.labelIndex (key side slots f) P =
      CanonicalLabelEncoding.labelIndex
        (key side (dummySlots (shape slots)) (transport slots f)) (transportLabel slots f P) := rfl

end
end PerfectCompleteness.CanonicalCoarseningErasure

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_CanonicalDictionaryAppendMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CanonicalDictionaryAppendMachine


open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

variable {K Λ A : Type} [DecidableEq K]

abbrev State (A : Type) := BinaryNameCompare.State A
abbrev clean (ambient : A) : State A := BinaryNameCompare.clean ambient

theorem payload_frame (bits : List Bool) :
    payload bits ++ [false] = BinaryNameMachine.frame bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      simpa [payload, BinaryNameMachine.frame] using congrArg (fun tail => true :: bit :: tail) ih

def finish (destination : K) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1.1) (exitAt destination exit)

def emitLoop (source destination : K) (again : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.push destination (fun state => state.2.getD false)
        (.push destination (fun _ => true) (finish destination (some again))))
      (.push destination (fun _ => false) (finish destination exit)))

theorem update_source (source destination : K) (distinct : source ≠ destination)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt source destination base input output) source replacement =
      tapesAt source destination base replacement output := by
  funext k
  by_cases hs : k = source
  · subst k; simp [tapesAt, distinct]
  · by_cases hd : k = destination
    · subst k; simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hs, hd]

theorem update_destination (source destination : K)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt source destination base input output) destination replacement =
      tapesAt source destination base input replacement := by
  simp [tapesAt]

theorem emitStep_empty (source destination : K) (distinct : source ≠ destination)
    (again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLoop : program again = emitLoop source destination again exit)
    (base : K → List Bool) (output : List Bool) (ambient : A) :
    TM2.step program
      ⟨some again, clean ambient, tapesAt source destination base [] output⟩ =
      some ⟨exit, clean ambient, tapesAt source destination base [] (false :: output)⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atLoop]
  cases exit <;>
    simp [emitLoop, finish, exitAt, TM2.stepAux, clean, BinaryNameCompare.clean,
      distinct, update_source, update_destination]

theorem emitStep_cons (source destination : K) (distinct : source ≠ destination)
    (again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLoop : program again = emitLoop source destination again exit)
    (base : K → List Bool) (bit : Bool) (input output : List Bool) (ambient : A) :
    TM2.step program
      ⟨some again, clean ambient, tapesAt source destination base (bit :: input) output⟩ =
      some ⟨some again, clean ambient,
        tapesAt source destination base input (true :: bit :: output)⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atLoop]
  simp [emitLoop, finish, exitAt, TM2.stepAux, clean, BinaryNameCompare.clean,
    distinct, update_source, update_destination]

theorem emitTrace (source destination : K) (distinct : source ≠ destination)
    (again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLoop : program again = emitLoop source destination again exit)
    (base : K → List Bool) (input output : List Bool) (ambient : A) :
    (advance (TM2.step program))^[input.length + 1]
      (some ⟨some again, clean ambient, tapesAt source destination base input output⟩) =
      some ⟨exit, clean ambient,
        tapesAt source destination base [] (false :: (payload input.reverse ++ output))⟩ := by
  induction input generalizing output with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, advance_some,
        List.reverse_nil, payload, List.flatMap_nil, List.nil_append] using
        emitStep_empty source destination distinct again exit program atLoop base output ambient
  | cons bit input ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [emitStep_cons source destination distinct again exit program atLoop, ih]
      simp only [List.reverse_cons, payload, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.append_assoc, List.cons_append,
        List.nil_append]

def instruction (tape : Fin 5 → K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .copyOut => loopAt (tape 0) (tape 3) id false
      (labels .copyOut) (some (labels .copyBack))
  | .copyBack => MachineCopy.forkLoop (tape 3) (tape 0) (tape 2) false
      (labels .copyBack) (some (labels .save))
  | .save => loopAt (tape 1) (tape 4) id false
      (labels .save) (some (labels .seed))
  | .seed => .push (tape 1) (fun _ => false) (.goto fun _ => labels .emit)
  | .emit => emitLoop (tape 2) (tape 1) (labels .emit) (some (labels .restore))
  | .restore => loopAt (tape 4) (tape 1) id false (labels .restore) exit

theorem appendTrace (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction tape labels exit l)
    (base : K → List Bool) (bits dictionary : List Bool)
    (keyWord : base (tape 0) = bits.reverse)
    (dictionaryWord : base (tape 1) = dictionary)
    (copyEmpty : base (tape 2) = []) (scratchEmpty : base (tape 3) = [])
    (savedEmpty : base (tape 4) = []) (ambient : A) :
    (advance (TM2.step program))^[steps bits.length dictionary.length]
      (some ⟨some (labels .copyOut), clean ambient, base⟩) =
      some ⟨exit, clean ambient,
        Function.update base (tape 1) (dictionary ++ (false :: BinaryNameMachine.frame bits))⟩ := by
  have hd (i j : Fin 5) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  let copyBase := Function.update base (tape 2) bits.reverse
  let savedBase := tapesAt (tape 1) (tape 4) copyBase [] dictionary.reverse
  let seedBase := Function.update savedBase (tape 1) [false]
  let emittedBase := tapesAt (tape 2) (tape 1) seedBase []
    (false :: BinaryNameMachine.frame bits)
  have copyRun : (advance (TM2.step program))^[2 * (bits.length + 1)]
      (some ⟨some (labels .copyOut), clean ambient, base⟩) =
      some ⟨some (labels .save), clean ambient, copyBase⟩ := by
    have h := MachineCopy.copyTrace (tape 0) (tape 2) (tape 3)
      (hd 0 2 (by decide)) (hd 0 3 (by decide)) (hd 2 3 (by decide)) false
      (labels .copyOut) (labels .copyBack) (some (labels .save)) program
      (atLabels .copyOut) (atLabels .copyBack) base scratchEmpty
      (ambient, false, none) none
    simpa only [keyWord, copyEmpty, List.append_nil, List.length_reverse,
      clean, BinaryNameCompare.clean, copyBase] using h
  have copyDictionary : copyBase (tape 1) = dictionary := by
    simpa [copyBase, hd 1 2 (by decide)] using dictionaryWord
  have copySaved : copyBase (tape 4) = [] := by
    simpa [copyBase, hd 4 2 (by decide)] using savedEmpty
  have saveRun : (advance (TM2.step program))^[dictionary.length + 1]
      (some ⟨some (labels .save), clean ambient, copyBase⟩) =
      some ⟨some (labels .seed), clean ambient, savedBase⟩ := by
    have h := transferAt_fromTapes (Γ := Alphabet) (σ := A × Bool × Option Bool)
      (tape 1) (tape 4) (hd 1 4 (by decide)) id false (labels .save)
      (some (labels .seed)) program (atLabels .save) copyBase (ambient, false, none) none
    change (advance (TM2.step program))^[(copyBase (tape 1)).length + 1]
      (some ⟨some (labels .save), clean ambient, copyBase⟩) =
      some ⟨some (labels .seed), clean ambient, tapesAt (tape 1) (tape 4) copyBase []
        ((copyBase (tape 1)).reverse.map id ++ copyBase (tape 4))⟩ at h
    simpa only [copyDictionary, copySaved, List.map_id,
      List.append_nil, clean, BinaryNameCompare.clean, savedBase] using h
  have seedRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .seed), clean ambient, savedBase⟩) =
      some ⟨some (labels .emit), clean ambient, seedBase⟩ := by
    simp only [Function.iterate_one, advance_some]
    change some (TM2.stepAux (program (labels .seed)) _ _) = _
    rw [atLabels .seed]
    simp [instruction, TM2.stepAux, savedBase, tapesAt, seedBase, hd 1 4 (by decide)]
  have seedKey : seedBase (tape 2) = bits.reverse := by
    simp [seedBase, savedBase, tapesAt, copyBase, hd 2 1 (by decide), hd 2 4 (by decide)]
  have seedDictionary : seedBase (tape 1) = [false] := by simp [seedBase]
  have emitRun : (advance (TM2.step program))^[bits.length + 1]
      (some ⟨some (labels .emit), clean ambient, seedBase⟩) =
      some ⟨some (labels .restore), clean ambient, emittedBase⟩ := by
    have h := emitTrace (tape 2) (tape 1) (hd 2 1 (by decide))
      (labels .emit) (some (labels .restore)) program (atLabels .emit) seedBase
      (seedBase (tape 2)) (seedBase (tape 1)) ambient
    rw [tapesAt_self] at h
    simpa only [seedKey, seedDictionary, List.length_reverse, List.reverse_reverse,
      payload_frame, emittedBase] using h
  have emittedSaved : emittedBase (tape 4) = dictionary.reverse := by
    simp [emittedBase, seedBase, savedBase, tapesAt,
      hd 4 1 (by decide), hd 4 2 (by decide)]
  have emittedDictionary : emittedBase (tape 1) =
      false :: BinaryNameMachine.frame bits := by simp [emittedBase]
  have restored : tapesAt (tape 4) (tape 1) emittedBase []
      (dictionary ++ (false :: BinaryNameMachine.frame bits)) =
      Function.update base (tape 1) (dictionary ++ (false :: BinaryNameMachine.frame bits)) := by
    funext k
    by_cases h1 : k = tape 1
    · subst k; simp [tapesAt]
    · by_cases h2 : k = tape 2
      · subst k
        simp [tapesAt, emittedBase, hd 2 1 (by decide), hd 2 4 (by decide), copyEmpty]
      · by_cases h4 : k = tape 4
        · subst k
          simp [tapesAt, hd 4 1 (by decide), savedEmpty]
        · simp [tapesAt, emittedBase, seedBase, savedBase, copyBase, h1, h2, h4]
  have restoreRun : (advance (TM2.step program))^[dictionary.length + 1]
      (some ⟨some (labels .restore), clean ambient, emittedBase⟩) =
      some ⟨exit, clean ambient,
        Function.update base (tape 1) (dictionary ++ (false :: BinaryNameMachine.frame bits))⟩ := by
    have h := transferAt_fromTapes (Γ := Alphabet) (σ := A × Bool × Option Bool)
      (tape 4) (tape 1) (hd 4 1 (by decide)) id false (labels .restore) exit
      program (atLabels .restore) emittedBase (ambient, false, none) none
    change (advance (TM2.step program))^[(emittedBase (tape 4)).length + 1]
      (some ⟨some (labels .restore), clean ambient, emittedBase⟩) =
      some ⟨exit, clean ambient, tapesAt (tape 4) (tape 1) emittedBase []
        ((emittedBase (tape 4)).reverse.map id ++ emittedBase (tape 1))⟩ at h
    simpa only [emittedSaved, emittedDictionary, List.length_reverse,
      List.reverse_reverse, List.map_id, restored, clean, BinaryNameCompare.clean] using h
  have h := joinTrace (joinTrace (joinTrace (joinTrace copyRun saveRun) seedRun) emitRun) restoreRun
  have time : (((2 * (bits.length + 1) + (dictionary.length + 1)) + 1) +
      (bits.length + 1)) + (dictionary.length + 1) = steps bits.length dictionary.length := by
    unfold steps
    omega
  rw [time] at h
  exact h

end PerfectCompleteness.CanonicalDictionaryAppendMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_CanonicalDictionaryMachine
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryParsing.canonical_nat_bits _root_.OAI.PerfectCompleteness.BinaryRenameWords.tokens_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec.decodeWords_encodeWord _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter.counterTapes_counter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CanonicalDictionaryMachine


open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

abbrev Token := BinaryNameSearch.Token

def updatedTokens (tokens : List Token) (bits : List Bool) : List Token :=
  tokens ++ [(false, bits)]

theorem stream_append (first second : List Token) :
    BinaryNameSearch.stream (first ++ second) =
      BinaryNameSearch.stream first ++ BinaryNameSearch.stream second := by
  induction first with
  | nil => rfl
  | cons token first ih =>
      simp only [List.cons_append, BinaryNameSearch.stream_cons, ih, List.append_assoc]

theorem stream_updated (tokens : List Token) (bits : List Bool) :
    BinaryNameSearch.stream (updatedTokens tokens bits) =
      BinaryNameSearch.stream tokens ++ (false :: BinaryNameMachine.frame bits) := by
  simp only [updatedTokens, stream_append, BinaryNameSearch.stream_cons,
    BinaryNameSearch.stream_nil, List.append_nil, BinaryNameSearch.tokenBits]

theorem stream_updated_length (tokens : List Token) (bits : List Bool) :
    (BinaryNameSearch.stream (updatedTokens tokens bits)).length =
      (BinaryNameSearch.stream tokens).length + 2 * bits.length + 2 := by
  rw [stream_updated]
  simp only [List.length_append, List.length_cons, BinaryNameMachine.frame_length]
  omega

theorem present (tokens : List Token) (bits : List Bool) :
    bits ∈ BinaryNameSearch.payloads (updatedTokens tokens bits) := by
  apply List.mem_map.mpr
  exact ⟨(false, bits), by simp [updatedTokens], rfl⟩

theorem updated_canonical (tokens : List Token) (bits : List Bool)
    (canonical : BinaryNameMachine.canonical bits = true)
    (allCanonical : ∀ token ∈ tokens, BinaryNameMachine.canonical token.2 = true) :
    ∀ token ∈ updatedTokens tokens bits, BinaryNameMachine.canonical token.2 = true := by
  intro token mem
  rcases List.mem_append.mp mem with old | new
  · exact allCanonical token old
  · have same : token = (false, bits) := by simpa only [List.mem_singleton] using new
    simpa only [same] using canonical

def index (tokens : List Token) (bits : List Bool) : Nat :=
  (BinaryNameSearch.payloads (updatedTokens tokens bits)).idxOf bits

theorem index_le (tokens : List Token) (bits : List Bool) : index tokens bits ≤ tokens.length := by
  have h := List.idxOf_lt_length_of_mem (present tokens bits)
  simpa only [index, BinaryNameSearch.payloads, List.length_map, updatedTokens,
    List.length_append, List.length_singleton, Nat.lt_add_one_iff] using h

theorem suffix_length_le (tokens : List Token) (bits : List Bool) :
    (BinaryNameSearch.stream (BinaryNameSearch.afterMatch tokens bits)).length ≤
      (BinaryNameSearch.stream tokens).length := by
  induction tokens with
  | nil => simp [BinaryNameSearch.afterMatch]
  | cons token tokens ih =>
      simp only [BinaryNameSearch.afterMatch, BinaryNameSearch.stream_cons, List.length_append]
      split <;> omega

def steps (tokens : List Token) (bits : List Bool) : Nat :=
  CanonicalDictionaryAppendMachine.steps bits.length (BinaryNameSearch.stream tokens).length +
    2 * ((BinaryNameSearch.stream (updatedTokens tokens bits)).length + 1) + 1 +
    BinaryNameSearch.steps (updatedTokens tokens bits) bits +
    ((BinaryNameSearch.stream (BinaryNameSearch.afterMatch (updatedTokens tokens bits) bits)).length + 1) +
    (index tokens bits + 2)

theorem steps_le (tokens : List Token) (bits : List Bool) :
    steps tokens bits ≤ 3 * (BinaryNameSearch.stream (updatedTokens tokens bits)).length ^ 2 +
      16 * (BinaryNameSearch.stream (updatedTokens tokens bits)).length + 12 := by
  have search := BinaryNameSearch.steps_le_stream (updatedTokens tokens bits) bits
  have suffix := suffix_length_le (updatedTokens tokens bits) bits
  have idx := index_le tokens bits
  have oldCount : tokens.length ≤ (BinaryNameSearch.stream tokens).length := by
    rw [BinaryNameSearch.stream_length]
    omega
  have sizes := stream_updated_length tokens bits
  have keyBound : bits.length ≤ (BinaryNameSearch.stream (updatedTokens tokens bits)).length := by omega
  have product := Nat.mul_le_mul_right (BinaryNameSearch.stream (updatedTokens tokens bits)).length keyBound
  unfold steps CanonicalDictionaryAppendMachine.steps
  nlinarith

section Program

variable {K Λ A : Type} [DecidableEq K]

abbrev State (A : Type) := BinaryNameCompare.State A
abbrev clean (ambient : A) : State A := BinaryNameCompare.clean ambient

inductive Label
  | append (label : CanonicalDictionaryAppendMachine.Label)
  | copyOut
  | copyBack
  | seed
  | search (label : BinaryNameSearch.Label)
  | drain
  | emit
  deriving DecidableEq, Fintype

def main : Label := .append .copyOut

def instruction (tape : Fin 8 → K) (labels : Label → Λ) (done rejected : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .append l => CanonicalDictionaryAppendMachine.instruction (appendTapes tape)
      (fun l => labels (.append l)) (some (labels .copyOut)) l
  | .copyOut => loopAt (tape 1) (tape 5) id false (labels .copyOut) (some (labels .copyBack))
  | .copyBack => MachineCopy.forkLoop (tape 5) (tape 1) (tape 2) false
      (labels .copyBack) (some (labels .seed))
  | .seed => .push (tape 6) (fun _ => false) (.goto fun _ => labels (.search .sign))
  | .search l => BinaryNameSearch.instruction (searchTapes tape)
      (fun l => labels (.search l)) (some (labels .drain)) rejected rejected l
  | .drain => MachineDrain.drain (tape 2) (labels .drain) (some (labels .emit))
  | .emit => loopAt (tape 6) (tape 7) id false (labels .emit) done

theorem dictionaryTrace (tape : Fin 8 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (done rejected : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction tape labels done rejected l)
    (base : K → List Bool) (ambient : A) (tokens : List Token) (bits : List Bool)
    (canonical : BinaryNameMachine.canonical bits = true)
    (allCanonical : ∀ token ∈ tokens, BinaryNameMachine.canonical token.2 = true)
    (keyWord : base (tape 0) = bits.reverse)
    (dictionaryWord : base (tape 1) = BinaryNameSearch.stream tokens)
    (empty : ∀ i : Fin 8, 2 ≤ i.val → i.val ≤ 6 → base (tape i) = []) :
    (advance (TM2.step program))^[steps tokens bits]
      (some ⟨some (labels main), clean ambient, base⟩) =
      some ⟨done, clean ambient,
        Function.update (Function.update base (tape 1)
          (BinaryNameSearch.stream (updatedTokens tokens bits))) (tape 7)
          ((encodeWord (index tokens bits)).reverse ++ base (tape 7))⟩ := by
  have hd (i j : Fin 8) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have he (i : Fin 8) (lo : 2 ≤ i.val := by decide) (hi : i.val ≤ 6 := by decide) :
      base (tape i) = [] := empty i lo hi
  let updated := updatedTokens tokens bits
  let dictionary := BinaryNameSearch.stream updated
  let tail := BinaryNameSearch.stream (BinaryNameSearch.afterMatch updated bits)
  let s₁ := Function.update base (tape 1) dictionary
  let s₂ := Function.update s₁ (tape 2) dictionary
  let s₃ := Function.update s₂ (tape 6) [false]
  let s₄ := tapesAt (tape 2) (tape 6) s₃ tail (encodeWord (index tokens bits))
  let s₅ := Function.update s₄ (tape 2) []
  let s₆ := tapesAt (tape 6) (tape 7) s₅ []
    ((encodeWord (index tokens bits)).reverse ++ s₅ (tape 7))
  have appended := CanonicalDictionaryAppendMachine.appendTrace (appendTapes tape)
    (appendTapes_injective tape distinct) (fun l => labels (.append l))
    (some (labels .copyOut)) program (fun l => atLabels (.append l))
    base bits (BinaryNameSearch.stream tokens) keyWord dictionaryWord
    (he 4) (he 5) (he 2) ambient
  rw [← stream_updated tokens bits] at appended
  change (advance (TM2.step program))^[CanonicalDictionaryAppendMachine.steps
      bits.length (BinaryNameSearch.stream tokens).length]
    (some ⟨some (labels main), clean ambient, base⟩) =
    some ⟨some (labels .copyOut), clean ambient, s₁⟩ at appended
  have s₁dictionary : s₁ (tape 1) = dictionary := by simp [s₁]
  have s₁empty (i : Fin 8) (lo : 2 ≤ i.val) (hi : i.val ≤ 6) : s₁ (tape i) = [] := by
    have ne : i ≠ 1 := by intro h; subst i; omega
    simp [s₁, hd i 1 ne, he i lo hi]
  have copied : (advance (TM2.step program))^[2 * (dictionary.length + 1)]
      (some ⟨some (labels .copyOut), clean ambient, s₁⟩) =
      some ⟨some (labels .seed), clean ambient, s₂⟩ := by
    have h := MachineCopy.copyTrace (tape 1) (tape 2) (tape 5)
      (hd 1 2 (by decide)) (hd 1 5 (by decide)) (hd 2 5 (by decide)) false
      (labels .copyOut) (labels .copyBack) (some (labels .seed)) program
      (atLabels .copyOut) (atLabels .copyBack) s₁ (s₁empty 5 (by decide) (by decide))
      (ambient, false, none) none
    simpa only [s₁dictionary, s₁empty 2 (by decide) (by decide), List.append_nil,
      clean, BinaryNameCompare.clean, s₂] using h
  have s₂counter : s₂ (tape 6) = [] := by
    simp [s₂, hd 6 2 (by decide), s₁empty 6 (by decide) (by decide)]
  have seeded : (advance (TM2.step program))^[1]
      (some ⟨some (labels .seed), clean ambient, s₂⟩) =
      some ⟨some (labels (.search .sign)), clean ambient, s₃⟩ := by
    change some (TM2.stepAux (program (labels .seed)) _ _) = _
    rw [atLabels .seed]
    simp [instruction, TM2.stepAux, s₂counter, s₃]
  have s₃key : s₃ (tape 0) = bits.reverse := by
    simpa [s₃, s₂, s₁, hd 0 6 (by decide), hd 0 2 (by decide), hd 0 1 (by decide)] using keyWord
  have s₃stream : s₃ (tape 2) = dictionary := by simp [s₃, s₂, hd 2 6 (by decide)]
  have s₃counter : s₃ (tape 6) = [false] := by simp [s₃]
  have s₃empty (i : Fin 8) (hi : i = 3 ∨ i = 4 ∨ i = 5) : s₃ (tape i) = [] := by
    rcases hi with rfl | rfl | rfl <;> simp [s₃, s₂, s₁, hd, he]
  have searched : (advance (TM2.step program))^[BinaryNameSearch.steps updated bits]
      (some ⟨some (labels (.search .sign)), clean ambient, s₃⟩) =
      some ⟨some (labels .drain), clean ambient, s₄⟩ := by
    have h := BinaryNameSearch.searchTrace (searchTapes tape) (searchTapes_injective tape distinct)
      (fun l => labels (.search l)) (some (labels .drain)) rejected rejected program
      (fun l => atLabels (.search l)) s₃ ambient updated bits [] [false]
      (updated_canonical tokens bits canonical allCanonical) (present tokens bits) s₃key
      (s₃empty 3 (by simp)) (s₃empty 4 (by simp)) (s₃empty 5 (by simp))
    have initial : tapesAt (tape 2) (tape 6) s₃ dictionary [false] = s₃ := by
      rw [← s₃stream, ← s₃counter]
      exact tapesAt_self _ _ _
    change (advance (TM2.step program))^[BinaryNameSearch.steps updated bits]
      (some ⟨some (labels (.search .sign)), clean ambient,
        tapesAt (tape 2) (tape 6) s₃ (dictionary ++ []) [false]⟩) =
      some ⟨some (labels .drain), clean ambient,
        tapesAt (tape 2) (tape 6) s₃ (tail ++ []) (encodeWord (index tokens bits))⟩ at h
    simpa only [List.append_nil, initial, s₄] using h
  have s₄stream : s₄ (tape 2) = tail := by simp [s₄, hd 2 6 (by decide)]
  have drained : (advance (TM2.step program))^[tail.length + 1]
      (some ⟨some (labels .drain), clean ambient, s₄⟩) =
      some ⟨some (labels .emit), clean ambient, s₅⟩ := by
    have h := MachineDrain.drainTrace (tape 2) (labels .drain) (some (labels .emit)) program
      (atLabels .drain) s₄ tail (ambient, false, none) none
    have initial : Function.update s₄ (tape 2) tail = s₄ := by
      rw [← s₄stream]
      exact Function.update_eq_self _ _
    simpa only [initial, clean, BinaryNameCompare.clean, s₅] using h
  have s₅counter : s₅ (tape 6) = encodeWord (index tokens bits) := by
    simp [s₅, s₄, hd 6 2 (by decide)]
  have emitted : (advance (TM2.step program))^[index tokens bits + 2]
      (some ⟨some (labels .emit), clean ambient, s₅⟩) =
      some ⟨done, clean ambient, s₆⟩ := by
    have h := transferAt_fromTapes (Γ := Alphabet) (σ := A × Bool × Option Bool)
      (tape 6) (tape 7) (hd 6 7 (by decide)) id false (labels .emit) done program
      (atLabels .emit) s₅ (ambient, false, none) none
    change (advance (TM2.step program))^[(s₅ (tape 6)).length + 1]
      (some ⟨some (labels .emit), clean ambient, s₅⟩) =
      some ⟨done, clean ambient, tapesAt (tape 6) (tape 7) s₅ []
        ((s₅ (tape 6)).reverse.map id ++ s₅ (tape 7))⟩ at h
    simpa only [s₅counter, encodeWord_length, List.map_id_fun, id_eq, Nat.add_assoc,
      clean, BinaryNameCompare.clean, s₆] using h
  have restored : s₆ = Function.update (Function.update base (tape 1) dictionary) (tape 7)
      ((encodeWord (index tokens bits)).reverse ++ base (tape 7)) := by
    funext k
    by_cases h7 : k = tape 7
    · subst k
      simp [s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, hd]
    · by_cases h1 : k = tape 1
      · subst k
        simp [s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, hd]
      · by_cases h2 : k = tape 2
        · subst k
          simp [s₆, s₅, tapesAt, hd, he 2]
        · by_cases h6 : k = tape 6
          · subst k
            simp [s₆, tapesAt, hd, he 6]
          · simp [s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, h7, h1, h2, h6,
              Function.update_apply]
  have full := joinTrace (joinTrace (joinTrace (joinTrace
    (joinTrace appended copied) seeded) searched) drained) emitted
  simpa only [steps, dictionary, updated, tail, restored] using full

end Program

end PerfectCompleteness.CanonicalDictionaryMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_CanonicalVertexNames
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryParsing.canonical_nat_bits _root_.OAI.PerfectCompleteness.BinaryRenameWords.tokens_length _root_.OAI.PerfectCompleteness.CanonicalLabelEncoding.labelEmbedding_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CanonicalVertexNames

open CanonicalKeys
open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

noncomputable section

variable {n : Nat}

def payload (key : Key n) : List Bool := CanonicalKeyEncoding.bits key ++ [true]

theorem payload_injective (n : Nat) : Function.Injective (payload (n := n)) := by
  intro a b h
  exact CanonicalKeyEncoding.bits_injective n (List.append_cancel_right h)

theorem finalDigit_append_true (bits : List Bool) (previous : Option Bool) :
    BinaryNameMachine.finalDigit (bits ++ [true]) previous = some true := by
  induction bits generalizing previous with
  | nil => rfl
  | cons bit bits ih => exact ih (some bit)

@[simp] theorem payload_canonical (key : Key n) :
    BinaryNameMachine.canonical (payload key) = true := by
  simp [payload, BinaryNameMachine.canonical, finalDigit_append_true]

@[simp] theorem payload_length (key : Key n) :
    (payload key).length = (CanonicalKeyEncoding.bits key).length + 1 := by
  simp only [payload, List.length_append, List.length_cons, List.length_nil]

def tokens (keys : List (Key n)) : List BinaryNameSearch.Token :=
  keys.map (fun key => (false, payload key))

@[simp] theorem tokens_length (keys : List (Key n)) :
    (tokens keys).length = keys.length := by
  simp only [tokens, List.length_map]

@[simp] theorem tokens_payloads (keys : List (Key n)) :
    BinaryNameSearch.payloads (tokens keys) = keys.map payload := by
  simp only [BinaryNameSearch.payloads, tokens, List.map_map, Function.comp_def]

theorem payload_mem (keys : List (Key n)) (key : Key n) (hmem : key ∈ keys) :
    payload key ∈ BinaryNameSearch.payloads (tokens keys) := by
  rw [tokens_payloads]
  exact List.mem_map.mpr ⟨key, hmem, rfl⟩

theorem tokens_canonical (keys : List (Key n)) :
    ∀ token ∈ tokens keys, BinaryNameMachine.canonical token.2 = true := by
  intro token htoken
  obtain ⟨key, _, rfl⟩ := List.mem_map.mp htoken
  exact payload_canonical key

def name (keys : List (Key n)) (key : Key n) (hmem : key ∈ keys) : Fin keys.length :=
  ⟨(BinaryNameSearch.payloads (tokens keys)).idxOf (payload key), by
    have h := List.idxOf_lt_length_of_mem (payload_mem keys key hmem)
    simpa only [tokens_payloads, List.length_map] using h⟩

@[simp] theorem name_val (keys : List (Key n)) (key : Key n) (hmem : key ∈ keys) :
    (name keys key hmem).val =
      (BinaryNameSearch.payloads (tokens keys)).idxOf (payload key) := rfl

theorem name_eq_iff (keys : List (Key n)) (a b : Key n)
    (ha : a ∈ keys) (hb : b ∈ keys) : name keys a ha = name keys b hb ↔ a = b := by
  constructor
  · intro h
    have hidx := congrArg Fin.val h
    exact payload_injective n ((List.idxOf_inj (payload_mem keys a ha)).mp hidx)
  · intro h
    subst b
    rfl

theorem payload_length_le (key : Key n) (bound : Nat)
    (hretained : key.retained.length ≤ n)
    (hIDs : ∀ entry ∈ key.retained, KeyMetadataEncoding.entryID entry.2 ≤ bound) :
    (payload key).length ≤ payloadBound n bound := by
  rw [payload_length]
  unfold payloadBound
  apply Nat.add_le_add_right
  apply (CanonicalKeyEncoding.bits_length_le key bound hIDs).trans
  apply Nat.mul_le_mul_right
  rw [CanonicalKeyEncoding.partitionWidth_eq]
  omega

theorem payloadSize_le (keys : List (Key n)) (B : Nat)
    (hbound : ∀ key ∈ keys, (payload key).length ≤ B) :
    BinaryNameSearch.payloadSize (tokens keys) ≤ B * keys.length := by
  revert hbound
  induction keys with
  | nil =>
      intro _
      exact Nat.le_refl 0
  | cons key keys ih =>
      intro hbound
      have hhead := hbound key (by simp)
      have htail := ih (fun k hk => hbound k (List.mem_cons_of_mem key hk))
      change (payload key).length + BinaryNameSearch.payloadSize (tokens keys) ≤
        B * (keys.length + 1)
      apply (Nat.add_le_add hhead htail).trans_eq
      rw [Nat.mul_add, Nat.mul_one]
      exact Nat.add_comm _ _

theorem stream_length_le (keys : List (Key n)) (bound : Nat)
    (hretained : ∀ key ∈ keys, key.retained.length ≤ n)
    (hIDs : ∀ key ∈ keys, ∀ entry ∈ key.retained,
      KeyMetadataEncoding.entryID entry.2 ≤ bound) :
    (BinaryNameSearch.stream (tokens keys)).length ≤
      (2 * payloadBound n bound + 2) * keys.length := by
  have hsize := payloadSize_le keys (payloadBound n bound)
    (fun key hk => payload_length_le key bound (hretained key hk) (hIDs key hk))
  rw [BinaryNameSearch.stream_length, tokens_length]
  calc
    _ ≤ 2 * (payloadBound n bound * keys.length) + 2 * keys.length :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 2 hsize) _
    _ = _ := by rw [Nat.add_mul, Nat.mul_assoc]


end
end PerfectCompleteness.CanonicalVertexNames

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_CanonicalKeyShapeMachineLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalLabelEncoding.labelEmbedding_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CanonicalKeyShapeMachine

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open CanonicalKeyShape CanonicalKeyEncoding CanonicalKeys

noncomputable section

def recoverKey {n k : Nat} (side : Side) (slots : Fin n → MixedSupport.Slot)
    (data : Input n k) : Key n :=
  ⟨side, CanonicalKeyShape.retained slots (inputModes data), inputPartition data⟩

theorem recoverKey_input {n k : Nat} (side : Side) (slots : Fin n → MixedSupport.Slot)
    (f : MixedSupport.Assignment slots → Fin k) :
    recoverKey side slots (CanonicalKeyShape.input slots f) = CanonicalKeys.key side slots f := by
  simp only [recoverKey, CanonicalKeys.key, inputModes_recover, inputPartition_eq]

end
end PerfectCompleteness.CanonicalKeyShapeMachine


namespace PerfectCompleteness.CanonicalOnlineNames

open CanonicalKeys

section Lists

variable {α : Type*} [BEq α] [LawfulBEq α]

theorem firstIndex_le_prefix (earlier : List α) (key : α) :
    (earlier ++ [key]).idxOf key ≤ earlier.length := by
  have found := List.idxOf_lt_length_of_mem (by simp : key ∈ earlier ++ [key])
  simp only [List.length_append, List.length_singleton] at found
  omega

end Lists

noncomputable section

variable {n : Nat}

def onlineID (earlier : List (Key n)) (key : Key n) : Nat :=
  (BinaryNameSearch.payloads (CanonicalVertexNames.tokens (earlier ++ [key]))).idxOf
    (CanonicalVertexNames.payload key)

theorem tokens_append_current (earlier : List (Key n)) (key : Key n) :
    CanonicalVertexNames.tokens (earlier ++ [key]) =
      CanonicalVertexNames.tokens earlier ++ [(false, CanonicalVertexNames.payload key)] := by
  simp only [CanonicalVertexNames.tokens, List.map_append, List.map_cons, List.map_nil]

theorem onlineID_le_prefix (earlier : List (Key n)) (key : Key n) :
    onlineID earlier key ≤ earlier.length := by
  have bound := firstIndex_le_prefix (earlier.map CanonicalVertexNames.payload)
    (CanonicalVertexNames.payload key)
  simpa only [onlineID, CanonicalVertexNames.tokens_payloads, List.map_append,
    List.map_cons, List.map_nil, List.length_map] using bound

theorem onlineID_eq_global (earlier suffix : List (Key n)) (key : Key n) :
    onlineID earlier key =
      (BinaryNameSearch.payloads
        (CanonicalVertexNames.tokens (earlier ++ key :: suffix))).idxOf
          (CanonicalVertexNames.payload key) := by
  simpa only [onlineID, CanonicalVertexNames.tokens_payloads, List.map_append,
    List.map_cons, List.map_nil] using
      firstIndex_append_current (earlier.map CanonicalVertexNames.payload)
        (suffix.map CanonicalVertexNames.payload) (CanonicalVertexNames.payload key)

def onlineName (earlier : List (Key n)) (key : Key n) : Fin (earlier.length + 1) :=
  ⟨onlineID earlier key, by have := onlineID_le_prefix earlier key; omega⟩

@[simp] theorem onlineName_val (earlier : List (Key n)) (key : Key n) :
    (onlineName earlier key).val = onlineID earlier key := rfl

end
end PerfectCompleteness.CanonicalOnlineNames

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_CanonicalDictionaryNames
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CanonicalDictionaryNames

open CanonicalKeys Turing
open UniqueGamesTheorem.Foundations.Complexity MachineComposition

noncomputable section

variable {n : Nat}

theorem updatedTokens_eq (earlier : List (Key n)) (key : Key n) :
    CanonicalDictionaryMachine.updatedTokens (CanonicalVertexNames.tokens earlier)
      (CanonicalVertexNames.payload key) =
        CanonicalVertexNames.tokens (earlier ++ [key]) :=
  (CanonicalOnlineNames.tokens_append_current earlier key).symm

theorem index_eq_onlineID (earlier : List (Key n)) (key : Key n) :
    CanonicalDictionaryMachine.index (CanonicalVertexNames.tokens earlier)
      (CanonicalVertexNames.payload key) = CanonicalOnlineNames.onlineID earlier key := by
  unfold CanonicalDictionaryMachine.index CanonicalOnlineNames.onlineID
  rw [updatedTokens_eq]

def steps (earlier : List (Key n)) (key : Key n) : Nat :=
  CanonicalDictionaryMachine.steps (CanonicalVertexNames.tokens earlier)
    (CanonicalVertexNames.payload key)

theorem steps_le (earlier : List (Key n)) (key : Key n) :
    steps earlier key ≤
      3 * (BinaryNameSearch.stream (CanonicalVertexNames.tokens (earlier ++ [key]))).length ^ 2 +
      16 * (BinaryNameSearch.stream (CanonicalVertexNames.tokens (earlier ++ [key]))).length +
      12 := by
  simpa only [steps, updatedTokens_eq] using
    CanonicalDictionaryMachine.steps_le (CanonicalVertexNames.tokens earlier)
      (CanonicalVertexNames.payload key)


variable {K Λ A : Type} [DecidableEq K]

theorem dictionaryTrace (tape : Fin 8 → K) (distinct : Function.Injective tape)
    (labels : CanonicalDictionaryMachine.Label → Λ) (done rejected : Option Λ)
    (program : Λ → TM2.Stmt (CanonicalDictionaryMachine.Alphabet (K := K)) Λ
      (CanonicalDictionaryMachine.State A))
    (atLabels : ∀ l, program (labels l) =
      CanonicalDictionaryMachine.instruction tape labels done rejected l)
    (base : K → List Bool) (ambient : A) (earlier : List (Key n)) (key : Key n)
    (keyWord : base (tape 0) = (CanonicalVertexNames.payload key).reverse)
    (dictionaryWord : base (tape 1) =
      BinaryNameSearch.stream (CanonicalVertexNames.tokens earlier))
    (empty : ∀ i : Fin 8, 2 ≤ i.val → i.val ≤ 6 → base (tape i) = []) :
    (advance (TM2.step program))^[steps earlier key]
      (some ⟨some (labels CanonicalDictionaryMachine.main),
        CanonicalDictionaryMachine.clean ambient, base⟩) =
      some ⟨done, CanonicalDictionaryMachine.clean ambient,
        Function.update (Function.update base (tape 1)
          (BinaryNameSearch.stream (CanonicalVertexNames.tokens (earlier ++ [key])))) (tape 7)
          ((encodeWord (CanonicalOnlineNames.onlineID earlier key)).reverse ++ base (tape 7))⟩ := by
  simpa only [steps, updatedTokens_eq, index_eq_onlineID] using
    CanonicalDictionaryMachine.dictionaryTrace tape distinct labels done rejected program
      atLabels base ambient (CanonicalVertexNames.tokens earlier) (CanonicalVertexNames.payload key)
      (CanonicalVertexNames.payload_canonical key) (CanonicalVertexNames.tokens_canonical earlier)
      keyWord dictionaryWord empty

def dictionaryInTime (tape : Fin 8 → K) (distinct : Function.Injective tape)
    (labels : CanonicalDictionaryMachine.Label → Λ) (done rejected : Option Λ)
    (program : Λ → TM2.Stmt (CanonicalDictionaryMachine.Alphabet (K := K)) Λ
      (CanonicalDictionaryMachine.State A))
    (atLabels : ∀ l, program (labels l) =
      CanonicalDictionaryMachine.instruction tape labels done rejected l)
    (base : K → List Bool) (ambient : A) (earlier : List (Key n)) (key : Key n)
    (keyWord : base (tape 0) = (CanonicalVertexNames.payload key).reverse)
    (dictionaryWord : base (tape 1) =
      BinaryNameSearch.stream (CanonicalVertexNames.tokens earlier))
    (empty : ∀ i : Fin 8, 2 ≤ i.val → i.val ≤ 6 → base (tape i) = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels CanonicalDictionaryMachine.main), CanonicalDictionaryMachine.clean ambient,
        base⟩
      (some ⟨done, CanonicalDictionaryMachine.clean ambient,
        Function.update (Function.update base (tape 1)
          (BinaryNameSearch.stream (CanonicalVertexNames.tokens (earlier ++ [key])))) (tape 7)
          ((encodeWord (CanonicalOnlineNames.onlineID earlier key)).reverse ++ base (tape 7))⟩)
      (3 * (BinaryNameSearch.stream (CanonicalVertexNames.tokens (earlier ++ [key]))).length ^ 2 +
        16 * (BinaryNameSearch.stream (CanonicalVertexNames.tokens (earlier ++ [key]))).length +
        12) where
  steps := steps earlier key
  evals_in_steps := dictionaryTrace tape distinct labels done rejected program atLabels
    base ambient earlier key keyWord dictionaryWord empty
  steps_le_m := steps_le earlier key

end
end PerfectCompleteness.CanonicalDictionaryNames

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_PreliminaryAveraging
attribute [-instance] _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.PreliminaryAveraging

open PreliminarySampler TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {v m n t : Nat} {branch rows repeats : Nat → Nat}

def directionLaw (leaf : RecursiveSpaces.Slots branch n) (level : Fin n)
    (hrows : ∀ k, 0 < rows (k + 1)) :
    FiniteDistribution (BucketSampler.Direction
      (rows (Nodes.height (GeometricPath.nodeAtLevel leaf level)))) := by
  letI : Nonempty (BucketSampler.Direction
      (rows (Nodes.height (GeometricPath.nodeAtLevel leaf level)))) :=
    directionNonempty _ (by rw [GeometricPath.nodeAtLevel_height]; exact hrows level.val)
  exact FiniteDistribution.uniform _

end
end PerfectCompleteness.PreliminaryAveraging

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_CandidateCoupling
attribute [-instance] _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CandidateCoupling

open PreliminarySampler PreliminaryAveraging TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {v m n t : Nat} {branch rows repeats : Nat → Nat}

abbrev DirectionTuple (rows : Nat → Nat) (leaf : RecursiveSpaces.Slots branch n) :=
  (level : Fin n) → BucketSampler.Direction
    (rows (Nodes.height (GeometricPath.nodeAtLevel leaf level)))

def directionsLaw (leaf : RecursiveSpaces.Slots branch n)
    (hrows : ∀ k, 0 < rows (k + 1)) : FiniteDistribution (DirectionTuple rows leaf) :=
  FiniteProduct.law (fun level => directionLaw leaf level hrows)

def candidateFraction (leaf : RecursiveSpaces.Slots branch n)
    (event : Choice rows leaf → Bool) (directions : DirectionTuple rows leaf) : ℝ :=
  (∑ level : Fin n, if event ⟨level, directions level⟩ then 1 else 0) / (n : ℝ)

abbrev Shared (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows : Nat → Nat) :=
  (b : Base branch n t m) ×
    (Arrays (sourceSlots clauses (endpoints b.1)) rows × DirectionTuple rows b.2)

def conditionalSharedLaw (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hrows : ∀ k, 0 < rows (k + 1))
    (b : Base branch n t m) :
    FiniteDistribution
      (Arrays (sourceSlots clauses (endpoints b.1)) rows × DirectionTuple rows b.2) :=
  (WholeArraySampler.law rows repeats (GeometricPath.leafPath b.2)
    (sourceSlots clauses (endpoints b.1))).product (directionsLaw b.2 hrows)

def sharedLaw [NeZero m] (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hbranch : ∀ k < n, 0 < branch k)
    (hrows : ∀ k, 0 < rows (k + 1)) :
    FiniteDistribution (Shared clauses branch n t rows) :=
  CompletionSoundness.sigmaLaw (baseLaw hbranch)
    (conditionalSharedLaw clauses rows repeats hrows)

end
end PerfectCompleteness.CandidateCoupling

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_PrefixTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.PrefixTests

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n cutoff : Nat}

abbrev LevelDirection (rows : Nat → Nat) (level : Fin n) :=
  BucketSampler.Direction (rows (level.val + 1))

abbrev LevelNode (branch : Nat → Nat) {n : Nat} (level : Fin n) :=
  {node : Nodes branch n // Nodes.height node = level.val + 1}

def levelNode (leaf : Slots branch n) (level : Fin n) : LevelNode branch level :=
  ⟨GeometricPath.nodeAtLevel leaf level, GeometricPath.nodeAtLevel_height leaf level⟩

def nodeDirection (rows : Nat → Nat) (level : Fin n) (node : LevelNode branch level)
    (direction : LevelDirection rows level) :
    BucketSampler.Direction (rows (Nodes.height node.val)) :=
  (Equiv.cast (congrArg (fun height => BucketSampler.Direction (rows height)) node.property)).symm
    direction

def choiceAt (rows : Nat → Nat) (leaf : Slots branch n) (level : Fin n)
    (direction : LevelDirection rows level) : PreliminarySampler.Choice rows leaf :=
  ⟨level, nodeDirection rows level (levelNode leaf level) direction⟩

end
end PerfectCompleteness.PrefixTests

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_CanonicalDirections
attribute [-simp] _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CanonicalDirections

open RecursiveSpaces HierarchicalArrays PreliminarySampler
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n : Nat}

abbrev Tuple (rows : Nat → Nat) (n : Nat) :=
  (level : Fin n) → PrefixTests.LevelDirection rows level

def directionEquiv (rows : Nat → Nat) (leaf : Slots branch n) (level : Fin n) :
    PrefixTests.LevelDirection rows level ≃
      BucketSampler.Direction (rows (Nodes.height (GeometricPath.nodeAtLevel leaf level))) :=
  (Equiv.cast (congrArg (fun height => BucketSampler.Direction (rows height))
    (GeometricPath.nodeAtLevel_height leaf level))).symm

def tupleEquiv (rows : Nat → Nat) (leaf : Slots branch n) :
    Tuple rows n ≃ CandidateCoupling.DirectionTuple rows leaf :=
  Equiv.piCongrRight (directionEquiv rows leaf)

@[simp] theorem tupleEquiv_apply (rows : Nat → Nat) (leaf : Slots branch n)
    (directions : Tuple rows n) (level : Fin n) :
    tupleEquiv rows leaf directions level = directionEquiv rows leaf level (directions level) := rfl

@[simp] theorem tupleEquiv_symm_apply (rows : Nat → Nat) (leaf : Slots branch n)
    (directions : CandidateCoupling.DirectionTuple rows leaf) (level : Fin n) :
    (tupleEquiv rows leaf).symm directions level =
      (directionEquiv rows leaf level).symm (directions level) := rfl

def levelLaw (rows : Nat → Nat) (hrows : ∀ k, 0 < rows (k + 1)) (level : Fin n) :
    FiniteDistribution (PrefixTests.LevelDirection rows level) := by
  letI := directionNonempty (rows (level.val + 1)) (hrows level.val)
  exact FiniteDistribution.uniform _

def law (rows : Nat → Nat) (n : Nat) (hrows : ∀ k, 0 < rows (k + 1)) :
    FiniteDistribution (Tuple rows n) :=
  FiniteProduct.law (levelLaw rows hrows)

@[simp] theorem choiceAt_toCanonical (rows : Nat → Nat) (leaf : Slots branch n)
    (directions : CandidateCoupling.DirectionTuple rows leaf) (level : Fin n) :
    PrefixTests.choiceAt rows leaf level ((tupleEquiv rows leaf).symm directions level) =
      (⟨level, directions level⟩ : Choice rows leaf) := by
  change (⟨level, directionEquiv rows leaf level
    ((directionEquiv rows leaf level).symm (directions level))⟩ : Choice rows leaf) = _
  rw [Equiv.apply_symm_apply]

end
end PerfectCompleteness.CanonicalDirections

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_CanonicalPartialTable
attribute [-instance] _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.FlexibleLocalCompletion.localLegalEquiv_apply_val _root_.OAI.PerfectCompleteness.HierarchicalArrays.joint_component _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.LocalCompletionGame.localLegalEquiv_apply_val _root_.OAI.PerfectCompleteness.NodeEmbedding.embed_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.embeddedRows_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.equiv_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.matrix_evaluate _root_.OAI.PerfectCompleteness.NodeEmbedding.rowsEquiv_apply _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.TreeCanonical.assignmentEquiv_apply _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_selected _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CanonicalPartialTable

open MixedSupport CanonicalKeys CanonicalKeyShape CanonicalEdges CanonicalLabelEncoding
open scoped Classical

noncomputable section

abbrev Input (n k l : Nat) :=
  Σ shapes : Fin n → Shape,
    (Assignment (dummySlots shapes) → Fin k) × (Fin k → Fin l)

instance inputFintype (n k l : Nat) : Fintype (Input n k l) := by
  unfold Input
  infer_instance

variable {n k l q : Nat}

def slots (data : Input n k l) : Fin n → Slot := dummySlots data.1

def joint (data : Input n k l) : Assignment (slots data) → Fin k := data.2.1

def outputMap (data : Input n k l) : Fin k → Fin l := data.2.2

def leftKey (data : Input n k l) : Key n := key .left (slots data) (joint data)

def rightKey (data : Input n k l) : Key n :=
  key .right (slots data) (outputMap data ∘ joint data)

theorem left_large (large : CanonicalKeyEncoding.partitionWidth n ≤ q) :
    CanonicalKeyEncoding.partitionWidth n ≤ 2 * q := by omega

def leftEmbedding (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (data : Input n k l) : Label (slots data) (joint data) ↪ Fin (2 * q) :=
  labelEmbedding (leftKey data) (left_large large)

def rightEmbedding (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (data : Input n k l) : Label (slots data) (outputMap data ∘ joint data) ↪ Fin q :=
  labelEmbedding (rightKey data) large

def image (hq : 0 < q) (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (data : Input n k l) (a : Fin (2 * q)) : Fin q :=
  if h : a ∈ Set.range (leftEmbedding large data) then
    rightEmbedding large data
      (coarsen (slots data) (joint data) (outputMap data) h.choose)
  else ⟨0, hq⟩

def lookup (hq : 0 < q) (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (data : Input n k l) : LocalCompletionFamily.Input q :=
  (paddedMask (leftKey data), image hq large data)

@[simp] theorem lookup_mask (hq : 0 < q)
    (large : CanonicalKeyEncoding.partitionWidth n ≤ q) (data : Input n k l) :
    (lookup hq large data).1 = paddedMask (leftKey data) := rfl

theorem mask_true (hq : 0 < q) (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (data : Input n k l) (a : Fin (2 * q)) :
    (lookup hq large data).1 a = true ↔ a ∈ Set.range (leftEmbedding large data) :=
  paddedMask_eq_true_iff (leftKey data) (left_large large) a

theorem image_legal (hq : 0 < q) (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (data : Input n k l) (P : Label (slots data) (joint data)) :
    (lookup hq large data).2 (leftEmbedding large data P) =
      rightEmbedding large data (coarsen (slots data) (joint data) (outputMap data) P) := by
  have h : leftEmbedding large data P ∈ Set.range (leftEmbedding large data) := ⟨P, rfl⟩
  have hchosen : h.choose = P := (leftEmbedding large data).injective h.choose_spec
  change image hq large data (leftEmbedding large data P) = _
  rw [image, dite_eq_left h, hchosen]

def legalEquiv (hq : 0 < q) (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (data : Input n k l) :
    Label (slots data) (joint data) ≃ LocalCompletionFamily.Legal (lookup hq large data) where
  toFun P := ⟨leftEmbedding large data P,
    (mask_true hq large data _).2 ⟨P, rfl⟩⟩
  invFun a := ((mask_true hq large data a.val).1 a.property).choose
  left_inv P := (leftEmbedding large data).injective
    ((mask_true hq large data _).1
      ((mask_true hq large data _).2 ⟨P, rfl⟩)).choose_spec
  right_inv a := Subtype.ext ((mask_true hq large data a.val).1 a.property).choose_spec

@[simp] theorem legalEquiv_val (hq : 0 < q)
    (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (data : Input n k l) (P : Label (slots data) (joint data)) :
    (legalEquiv hq large data P).val = leftEmbedding large data P := rfl

theorem admissible (hq : 0 < q) (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (data : Input n k l)
    (hsmall : ∀ Q, Nat.card {P : Label (slots data) (joint data) //
      coarsen (slots data) (joint data) (outputMap data) P = Q} ≤ 2) :
    LocalCompletionFamily.Admissible (lookup hq large data) := by
  let : Fintype (Label (slots data) (joint data)) := Fintype.ofFinite _
  intro b
  let fibers :
      {P : Label (slots data) (joint data) // rightEmbedding large data
        (coarsen (slots data) (joint data) (outputMap data) P) = b} ≃
      {a : LocalCompletionFamily.Legal (lookup hq large data) //
        (lookup hq large data).2 a.val = b} :=
    (legalEquiv hq large data).subtypeEquiv (fun P => by
      rw [legalEquiv_val, image_legal])
  have hcard := Nat.card_congr fibers
  have hbound := CompletionSoundness.LegalProjectionGame.embedded_fiber_le_two
    (rightEmbedding large data) (coarsen (slots data) (joint data) (outputMap data))
    (by intro Q; simpa only [← Nat.card_eq_fintype_card] using hsmall Q) b
  simp only [← Nat.card_eq_fintype_card] at hcard hbound ⊢
  exact hcard.symm.le.trans hbound

theorem admissible_of_output_fibers (hq : 0 < q)
    (large : CanonicalKeyEncoding.partitionWidth n ≤ q) (data : Input n k l)
    (hsmall : ∀ b, Nat.card {a : Fin k // outputMap data a = b} ≤ 2) :
    LocalCompletionFamily.Admissible (lookup hq large data) :=
  admissible hq large data
    (coarsen_at_most_two (slots data) (joint data) (outputMap data) hsmall)

def input (sourceSlots : Fin n → Slot) (f : Assignment sourceSlots → Fin k)
    (p : Fin k → Fin l) : Input n k l :=
  ⟨shape sourceSlots, transport sourceSlots f, p⟩

@[simp] theorem leftEmbedding_input (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (sourceSlots : Fin n → Slot) (f : Assignment sourceSlots → Fin k)
    (p : Fin k → Fin l) (P : Label sourceSlots f) :
    leftEmbedding large (input sourceSlots f p)
        (CanonicalCoarseningErasure.transportLabel sourceSlots f P) =
      labelEmbedding (key .left sourceSlots f) (left_large large) P := rfl

theorem lookup_mask_actual (hq : 0 < q)
    (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (sourceSlots : Fin n → Slot) (f : Assignment sourceSlots → Fin k)
    (p : Fin k → Fin l) :
    (lookup hq large (input sourceSlots f p)).1 = paddedMask (key .left sourceSlots f) := by
  funext a
  change paddedMask (key .left (dummySlots (shape sourceSlots)) (transport sourceSlots f)) a = _
  simp only [paddedMask, key, ← partition_erasure sourceSlots f]

theorem image_actual_legal (hq : 0 < q)
    (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (sourceSlots : Fin n → Slot) (f : Assignment sourceSlots → Fin k)
    (p : Fin k → Fin l) (P : Label sourceSlots f) :
    (lookup hq large (input sourceSlots f p)).2
        (labelEmbedding (key .left sourceSlots f) (left_large large) P) =
      labelEmbedding (key .right sourceSlots (p ∘ f)) large (coarsen sourceSlots f p P) := by
  have h := image_legal hq large (input sourceSlots f p)
    (CanonicalCoarseningErasure.transportLabel sourceSlots f P)
  rw [leftEmbedding_input] at h
  refine h.trans ?_
  apply Fin.ext
  change (CanonicalKeyEncoding.partEnum n
    (coarsen (dummySlots (shape sourceSlots)) (transport sourceSlots f) p
      (CanonicalCoarseningErasure.transportLabel sourceSlots f P)).val).val =
    (CanonicalKeyEncoding.partEnum n (coarsen sourceSlots f p P).val).val
  exact congrArg (fun a : Fin (CanonicalKeyEncoding.partitionWidth n) => a.val)
    (CanonicalCoarseningErasure.partIndex_coarsen sourceSlots f p P).symm

end
end PerfectCompleteness.CanonicalPartialTable

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_CanonicalCoarseningEncoding
attribute [-instance] _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.CanonicalPartialTable.legalEquiv_val _root_.OAI.PerfectCompleteness.CanonicalPartialTable.lookup_mask _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.HierarchicalArrays.joint_component _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.NodeEmbedding.embed_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.embeddedRows_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.equiv_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.matrix_evaluate _root_.OAI.PerfectCompleteness.NodeEmbedding.rowsEquiv_apply _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.TreeCanonical.assignmentEquiv_apply _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_selected _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CanonicalCoarseningEncoding

open MixedSupport CanonicalKeys CanonicalEdges

noncomputable section

universe uY uY' uZ uZ'

variable {n : Nat} {Y : Type uY} {Y' : Type uY'} {Z : Type uZ} {Z' : Type uZ'}

theorem fineKernel (slots : Fin n → Slot) (f : Assignment slots → Y)
    (eL : Y → Y') (heL : Function.Injective eL) :
    ∀ x x', f x = f x' ↔ (eL ∘ f) x = (eL ∘ f) x' := by
  intro x x'
  exact ⟨fun h => congrArg eL h, fun h => heL h⟩

theorem coarseKernel (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (eL : Y → Y') (eR : Z → Z') (p' : Y' → Z')
    (heR : Function.Injective eR) (commutes : ∀ y, p' (eL y) = eR (p y)) :
    ∀ x x', (p ∘ f) x = (p ∘ f) x' ↔
      (p' ∘ (eL ∘ f)) x = (p' ∘ (eL ∘ f)) x' := by
  intro x x'
  change p (f x) = p (f x') ↔ p' (eL (f x)) = p' (eL (f x'))
  rw [commutes (f x), commutes (f x')]
  exact ⟨fun h => congrArg eR h, fun h => heR h⟩

theorem key_fine (side : Side) (slots : Fin n → Slot) (f : Assignment slots → Y)
    (eL : Y → Y') (heL : Function.Injective eL) :
    key side slots (eL ∘ f) = key side slots f :=
  key_postcomp_injective side slots f eL heL

theorem key_coarse (side : Side) (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (eL : Y → Y') (eR : Z → Z') (p' : Y' → Z')
    (heR : Function.Injective eR) (commutes : ∀ y, p' (eL y) = eR (p y)) :
    key side slots (p' ∘ (eL ∘ f)) = key side slots (p ∘ f) :=
  (key_kernel_invariant side slots (p ∘ f) (p' ∘ (eL ∘ f))
    (coarseKernel slots f p eL eR p' heR commutes)).symm

def transportFine (slots : Fin n → Slot) (f : Assignment slots → Y)
    (eL : Y → Y') (heL : Function.Injective eL) (P : Label slots f) :
    Label slots (eL ∘ f) :=
  transportKernel slots f (eL ∘ f) (fineKernel slots f eL heL) P

def transportCoarse (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (eL : Y → Y') (eR : Z → Z') (p' : Y' → Z')
    (heR : Function.Injective eR) (commutes : ∀ y, p' (eL y) = eR (p y))
    (Q : Label slots (p ∘ f)) : Label slots (p' ∘ (eL ∘ f)) :=
  transportKernel slots (p ∘ f) (p' ∘ (eL ∘ f))
    (coarseKernel slots f p eL eR p' heR commutes) Q

@[simp] theorem transportFine_val (slots : Fin n → Slot) (f : Assignment slots → Y)
    (eL : Y → Y') (heL : Function.Injective eL) (P : Label slots f) :
    (transportFine slots f eL heL P).val = P.val := rfl

@[simp] theorem transportCoarse_val (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (eL : Y → Y') (eR : Z → Z') (p' : Y' → Z')
    (heR : Function.Injective eR) (commutes : ∀ y, p' (eL y) = eR (p y))
    (Q : Label slots (p ∘ f)) :
    (transportCoarse slots f p eL eR p' heR commutes Q).val = Q.val := rfl

theorem restore_transportFine (slots : Fin n → Slot) (f : Assignment slots → Y)
    (eL : Y → Y') (heL : Function.Injective eL) (P : Label slots f) :
    restore slots (eL ∘ f) (transportFine slots f eL heL P) = eL (restore slots f P) :=
  restore_transportKernel slots f (eL ∘ f) (fineKernel slots f eL heL)
    eL (fun _ => rfl) P

theorem restore_transportCoarse (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (eL : Y → Y') (eR : Z → Z') (p' : Y' → Z')
    (heR : Function.Injective eR) (commutes : ∀ y, p' (eL y) = eR (p y))
    (Q : Label slots (p ∘ f)) :
    restore slots (p' ∘ (eL ∘ f)) (transportCoarse slots f p eL eR p' heR commutes Q) =
      eR (restore slots (p ∘ f) Q) :=
  restore_transportKernel slots (p ∘ f) (p' ∘ (eL ∘ f))
    (coarseKernel slots f p eL eR p' heR commutes) eR (fun x => commutes (f x)) Q

theorem coarsen_transport (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (eL : Y → Y') (eR : Z → Z') (p' : Y' → Z')
    (heL : Function.Injective eL) (heR : Function.Injective eR)
    (commutes : ∀ y, p' (eL y) = eR (p y)) (P : Label slots f) :
    transportCoarse slots f p eL eR p' heR commutes (coarsen slots f p P) =
      coarsen slots (eL ∘ f) p' (transportFine slots f eL heL P) := by
  apply restore_injective slots (p' ∘ (eL ∘ f))
  calc
    restore slots (p' ∘ (eL ∘ f))
        (transportCoarse slots f p eL eR p' heR commutes (coarsen slots f p P)) =
        eR (restore slots (p ∘ f) (coarsen slots f p P)) :=
      restore_transportCoarse slots f p eL eR p' heR commutes (coarsen slots f p P)
    _ = eR (p (restore slots f P)) := congrArg eR (restore_coarsen slots f p P)
    _ = p' (eL (restore slots f P)) := (commutes (restore slots f P)).symm
    _ = p' (restore slots (eL ∘ f) (transportFine slots f eL heL P)) :=
      congrArg p' (restore_transportFine slots f eL heL P).symm
    _ = restore slots (p' ∘ (eL ∘ f))
        (coarsen slots (eL ∘ f) p' (transportFine slots f eL heL P)) :=
      (restore_coarsen slots (eL ∘ f) p' (transportFine slots f eL heL P)).symm

theorem coarsen_val (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (eL : Y → Y') (eR : Z → Z') (p' : Y' → Z')
    (heL : Function.Injective eL) (heR : Function.Injective eR)
    (commutes : ∀ y, p' (eL y) = eR (p y)) (P : Label slots f) :
    (coarsen slots f p P).val =
      (coarsen slots (eL ∘ f) p' (transportFine slots f eL heL P)).val :=
  congrArg Subtype.val (coarsen_transport slots f p eL eR p' heL heR commutes P)

@[simp] theorem partIndex_transportFine (slots : Fin n → Slot) (f : Assignment slots → Y)
    (eL : Y → Y') (heL : Function.Injective eL) (P : Label slots f) :
    CanonicalKeyEncoding.partEnum n (transportFine slots f eL heL P).val =
      CanonicalKeyEncoding.partEnum n P.val := rfl

theorem partIndex_coarsen (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (eL : Y → Y') (eR : Z → Z') (p' : Y' → Z')
    (heL : Function.Injective eL) (heR : Function.Injective eR)
    (commutes : ∀ y, p' (eL y) = eR (p y)) (P : Label slots f) :
    CanonicalKeyEncoding.partEnum n (coarsen slots f p P).val =
      CanonicalKeyEncoding.partEnum n
        (coarsen slots (eL ∘ f) p' (transportFine slots f eL heL P)).val :=
  congrArg (CanonicalKeyEncoding.partEnum n)
    (coarsen_val slots f p eL eR p' heL heR commutes P)

@[simp] theorem labelEmbedding_transportFine {q : Nat} (side : Side)
    (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (slots : Fin n → Slot) (f : Assignment slots → Y)
    (eL : Y → Y') (heL : Function.Injective eL) (P : Label slots f) :
    CanonicalLabelEncoding.labelEmbedding (key side slots (eL ∘ f)) large
        (transportFine slots f eL heL P) =
      CanonicalLabelEncoding.labelEmbedding (key side slots f) large P := rfl

theorem labelEmbedding_coarsen {q : Nat} (side : Side)
    (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (eL : Y → Y') (eR : Z → Z') (p' : Y' → Z')
    (heL : Function.Injective eL) (heR : Function.Injective eR)
    (commutes : ∀ y, p' (eL y) = eR (p y)) (P : Label slots f) :
    CanonicalLabelEncoding.labelEmbedding (key side slots (p ∘ f)) large
        (coarsen slots f p P) =
      CanonicalLabelEncoding.labelEmbedding (key side slots (p' ∘ (eL ∘ f))) large
        (coarsen slots (eL ∘ f) p' (transportFine slots f eL heL P)) := by
  apply Fin.ext
  change (CanonicalKeyEncoding.partEnum n (coarsen slots f p P).val).val =
    (CanonicalKeyEncoding.partEnum n
      (coarsen slots (eL ∘ f) p' (transportFine slots f eL heL P)).val).val
  exact congrArg (fun i : Fin (CanonicalKeyEncoding.partitionWidth n) => i.val)
    (partIndex_coarsen slots f p eL eR p' heL heR commutes P)

end
end PerfectCompleteness.CanonicalCoarseningEncoding

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_KeyMetadataMachine
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.actualProjection_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.clauseAnswerEquiv_decode _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.clauseAnswerEquiv_symm_val _root_.OAI.PerfectCompleteness.SourceGame.decodeLabel_encodeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.KeyMetadataMachine


open Turing UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Reduction.MachineSubstitution
open MachineComposition CanonicalKeyShape ClauseSupport MixedSupport
open scoped BigOperators Classical

noncomputable section

variable {n : Nat}

def actualSlot (shape : Shape) (occurrence : Nat) (variableIDs : Fin 3 → Nat) : Slot :=
  match shape with
  | .clause signs => .clause occurrence variableIDs signs
  | .bit => .bit (variableIDs 0)

def sourceField : Shape → SupportMode → Option (Fin 4)
  | .clause _, .full => some 0
  | .clause _, .clauseBit i => some i.succ
  | .bit, .bit => some 1
  | _, _ => none

def prefixWords (position : Fin n) (shape : Shape) (mode : SupportMode) : List Nat :=
  [position.val, match shape, mode with | .clause _, .full => 2 | _, _ => 1]

def suffixWords : Shape → SupportMode → List Nat
  | .clause signs, .full =>
      [KeyMetadataEncoding.bitWord signs.1, KeyMetadataEncoding.bitWord signs.2.1,
        KeyMetadataEncoding.bitWord signs.2.2]
  | _, _ => [0, 0, 0]

def retainedWords (position : Fin n) (slot : Slot) (mode : SupportMode) : List Nat :=
  if recover slot mode = .dropped then []
  else KeyMetadataEncoding.entryWords (position, recover slot mode)

def retainedBits (position : Fin n) (slot : Slot) (mode : SupportMode) : List Bool :=
  encodeWords (retainedWords position slot mode)

theorem retainedWords_eq (position : Fin n) (shape : Shape) (mode : SupportMode)
    (occurrence : Nat) (variableIDs : Fin 3 → Nat) :
    retainedWords position (actualSlot shape occurrence variableIDs) mode =
      match sourceField shape mode with
      | none => []
      | some field => prefixWords position shape mode ++
          [fieldValue occurrence variableIDs field] ++ suffixWords shape mode := by
  cases shape <;> cases mode <;>
    simp [retainedWords, actualSlot, sourceField, prefixWords, suffixWords,
      fieldValue, recover, KeyMetadataEncoding.entryWords]
  rfl

variable {K Λ σ : Type} [DecidableEq K]

omit [DecidableEq K] in
@[simp] theorem finish_pushBound (exit : Option Λ) :
    Runtime.statementPushBound (finish (K := K) (σ := σ) exit) = 0 := by
  cases exit <;> rfl

def literal (destination : K) (bits : List Bool) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  pushWord destination bits.reverse (finish exit)

theorem literal_step (destination : K) (bits : List Bool) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ)) (label : Λ)
    (atLabel : program label = literal destination bits exit)
    (base : K → List Bool) (ambient : σ) :
    TM2.step program ⟨some label, clean ambient, base⟩ =
      some ⟨exit, clean ambient, Function.update base destination (bits ++ base destination)⟩ := by
  change some (TM2.stepAux (program label) (ambient, none) base) = _
  rw [atLabel]
  unfold literal
  rw [stepAux_pushWord (Γ := Alphabet (K := K)) (Λ := Λ) (σ := State σ)
    destination bits.reverse (finish exit) (ambient, none) base,
    List.reverse_reverse, stepAux_finish]

def instruction (position : Fin n) (shape : Shape) (mode : SupportMode)
    (tape : Fin 6 → K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .suffix => match sourceField shape mode with
      | none => finish exit
      | some _ => literal (tape 5) (encodeWords (suffixWords shape mode))
          (some (labels .copyOut))
  | .copyOut => UniqueGamesTheorem.Reduction.MachineTransfer.loopAt
      (idTape tape ((sourceField shape mode).getD 0)) (tape 4) id false
      (labels .copyOut) (some (labels .copyBack))
  | .copyBack => MachineCopy.forkLoop (tape 4)
      (idTape tape ((sourceField shape mode).getD 0)) (tape 5) false
      (labels .copyBack) (some (labels .prefix))
  | .prefix => literal (tape 5) (encodeWords (prefixWords position shape mode)) exit

theorem droppedTrace (position : Fin n) (shape : Shape) (mode : SupportMode)
    (hdrop : sourceField shape mode = none)
    (tape : Fin 6 → K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, program (labels label) =
      instruction position shape mode tape labels exit label)
    (base : K → List Bool) (ambient : σ) :
    (advance (TM2.step program))^[1]
      (some ⟨some (labels .suffix), clean ambient, base⟩) =
      some ⟨exit, clean ambient, base⟩ := by
  change some (TM2.stepAux (program (labels .suffix)) (ambient, none) base) = _
  rw [atLabels .suffix]
  simp only [instruction, hdrop, stepAux_finish]

theorem selectedTrace (position : Fin n) (shape : Shape) (mode : SupportMode)
    (field : Fin 4) (hfield : sourceField shape mode = some field)
    (tape : Fin 6 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, program (labels label) =
      instruction position shape mode tape labels exit label)
    (base : K → List Bool) (scratchEmpty : base (tape 4) = []) (ambient : σ) :
    (advance (TM2.step program))^[2 * ((base (idTape tape field)).length + 1) + 2]
      (some ⟨some (labels .suffix), clean ambient, base⟩) =
      some ⟨exit, clean ambient, Function.update base (tape 5)
        ((encodeWords (prefixWords position shape mode) ++ base (idTape tape field) ++
          encodeWords (suffixWords shape mode)) ++ base (tape 5))⟩ := by
  have hd (i j : Fin 6) (h : i ≠ j) : tape i ≠ tape j := fun heq => h (distinct heq)
  have hsourceOutput : idTape tape field ≠ tape 5 := by
    apply hd
    intro h
    have heq := congrArg Fin.val h
    have hlt := field.isLt
    change field.val = 5 at heq
    omega
  have hsourceScratch : idTape tape field ≠ tape 4 := by
    apply hd
    intro h
    have heq := congrArg Fin.val h
    have hlt := field.isLt
    change field.val = 4 at heq
    omega
  have houtputScratch : tape 5 ≠ tape 4 := hd 5 4 (by decide)
  let afterSuffix := Function.update base (tape 5)
    (encodeWords (suffixWords shape mode) ++ base (tape 5))
  let afterCopy := Function.update base (tape 5)
    (base (idTape tape field) ++ encodeWords (suffixWords shape mode) ++ base (tape 5))
  have first : (advance (TM2.step program))^[1]
      (some ⟨some (labels .suffix), clean ambient, base⟩) =
      some ⟨some (labels .copyOut), clean ambient, afterSuffix⟩ := by
    rw [Function.iterate_one, advance_some]
    apply literal_step (tape 5) (encodeWords (suffixWords shape mode))
      (some (labels .copyOut)) program (labels .suffix)
    rw [atLabels .suffix]
    simp only [instruction, hfield]
  have hselected : (sourceField shape mode).getD 0 = field := by
    rw [hfield]
    rfl
  have atOut : program (labels .copyOut) =
      UniqueGamesTheorem.Reduction.MachineTransfer.loopAt (idTape tape field) (tape 4) id false
        (labels .copyOut) (some (labels .copyBack)) := by
    rw [atLabels .copyOut]
    exact congrArg (fun selected : Fin 4 =>
      UniqueGamesTheorem.Reduction.MachineTransfer.loopAt (Γ := Alphabet (K := K)) (σ := σ)
        (idTape tape selected) (tape 4) id false
        (labels .copyOut) (some (labels .copyBack))) hselected
  have atBack : program (labels .copyBack) =
      MachineCopy.forkLoop (tape 4) (idTape tape field) (tape 5) false
        (labels .copyBack) (some (labels .prefix)) := by
    rw [atLabels .copyBack]
    exact congrArg (fun selected : Fin 4 =>
      MachineCopy.forkLoop (tape 4) (idTape tape selected) (tape 5) false
        (labels .copyBack) (some (labels .prefix))) hselected
  have hscratch : afterSuffix (tape 4) = [] := by
    simpa only [afterSuffix, Function.update_of_ne (Ne.symm houtputScratch)] using scratchEmpty
  have hsource : afterSuffix (idTape tape field) = base (idTape tape field) := by
    simp [afterSuffix, hsourceOutput]
  have htapes : Function.update afterSuffix (tape 5)
      (afterSuffix (idTape tape field) ++ afterSuffix (tape 5)) = afterCopy := by
    simp [afterSuffix, afterCopy, hsourceOutput, Function.update_idem, List.append_assoc]
  let copied := MachineCopy.copyInTime (idTape tape field) (tape 5) (tape 4)
    hsourceOutput hsourceScratch houtputScratch false (labels .copyOut) (labels .copyBack)
    (some (labels .prefix)) program atOut atBack afterSuffix hscratch ambient none
  have middle := copied.evals_in_steps
  change (advance (TM2.step program))^[2 * ((afterSuffix (idTape tape field)).length + 1)]
    (some ⟨some (labels .copyOut), clean ambient, afterSuffix⟩) =
    some ⟨some (labels .prefix), clean ambient,
      Function.update afterSuffix (tape 5)
        (afterSuffix (idTape tape field) ++ afterSuffix (tape 5))⟩ at middle
  rw [htapes, hsource] at middle
  have last : (advance (TM2.step program))^[1]
      (some ⟨some (labels .prefix), clean ambient, afterCopy⟩) =
      some ⟨exit, clean ambient, Function.update base (tape 5)
        ((encodeWords (prefixWords position shape mode) ++ base (idTape tape field) ++
          encodeWords (suffixWords shape mode)) ++ base (tape 5))⟩ := by
    rw [Function.iterate_one, advance_some]
    have h := literal_step (tape 5) (encodeWords (prefixWords position shape mode)) exit
      program (labels .prefix) (atLabels .prefix) afterCopy ambient
    simpa only [afterCopy, Function.update_self, Function.update_idem, List.append_assoc] using h
  have joined := joinTrace (joinTrace first middle) last
  rw [show (1 + 2 * ((base (idTape tape field)).length + 1)) + 1 =
    2 * ((base (idTape tape field)).length + 1) + 2 by omega] at joined
  exact joined

end
end PerfectCompleteness.KeyMetadataMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_CanonicalKeyMachine
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalLabelEncoding.labelEmbedding_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.HierarchicalArrays.joint_component _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.NodeEmbedding.embed_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.embeddedRows_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.equiv_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.matrix_evaluate _root_.OAI.PerfectCompleteness.NodeEmbedding.rowsEquiv_apply _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.TreeCanonical.assignmentEquiv_apply _root_.OAI.PerfectCompleteness.TreeSourceSpaces.HPullback_apply _root_.OAI.PerfectCompleteness.TreeSourceSpaces.sourceProjection_apply _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_selected _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec.decodeWords_encodeWord _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter.counterTapes_counter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CanonicalKeyMachine


open Turing UniqueGamesTheorem.Foundations.Complexity MachineComposition
open CanonicalKeys CanonicalKeyShape ClauseSupport MixedSupport
open scoped BigOperators Classical

noncomputable section

variable {n : Nat}

def actualSlots (shapes : Fin n → Shape) (occurrences : Fin n → Nat)
    (variableIDs : Fin n → Fin 3 → Nat) : Fin n → Slot :=
  fun i => KeyMetadataMachine.actualSlot (shapes i) (occurrences i) (variableIDs i)

def recoveredKey (shapes : Fin n → Shape) (modes : Fin n → SupportMode) (side : Side)
    (partition : Set (Set (Fin n → ReducedValue)))
    (occurrences : Fin n → Nat) (variableIDs : Fin n → Fin 3 → Nat) : Key n where
  side := side
  retained := retained (actualSlots shapes occurrences variableIDs) modes
  partition := partition

def prefixBits (side : Side) (partition : Set (Set (Fin n → ReducedValue))) : List Bool :=
  encodeWords (CanonicalKeyEncoding.sideWord side :: CanonicalKeyEncoding.partitionWords partition)

def payload (shapes : Fin n → Shape) (modes : Fin n → SupportMode) (side : Side)
    (partition : Set (Set (Fin n → ReducedValue)))
    (occurrences : Fin n → Nat) (variableIDs : Fin n → Fin 3 → Nat) : List Bool :=
  CanonicalKeyEncoding.bits (recoveredKey shapes modes side partition occurrences variableIDs) ++ [true]

theorem metadata_words (slots : Fin n → Slot) (modes : Fin n → SupportMode)
    (positions : List (Fin n)) :
    KeyMetadataEncoding.metadataWords
        ((positions.map (fun i => (i, recover (slots i) (modes i)))).filter
          (fun entry => decide (entry.2 ≠ .dropped))) =
      positions.flatMap (fun i => KeyMetadataMachine.retainedWords i (slots i) (modes i)) := by
  induction positions with
  | nil => rfl
  | cons i positions ih =>
    by_cases h : recover (slots i) (modes i) = .dropped
    · simp [KeyMetadataEncoding.metadataWords, KeyMetadataMachine.retainedWords, h] at ih ⊢
      exact ih
    · simpa only [List.map_cons, List.filter_cons, h, ne_eq, not_false_eq_true,
        decide_true, Bool.cond_true, ite_true, if_true, KeyMetadataEncoding.metadataWords_cons,
        KeyMetadataMachine.retainedWords, ite_false, if_false, List.flatMap_cons] using
        congrArg (KeyMetadataEncoding.entryWords (i, recover (slots i) (modes i)) ++ ·) ih

theorem encodeWords_flatMap {α : Type*} (xs : List α) (words : α → List Nat) :
    encodeWords (xs.flatMap words) = xs.flatMap (fun x => encodeWords (words x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem payload_eq (shapes : Fin n → Shape) (modes : Fin n → SupportMode) (side : Side)
    (partition : Set (Set (Fin n → ReducedValue)))
    (occurrences : Fin n → Nat) (variableIDs : Fin n → Fin 3 → Nat) :
    payload shapes modes side partition occurrences variableIDs =
      prefixBits side partition ++
        (List.finRange n).flatMap (fun i => KeyMetadataMachine.retainedBits i
          (KeyMetadataMachine.actualSlot (shapes i) (occurrences i) (variableIDs i)) (modes i)) ++
        [true] := by
  change encodeWords
    ((CanonicalKeyEncoding.sideWord side :: CanonicalKeyEncoding.partitionWords partition) ++
      KeyMetadataEncoding.metadataWords (retained (actualSlots shapes occurrences variableIDs) modes)) ++
      [true] = _
  rw [encodeWords_append]
  unfold retained
  rw [metadata_words, encodeWords_flatMap]
  rfl

variable {K Λ σ : Type} [DecidableEq K]

abbrev State (σ : Type) := KeyMetadataMachine.State σ

def localInstruction (shapes : Fin n → Shape) (modes : Fin n → SupportMode) (side : Side)
    (partition : Set (Set (Fin n → ReducedValue))) (tape : Fin n → Fin 6 → K) (output : K) :
    (command : Command n) → (LocalLabel command → Λ) → Option Λ →
      LocalLabel command → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .terminal, _, exit, _ => KeyMetadataMachine.literal output [true] exit
  | .metadata i, labels, exit, label =>
      KeyMetadataMachine.instruction i (shapes i) (modes i) (tape i) labels exit label
  | .header, _, exit, _ => KeyMetadataMachine.literal output (prefixBits side partition) exit

def instruction (shapes : Fin n → Shape) (modes : Fin n → SupportMode) (side : Side)
    (partition : Set (Set (Fin n → ReducedValue))) (tape : Fin n → Fin 6 → K) (output : K)
    (labels : Label n → Λ) (exit : Option Λ) :
    Label n → TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  MachineFiniteSequence.instruction LocalLabel main
    (localInstruction shapes modes side partition tape output) (commands n) labels exit

def commandBits (shapes : Fin n → Shape) (modes : Fin n → SupportMode) (side : Side)
    (partition : Set (Set (Fin n → ReducedValue)))
    (occurrences : Fin n → Nat) (variableIDs : Fin n → Fin 3 → Nat) : Command n → List Bool
  | .terminal => [true]
  | .metadata i => KeyMetadataMachine.retainedBits i
      (KeyMetadataMachine.actualSlot (shapes i) (occurrences i) (variableIDs i)) (modes i)
  | .header => prefixBits side partition

def commandCost (shapes : Fin n → Shape) (modes : Fin n → SupportMode)
    (tape : Fin n → Fin 6 → K) (base : K → List Bool) : Command n → Nat
  | .terminal => 1
  | .metadata i => match KeyMetadataMachine.sourceField (shapes i) (modes i) with
      | none => 1
      | some field => 2 * ((base (KeyMetadataMachine.idTape (tape i) field)).length + 1) + 2
  | .header => 1

theorem commands_bits (shapes : Fin n → Shape) (modes : Fin n → SupportMode) (side : Side)
    (partition : Set (Set (Fin n → ReducedValue)))
    (occurrences : Fin n → Nat) (variableIDs : Fin n → Fin 3 → Nat) :
    (commands n).reverse.flatMap (commandBits shapes modes side partition occurrences variableIDs) =
      payload shapes modes side partition occurrences variableIDs := by
  rw [payload_eq]
  simp only [commands, List.reverse_cons, List.reverse_append, List.reverse_nil,
    List.map_reverse, List.reverse_reverse, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.flatMap_map, commandBits, List.nil_append, List.append_nil, List.append_assoc]

omit [DecidableEq K] in
theorem commandCost_metadata_le (shapes : Fin n → Shape) (modes : Fin n → SupportMode)
    (tape : Fin n → Fin 6 → K) (base : K → List Bool) (i : Fin n) :
    commandCost shapes modes tape base (.metadata i) ≤
      2 * KeyMetadataMachine.sourceLength (tape i) base + 4 := by
  cases h : KeyMetadataMachine.sourceField (shapes i) (modes i) with
  | none => simp only [commandCost, h]; omega
  | some field =>
    have hb := KeyMetadataMachine.selected_length_le (tape i) base field
    simp only [commandCost, h]
    omega

omit [DecidableEq K] in
theorem commands_cost_le (shapes : Fin n → Shape) (modes : Fin n → SupportMode)
    (tape : Fin n → Fin 6 → K) (base : K → List Bool) :
    ((commands n).map (commandCost shapes modes tape base)).sum ≤
      2 * sourceLength tape base + 4 * n + 2 := by
  have hsum : (∑ i, commandCost shapes modes tape base (.metadata i)) ≤
      ∑ i : Fin n, (2 * KeyMetadataMachine.sourceLength (tape i) base + 4) :=
    Finset.sum_le_sum (fun i _ => commandCost_metadata_le shapes modes tape base i)
  have htotal : (∑ i : Fin n, (2 * KeyMetadataMachine.sourceLength (tape i) base + 4)) =
      2 * sourceLength tape base + 4 * n := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [sourceLength, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.nsmul_eq_mul, Nat.mul_comm]
  rw [htotal] at hsum
  rw [commands_cost]
  change 1 + (∑ i, commandCost shapes modes tape base (.metadata i)) + 1 ≤ _
  omega

def keyInTime (shapes : Fin n → Shape) (modes : Fin n → SupportMode) (side : Side)
    (partition : Set (Set (Fin n → ReducedValue)))
    (occurrences : Fin n → Nat) (variableIDs : Fin n → Fin 3 → Nat)
    (tape : Fin n → Fin 6 → K) (distinct : ∀ i, Function.Injective (tape i))
    (scratch output : K) (scratchOutput : scratch ≠ output)
    (sharedScratch : ∀ i, tape i 4 = scratch) (sharedOutput : ∀ i, tape i 5 = output)
    (labels : Label n → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, program (labels label) =
      instruction shapes modes side partition tape output labels exit label)
    (base : K → List Bool)
    (sourceWords : ∀ i field, base (KeyMetadataMachine.idTape (tape i) field) =
      encodeWord (KeyMetadataMachine.fieldValue (occurrences i) (variableIDs i) field))
    (scratchEmpty : base scratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry labels exit, KeyMetadataMachine.clean ambient, base⟩
      (some ⟨exit, KeyMetadataMachine.clean ambient, Function.update base output
        (payload shapes modes side partition occurrences variableIDs ++ base output)⟩)
      (2 * sourceLength tape base + 4 * n + 2) := by
  let bits := commandBits shapes modes side partition occurrences variableIDs
  let result : Command n → List Bool → List Bool := fun command out => bits command ++ out
  let cost := commandCost shapes modes tape base
  let tapes : List Bool → K → List Bool := fun out => Function.update base output out
  have source_preserved (out : List Bool) (i : Fin n) (field : Fin 4) :
      tapes out (KeyMetadataMachine.idTape (tape i) field) =
        base (KeyMetadataMachine.idTape (tape i) field) := by
    exact Function.update_of_ne (source_ne_output tape distinct output sharedOutput i field) out base
  have scratch_preserved (out : List Bool) (i : Fin n) : tapes out (tape i 4) = [] := by
    rw [sharedScratch i]
    exact (Function.update_of_ne scratchOutput out base).trans scratchEmpty
  have localTrace : ∀ command ∈ commands n,
      ∀ (placed : LocalLabel command → Λ) (next : Option Λ),
      (∀ l, program (placed l) =
        localInstruction shapes modes side partition tape output command placed next l) →
      ∀ out : List Bool, True →
      (advance (TM2.step program))^[cost command]
        (some ⟨some (placed (main command)), KeyMetadataMachine.clean ambient, tapes out⟩) =
      some ⟨next, KeyMetadataMachine.clean ambient, tapes (result command out)⟩ := by
    intro command _ placed next atPlaced out _
    cases command with
    | terminal =>
      have h := KeyMetadataMachine.literal_step output [true] next program (placed ())
        (atPlaced ()) (tapes out) ambient
      simpa only [cost, commandCost, Function.iterate_one, advance_some, main,
        result, bits, commandBits, tapes, Function.update_self, Function.update_idem] using h
    | header =>
      have h := KeyMetadataMachine.literal_step output (prefixBits side partition) next
        program (placed ()) (atPlaced ()) (tapes out) ambient
      simpa only [cost, commandCost, Function.iterate_one, advance_some, main,
        result, bits, commandBits, tapes, Function.update_self, Function.update_idem] using h
    | metadata i =>
      have atMetadata : ∀ l, program (placed l) =
          KeyMetadataMachine.instruction i (shapes i) (modes i) (tape i) placed next l := atPlaced
      cases hfield : KeyMetadataMachine.sourceField (shapes i) (modes i) with
      | none =>
        have hbits : bits (.metadata i) = [] := by
          simp only [bits, commandBits, KeyMetadataMachine.retainedBits,
            KeyMetadataMachine.retainedWords_eq, hfield, encodeWords]
        have h := KeyMetadataMachine.droppedTrace i (shapes i) (modes i) hfield
          (tape i) placed next program atMetadata (tapes out) ambient
        simpa only [cost, commandCost, hfield, main, result, hbits, List.nil_append] using h
      | some field =>
        have hbits : bits (.metadata i) =
            encodeWords (KeyMetadataMachine.prefixWords i (shapes i) (modes i)) ++
              base (KeyMetadataMachine.idTape (tape i) field) ++
              encodeWords (KeyMetadataMachine.suffixWords (shapes i) (modes i)) := by
          rw [sourceWords i field]
          simp [bits, commandBits, KeyMetadataMachine.retainedBits,
            KeyMetadataMachine.retainedWords_eq, hfield, encodeWords, List.append_assoc]
        have h := KeyMetadataMachine.selectedTrace i (shapes i) (modes i) field hfield
          (tape i) (distinct i) placed next program atMetadata (tapes out)
          (scratch_preserved out i) ambient
        rw [source_preserved out i field, sharedOutput i] at h
        simpa only [cost, commandCost, hfield, main, result, hbits,
          tapes, Function.update_self, Function.update_idem] using h
  have run := MachineFiniteSequence.trace LocalLabel main
    (localInstruction shapes modes side partition tape output) result (fun command _ => cost command)
    program (fun _ : List Bool => True) (fun _ => KeyMetadataMachine.clean ambient) tapes
    (commands n) (fun _ _ _ _ => True.intro) localTrace labels exit atLabels (base output) True.intro
  have finalOutput : MachineFiniteSequence.resultOf result (commands n) (base output) =
      payload shapes modes side partition occurrences variableIDs ++ base output := by
    rw [resultOf_prepend]
    exact congrArg (· ++ base output) (commands_bits shapes modes side partition occurrences variableIDs)
  refine
    { steps := MachineFiniteSequence.steps result (fun command _ => cost command) (commands n) (base output)
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · rw [finalOutput] at run
    unfold MachineComposition.advance at run
    simpa only [entry, tapes, Function.update_eq_self, Function.flip_def,
      Option.bind_eq_bind] using run
  · rw [steps_constant]
    exact commands_cost_le shapes modes tape base

end
end PerfectCompleteness.CanonicalKeyMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_CanonicalEndpointMachine
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalLabelEncoding.labelEmbedding_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec.decodeWords_encodeWord _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter.counterTapes_counter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CanonicalEndpointMachine


open Turing UniqueGamesTheorem.Foundations.Complexity MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer
open CanonicalKeys CanonicalKeyShape ClauseSupport
open scoped Classical

noncomputable section

variable {n : Nat} {K Λ A : Type} [DecidableEq K]

abbrev State (A : Type) := CanonicalDictionaryMachine.State A
abbrev clean (ambient : A) : State A := CanonicalDictionaryMachine.clean ambient

inductive Label (n : Nat)
  | key (label : CanonicalKeyMachine.Label n)
  | reverse
  | dictionary (label : CanonicalDictionaryMachine.Label)
  | drainKey
  deriving DecidableEq, Fintype

def main (n : Nat) : Label n := .key (.inl ())

def instruction (shapes : Fin n → Shape) (modes : Fin n → SupportMode) (side : Side)
    (partition : Set (Set (Fin n → ReducedValue)))
    (tape : Fin n → Fin 6 → K) (forwardKey : K) (dictionary : Fin 8 → K)
    (labels : Label n → Λ) (done rejected : Option Λ) :
    Label n → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .key label => CanonicalKeyMachine.instruction shapes modes side partition tape forwardKey
      (fun l => labels (.key l)) (some (labels .reverse)) label
  | .reverse => loopAt forwardKey (dictionary 0) id false (labels .reverse)
      (some (labels (.dictionary CanonicalDictionaryMachine.main)))
  | .dictionary label => CanonicalDictionaryMachine.instruction dictionary
      (fun l => labels (.dictionary l)) (some (labels .drainKey)) rejected label
  | .drainKey => MachineDrain.drain (dictionary 0) (labels .drainKey) done

def finalTapes (dictionary : Fin 8 → K) (base : K → List Bool)
    (earlier : List (Key n)) (key : Key n) : K → List Bool :=
  Function.update (Function.update base (dictionary 1)
    (BinaryNameSearch.stream (CanonicalVertexNames.tokens (earlier ++ [key])))) (dictionary 7)
      ((encodeWord (CanonicalOnlineNames.onlineID earlier key)).reverse ++ base (dictionary 7))

def budget (tape : Fin n → Fin 6 → K) (base : K → List Bool)
    (earlier : List (Key n)) (key : Key n) : Nat :=
  ((2 * CanonicalKeyMachine.sourceLength tape base + 4 * n + 2) +
      ((CanonicalVertexNames.payload key).length + 1)) +
    (3 * (BinaryNameSearch.stream (CanonicalVertexNames.tokens (earlier ++ [key]))).length ^ 2 +
      16 * (BinaryNameSearch.stream (CanonicalVertexNames.tokens (earlier ++ [key]))).length + 12) +
    ((CanonicalVertexNames.payload key).length + 1)

def endpointInTime (shapes : Fin n → Shape) (modes : Fin n → SupportMode) (side : Side)
    (partition : Set (Set (Fin n → ReducedValue)))
    (occurrences : Fin n → Nat) (variableIDs : Fin n → Fin 3 → Nat)
    (tape : Fin n → Fin 6 → K) (distinct : ∀ i, Function.Injective (tape i))
    (forwardKey : K) (dictionary : Fin 8 → K)
    (dictionaryDistinct : Function.Injective dictionary)
    (forwardDistinct : ∀ i, forwardKey ≠ dictionary i)
    (sharedScratch : ∀ i, tape i 4 = dictionary 5)
    (sharedOutput : ∀ i, tape i 5 = forwardKey)
    (labels : Label n → Λ) (done rejected : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) =
      instruction shapes modes side partition tape forwardKey dictionary labels done rejected l)
    (base : K → List Bool) (ambient : A) (earlier : List (Key n))
    (sourceWords : ∀ i field, base (KeyMetadataMachine.idTape (tape i) field) =
      encodeWord (KeyMetadataMachine.fieldValue (occurrences i) (variableIDs i) field))
    (forwardEmpty : base forwardKey = []) (keyEmpty : base (dictionary 0) = [])
    (dictionaryWord : base (dictionary 1) =
      BinaryNameSearch.stream (CanonicalVertexNames.tokens earlier))
    (empty : ∀ i : Fin 8, 2 ≤ i.val → i.val ≤ 6 → base (dictionary i) = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (main n)), clean ambient, base⟩
      (some ⟨done, clean ambient, finalTapes dictionary base earlier
        (CanonicalKeyMachine.recoveredKey shapes modes side partition occurrences variableIDs)⟩)
      (budget tape base earlier
        (CanonicalKeyMachine.recoveredKey shapes modes side partition occurrences variableIDs)) := by
  let key := CanonicalKeyMachine.recoveredKey shapes modes side partition occurrences variableIDs
  let bits := CanonicalVertexNames.payload key
  let s₁ := Function.update base forwardKey bits
  let s₂ := Function.update base (dictionary 0) bits.reverse
  let s₃ := Function.update (Function.update s₂ (dictionary 1)
    (BinaryNameSearch.stream (CanonicalVertexNames.tokens (earlier ++ [key])))) (dictionary 7)
      ((encodeWord (CanonicalOnlineNames.onlineID earlier key)).reverse ++ base (dictionary 7))
  have hd (i j : Fin 8) (hne : i ≠ j) : dictionary i ≠ dictionary j :=
    fun h => hne (dictionaryDistinct h)
  have payloadEq : CanonicalKeyMachine.payload shapes modes side partition occurrences variableIDs =
      bits := rfl
  have keyEntry : CanonicalKeyMachine.entry (fun l => labels (.key l))
      (some (labels .reverse)) = some (labels (main n)) := rfl
  have produced : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (main n)), clean ambient, base⟩
      (some ⟨some (labels .reverse), clean ambient, s₁⟩)
      (2 * CanonicalKeyMachine.sourceLength tape base + 4 * n + 2) := by
    have run := CanonicalKeyMachine.keyInTime shapes modes side partition occurrences variableIDs
      tape distinct (dictionary 5) forwardKey (Ne.symm (forwardDistinct 5))
      sharedScratch sharedOutput (fun l => labels (.key l)) (some (labels .reverse))
      program (fun l => atLabels (.key l)) base sourceWords
      (empty 5 (by decide) (by decide)) (ambient, false, none)
    simpa only [keyEntry, payloadEq, forwardEmpty, List.append_nil, s₁,
      KeyMetadataMachine.clean, clean, CanonicalDictionaryMachine.clean, BinaryNameCompare.clean]
      using run
  have s₁forward : s₁ forwardKey = bits := by simp [s₁]
  have s₁key : s₁ (dictionary 0) = [] := by
    simp [s₁, Ne.symm (forwardDistinct 0), keyEmpty]
  have transferredTapes : tapesAt forwardKey (dictionary 0) s₁ [] bits.reverse = s₂ := by
    funext k
    by_cases h0 : k = dictionary 0
    · subst k
      simp [tapesAt, s₁, s₂]
    · by_cases hf : k = forwardKey
      · subst k
        simp [tapesAt, s₁, s₂, forwardDistinct 0, forwardEmpty]
      · simp [tapesAt, s₁, s₂, h0, hf]
  have transferred : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .reverse), clean ambient, s₁⟩
      (some ⟨some (labels (.dictionary CanonicalDictionaryMachine.main)), clean ambient, s₂⟩)
      (bits.length + 1) := by
    have run := transferAtInTime (Γ := Alphabet) forwardKey (dictionary 0)
      (forwardDistinct 0) id false (labels .reverse)
      (some (labels (.dictionary CanonicalDictionaryMachine.main))) program (atLabels .reverse)
      s₁ (ambient, false, none) none
    simpa only [s₁forward, s₁key, List.map_id_fun, id_eq, List.append_nil, transferredTapes,
      clean, CanonicalDictionaryMachine.clean, BinaryNameCompare.clean] using run
  have s₂key : s₂ (dictionary 0) = bits.reverse := by simp [s₂]
  have s₂dictionary : s₂ (dictionary 1) =
      BinaryNameSearch.stream (CanonicalVertexNames.tokens earlier) := by
    simp [s₂, hd 1 0 (by decide), dictionaryWord]
  have s₂accumulator : s₂ (dictionary 7) = base (dictionary 7) := by
    simp [s₂, hd 7 0 (by decide)]
  have s₂empty (i : Fin 8) (lo : 2 ≤ i.val) (hi : i.val ≤ 6) : s₂ (dictionary i) = [] := by
    have ne : i ≠ 0 := by intro h; subst i; omega
    simp [s₂, hd i 0 ne, empty i lo hi]
  have named : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.dictionary CanonicalDictionaryMachine.main)), clean ambient, s₂⟩
      (some ⟨some (labels .drainKey), clean ambient, s₃⟩)
      (3 * (BinaryNameSearch.stream (CanonicalVertexNames.tokens (earlier ++ [key]))).length ^ 2 +
        16 * (BinaryNameSearch.stream (CanonicalVertexNames.tokens (earlier ++ [key]))).length + 12) := by
    have run := CanonicalDictionaryNames.dictionaryInTime dictionary dictionaryDistinct
      (fun l => labels (.dictionary l)) (some (labels .drainKey)) rejected program
      (fun l => atLabels (.dictionary l)) s₂ ambient earlier key s₂key s₂dictionary s₂empty
    simpa only [s₂accumulator, s₃, clean] using run
  have s₃key : s₃ (dictionary 0) = bits.reverse := by
    simp [s₃, s₂, hd 0 7 (by decide), hd 0 1 (by decide)]
  have restored : Function.update s₃ (dictionary 0) [] = finalTapes dictionary base earlier key := by
    funext k
    by_cases h0 : k = dictionary 0
    · subst k
      simp [finalTapes, hd 0 7 (by decide), hd 0 1 (by decide), keyEmpty]
    · simp [s₃, s₂, finalTapes, Function.update_apply, h0]
  have drained : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .drainKey), clean ambient, s₃⟩
      (some ⟨done, clean ambient, finalTapes dictionary base earlier key⟩)
      (bits.length + 1) := by
    have run := MachineDrain.drainInTime (dictionary 0) (labels .drainKey) done program
      (atLabels .drainKey) s₃ (ambient, false, none) none
    simpa only [s₃key, List.length_reverse, restored, clean,
      CanonicalDictionaryMachine.clean, BinaryNameCompare.clean] using run
  have first := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ produced transferred
  have second := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ first named
  have all := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ second drained
  simpa only [budget, bits, key, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all

theorem finalTapes_frame (dictionary : Fin 8 → K) (base : K → List Bool)
    (earlier : List (Key n)) (key : Key n) (k : K)
    (notDictionary : k ≠ dictionary 1) (notAccumulator : k ≠ dictionary 7) :
    finalTapes dictionary base earlier key k = base k := by
  simp only [finalTapes, Function.update_of_ne notAccumulator,
    Function.update_of_ne notDictionary]

theorem finalTapes_sources (tape : Fin n → Fin 6 → K) (dictionary : Fin 8 → K)
    (base : K → List Bool) (earlier : List (Key n)) (key : Key n)
    (notDictionary : ∀ i field, KeyMetadataMachine.idTape (tape i) field ≠ dictionary 1)
    (notAccumulator : ∀ i field, KeyMetadataMachine.idTape (tape i) field ≠ dictionary 7)
    (i : Fin n) (field : Fin 4) :
    finalTapes dictionary base earlier key (KeyMetadataMachine.idTape (tape i) field) =
      base (KeyMetadataMachine.idTape (tape i) field) :=
  finalTapes_frame dictionary base earlier key _ (notDictionary i field) (notAccumulator i field)

end

end PerfectCompleteness.CanonicalEndpointMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_CanonicalNamedGame
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalOnlineNames.onlineName_val _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.actualProjection_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightEquiv_apply _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CanonicalNamedGame

open CanonicalGame CanonicalKeys
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {v m n : Nat} {E I B : Type*} {V : I → Type*}
  [DecidableEq I] [∀ i, AddCommGroup (V i)]
  [∀ i, Module DirectionQuotient.F2 (V i)]
  {clauses : Fin m → SourceClause.NormalizedClause v}
  (F : BlockFamily clauses n E I V B)
  (occurrences : List E) (coverage : ∀ e, e ∈ occurrences)

def leftKeys : List (Key n) := occurrences.map (leftKey F)

def rightKeys : List (Key n) := occurrences.map (rightKey F)

omit [DecidableEq I] in
@[simp] theorem leftKeys_length : (leftKeys F occurrences).length = occurrences.length := by
  simp only [leftKeys, List.length_map]

@[simp] theorem rightKeys_length : (rightKeys F occurrences).length = occurrences.length := by
  simp only [rightKeys, List.length_map]

omit [DecidableEq I] in
include coverage in
theorem left_mem (x : LeftVertex F) : x.val ∈ leftKeys F occurrences := by
  obtain ⟨e, he⟩ := x.property
  exact List.mem_map.mpr ⟨e, coverage e, he⟩

include coverage in
theorem right_mem (y : RightVertex F) : y.val ∈ rightKeys F occurrences := by
  obtain ⟨e, he⟩ := y.property
  exact List.mem_map.mpr ⟨e, coverage e, he⟩

def leftEmbedding : LeftVertex F ↪ Fin occurrences.length where
  toFun x :=
    let named := CanonicalVertexNames.name (leftKeys F occurrences) x.val
      (left_mem F occurrences coverage x)
    ⟨named.val, by simpa only [leftKeys_length] using named.isLt⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    apply (CanonicalVertexNames.name_eq_iff (leftKeys F occurrences) x.val y.val
      (left_mem F occurrences coverage x) (left_mem F occurrences coverage y)).mp
    apply Fin.ext
    exact congrArg (fun i : Fin occurrences.length => i.val) h

def rightEmbedding : RightVertex F ↪ Fin occurrences.length where
  toFun y :=
    let named := CanonicalVertexNames.name (rightKeys F occurrences) y.val
      (right_mem F occurrences coverage y)
    ⟨named.val, by simpa only [rightKeys_length] using named.isLt⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    apply (CanonicalVertexNames.name_eq_iff (rightKeys F occurrences) x.val y.val
      (right_mem F occurrences coverage x) (right_mem F occurrences coverage y)).mp
    apply Fin.ext
    exact congrArg (fun i : Fin occurrences.length => i.val) h

omit [DecidableEq I] in
@[simp] theorem leftEmbedding_at_val (e : E) :
    (leftEmbedding F occurrences coverage (leftAt F e)).val =
      (BinaryNameSearch.payloads (CanonicalVertexNames.tokens (leftKeys F occurrences))).idxOf
        (CanonicalVertexNames.payload (leftKey F e)) := rfl

@[simp] theorem rightEmbedding_at_val (e : E) :
    (rightEmbedding F occurrences coverage (rightAt F e)).val =
      (BinaryNameSearch.payloads (CanonicalVertexNames.tokens (rightKeys F occurrences))).idxOf
        (CanonicalVertexNames.payload (rightKey F e)) := rfl

section CommonAlphabet

variable {E' A₁ A₂ : Type*} [Fintype E']
  [Fintype (LeftVertex F)] [Fintype (RightVertex F)] [Fintype A₁] [Fintype A₂]

def rename (G : OccurrenceGame E' (LeftVertex F) (RightVertex F) A₁ A₂) :
    OccurrenceGame E' (Fin occurrences.length) (Fin occurrences.length) A₁ A₂ :=
  OccurrenceVertexEmbedding.rename G
    (leftEmbedding F occurrences coverage) (rightEmbedding F occurrences coverage)

@[simp] theorem rename_occurrences
    (G : OccurrenceGame E' (LeftVertex F) (RightVertex F) A₁ A₂) :
    (rename F occurrences coverage G).occurrences = G.occurrences := rfl

@[simp] theorem rename_accepts
    (G : OccurrenceGame E' (LeftVertex F) (RightVertex F) A₁ A₂) :
    (rename F occurrences coverage G).accepts = G.accepts := rfl

theorem rename_value_eq [Nonempty A₁] [Nonempty A₂]
    (G : OccurrenceGame E' (LeftVertex F) (RightVertex F) A₁ A₂) :
    (rename F occurrences coverage G).value = G.value :=
  OccurrenceVertexEmbedding.value_eq G
    (leftEmbedding F occurrences coverage) (rightEmbedding F occurrences coverage)

end CommonAlphabet


variable [Finite I] [∀ i, Finite (V i)] [Finite B]
  [Fintype E] [Fintype (LeftVertex F)] [Fintype (RightVertex F)]
  [∀ x, Fintype (LeftLabel F x)] [∀ y, Fintype (RightLabel F y)]

local instance rightAlphabet_nonempty_rc6598c_2 (δ : ℚ) :
    Nonempty (Fin (CanonicalLocalCompletion.alphabet n δ)) :=
  ⟨⟨0, CanonicalLocalCompletion.alphabet_positive n δ⟩⟩
local instance leftAlphabet_nonempty_rc6598c_2 (δ : ℚ) :
    Nonempty (Fin (2 * CanonicalLocalCompletion.alphabet n δ)) :=
  ⟨⟨0, Nat.mul_pos (by decide) (CanonicalLocalCompletion.alphabet_positive n δ)⟩⟩
def completed (μ : FiniteDistribution E) (δ : ℚ) :=
  rename F occurrences coverage (CanonicalLocalCompletion.family F μ δ).game

omit [∀ y, Fintype (RightLabel F y)] in
@[simp] theorem completed_left (μ : FiniteDistribution E) (δ : ℚ)
    (e : E) (seed : Fin ((CanonicalLocalCompletion.family F μ δ).size e)) :
    (completed F occurrences coverage μ δ).left ⟨e, seed⟩ =
      leftEmbedding F occurrences coverage (leftAt F e) := rfl

omit [∀ y, Fintype (RightLabel F y)] in
@[simp] theorem completed_right (μ : FiniteDistribution E) (δ : ℚ)
    (e : E) (seed : Fin ((CanonicalLocalCompletion.family F μ δ).size e)) :
    (completed F occurrences coverage μ δ).right ⟨e, seed⟩ =
      rightEmbedding F occurrences coverage (rightAt F e) := rfl

end
end PerfectCompleteness.CanonicalNamedGame

end OAI
end


