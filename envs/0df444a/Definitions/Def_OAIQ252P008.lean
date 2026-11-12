-- Prove2me | Definitions.Def_OAIQ252P008
-- name    : OAIQ252P008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T07:40:46.667186+00:00
-- url     : https://prove2.me/theorems/0878b684-f02a-43c2-9fd9-23d9eeb1e8af
-- title:
--   Definitions bundle OAIQ252P008 of the split of OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 586 declarations of OpenAI's Lean: 344 definitions, 14 inductive types or structures, 11 instances and 217 theorems. The definitions and types are `OAI.PerfectCompleteness.CommonAccuracy.tolerance`, `OAI.PerfectCompleteness.CompletedEdgeMachine.Label`, `OAI.PerfectCompleteness.CompletedEdgeMachine.State`, `OAI.PerfectCompleteness.CompletedEdgeMachine.budget`, `OAI.PerfectCompleteness.CompletedEdgeMachine.clean`, `OAI.PerfectCompleteness.CompletedEdgeMachine.edge`, `OAI.PerfectCompleteness.CompletedEdgeMachine.edgeBits`, `OAI.PerfectCompleteness.CompletedEdgeMachine.edgeInTime`, `OAI.PerfectCompleteness.CompletedEdgeMachine.finalTapes`, `OAI.PerfectCompleteness.CompletedEdgeMachine.instruction`, `OAI.PerfectCompleteness.CompletedEdgeMachine.key`, `OAI.PerfectCompleteness.CompletedEdgeMachine.main`, `OAI.PerfectCompleteness.CompletedSignedLaw.Completed`, `OAI.PerfectCompleteness.CompletedSignedLaw.SignedCompleted`, `OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv`, `OAI.PerfectCompleteness.CompletedSignedLaw.law`, `OAI.PerfectCompleteness.CompletedSignedLaw.leftVertex_fintype`, `OAI.PerfectCompleteness.CompletedSignedLaw.rightVertex_fintype`, `OAI.PerfectCompleteness.CompletedVisitOrder.completedOrder`, `OAI.PerfectCompleteness.CompletedVisitOrder.leftVertex_fintype`, `OAI.PerfectCompleteness.CompletedVisitOrder.localOrder`, `OAI.PerfectCompleteness.CompletedVisitOrder.rawOrder`, `OAI.PerfectCompleteness.CompletedVisitOrder.rightVertex_fintype`, `OAI.PerfectCompleteness.CompletionSoundness.LegalProjectionGame.liftStrategy`, `OAI.PerfectCompleteness.CompletionSoundness.LegalProjectionGame.roundStrategy`, `OAI.PerfectCompleteness.CompletionSoundness.LegalProjectionGame.value`, `OAI.PerfectCompleteness.CoordinateReplacement.ratio`, `OAI.PerfectCompleteness.CutSamplerLocality.ZeroAtClean`, `OAI.PerfectCompleteness.CutSamplerLocality.subTape`, `OAI.PerfectCompleteness.CutSamplerRefinement.zeroFactor`, `OAI.PerfectCompleteness.DecoderSourcePullback.relativeCut`, `OAI.PerfectCompleteness.DecoderSourcePullback.selectedCut`, `OAI.PerfectCompleteness.DependentDecoderSampling.seedLaw`, `OAI.PerfectCompleteness.DependentPredictionDifference.law`, `OAI.PerfectCompleteness.DescendingRows.commonCutoff`, `OAI.PerfectCompleteness.DescendingRows.lowerChoice`, `OAI.PerfectCompleteness.DescriptorKeyTemplate.Template`, `OAI.PerfectCompleteness.DescriptorKeyTemplate.occurrence`, `OAI.PerfectCompleteness.DescriptorKeyTemplate.ofDescriptor`, `OAI.PerfectCompleteness.DescriptorKeyTemplate.ofInput` and 318 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `PerfectCompleteness_Algebra_MatrixInverseConstantsLemmas`, `PerfectCompleteness_Algebra_UniformLinearImage`, `PerfectCompleteness_Construction_AscendingBranchingLemmas`, `PerfectCompleteness_Construction_CutChildGrouping`, `PerfectCompleteness_Construction_OriginalChildBlocks`, `PerfectCompleteness_Construction_OriginalChildScalars`, `PerfectCompleteness_Construction_SourceQuestionOrderLemmas`, `PerfectCompleteness_Construction_SourceQuestionPositionSplit`, `PerfectCompleteness_Construction_TreeCanonical`, `PerfectCompleteness_Decoding_DecoderSourcePullback`, `PerfectCompleteness_Decoding_DependentDecoderSampling`, `PerfectCompleteness_Decoding_HierarchicalAllDecoderTables`, `PerfectCompleteness_Decoding_LowerDirectionFiber`, `PerfectCompleteness_Foundations_CommonAccuracy`, `PerfectCompleteness_Foundations_CoordinateReplacementLemmas`, `PerfectCompleteness_Foundations_CutTerminalSplit`, `PerfectCompleteness_Foundations_DependentPredictionDifferenceLemmas`, `PerfectCompleteness_Foundations_DescriptorKeyTemplate`, `PerfectCompleteness_Foundations_HierarchicalArrays`, `PerfectCompleteness_Foundations_HierarchicalFrozenTablesLemmas`, `PerfectCompleteness_Foundations_HierarchicalProjectedSliceLemmas`, `PerfectCompleteness_Foundations_LinearEvaluationLemmas`, `PerfectCompleteness_Foundations_OriginalBelowCut`, `PerfectCompleteness_Foundations_RawOccurrenceOrderLemmas`, `PerfectCompleteness_Foundations_SignedScheduleIndex`, `PerfectCompleteness_Foundations_SignedTupleLayout`, `PerfectCompleteness_Foundations_SignedTupleSemantics`, `PerfectCompleteness_Foundations_SourceTupleData`, `PerfectCompleteness_Foundations_SourceTuplePlacement`, `PerfectCompleteness_Foundations_SourceTupleResetPlacementLemmas`, `PerfectCompleteness_Foundations_SourceVisitOrder`, `PerfectCompleteness_Machines_CompletedEdgeMachine`, `PerfectCompleteness_Machines_DescriptorProjectionMachine`, `PerfectCompleteness_Machines_ExactTargetOdometer`, `PerfectCompleteness_Machines_ExactTargetOnlineEncoding`, `PerfectCompleteness_Machines_FiniteConstraintMachine`, `PerfectCompleteness_Machines_MetadataFreeTapeLemmas`, `PerfectCompleteness_Machines_OwnInputAffineSliceLemmas`, `PerfectCompleteness_Machines_OwnInputReferenceLemmas`, `PerfectCompleteness_Machines_SignedDescriptorStageMachine`, `PerfectCompleteness_Machines_SignedTupleBodyMachine`, `PerfectCompleteness_Machines_SignedTupleCleanupMachineLemmas`, `PerfectCompleteness_Machines_SourceClauseLookupMachine`, `PerfectCompleteness_Machines_SourceClauseReaderMachineLemmas`, `PerfectCompleteness_Machines_SourceCoordinateMachine`, `PerfectCompleteness_Machines_SourceTupleMachine`, `PerfectCompleteness_Machines_SourceTupleResetMachine`, `PerfectCompleteness_Reduction_CompletedVisitOrder`, `PerfectCompleteness_Reduction_CompletionAlphabetLemmas`, `PerfectCompleteness_Reduction_CompletionSoundness`, `PerfectCompleteness_Reduction_ExactPreliminaryTarget`, `PerfectCompleteness_Reduction_FinitePreliminaryCompletion`, `PerfectCompleteness_Reduction_FixedQueryCodec`, `PerfectCompleteness_Reduction_FixedRows`, `PerfectCompleteness_Reduction_OccurrenceGame`, `PerfectCompleteness_Reduction_SignedCompletionSchedule`, `PerfectCompleteness_Sampling_CompletedSignedLaw`, `PerfectCompleteness_Sampling_CutSamplerLocality`, `PerfectCompleteness_Sampling_CutSamplerRefinement`, `PerfectCompleteness_Sampling_MetadataFreeLaw`, `PerfectCompleteness_Sampling_MetadataFreeSampler`, `PerfectCompleteness_Sampling_PreliminarySampler`, `PerfectCompleteness_Sampling_RationalFiniteLawLemmas`, `PerfectCompleteness_Sampling_RecordSeedSamplingLemmas`, `PerfectCompleteness_Sampling_SamplerCardinalityLemmas`, `PerfectCompleteness_Sampling_WholeArraySampler`, `UniqueGames_Foundations_SamplingLemmas`, `UniqueGames_Machines_MachineCeilingPower`, `UniqueGames_Machines_MachineCloudPrefix`, `UniqueGames_Machines_MachineDrainManyLemmas`, `UniqueGames_Machines_MachineLemmas`, `UniqueGames_Machines_MachinePaddedExpanderFamilyBoundsLemmas`, `UniqueGames_Machines_MachineRegularOriginalBody`, `UniqueGames_Machines_MachineRegularOwnerCleanup`, `UniqueGames_PCP_FinalTableFormula`, `UniqueGames_PCP_HonestTestLemmas`, `UniqueGames_PCP_SourceHeaderCounts`, `UniqueGames_PCP_SourceOccurrences`, `UniqueGames_PCP_SourceQueryOrderLemmas`, `UniqueGames_PCP_SourceSignaturePrepareLemmas`, `UniqueGames_PCP_TableIteration`.
--
--   **Imports.** It imports the published bundle `Def_PerfectCompleteness`; the bundles `OAIQ252P003` and `OAIQ252P004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ252P012`, `OAIQ252P013`, `OAIQ252P014` and `OAIQ252P015`; the proofs of `OAI.PerfectCompleteness.BucketQuotientAgreement.agreement_eq_nonzeroAgreement`, `OAI.PerfectCompleteness.BucketQuotientAgreement.directionCollision_eq`, `OAI.PerfectCompleteness.ChildBilinearCollisionTransfer.marked_restricted_le_uniform_full` and `OAI.PerfectCompleteness.HeterogeneousAdviceFamily.J_probability_ge`.
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
import Definitions.Def_OAIQ252P003
import Definitions.Def_OAIQ252P004

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_SamplingLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
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

theorem expectation_uniform {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    (uniform Ω).expectation f = (∑ x, f x) / (Fintype.card Ω : ℝ) := by
  unfold expectation uniform
  rw [← Finset.mul_sum]
  simp [div_eq_mul_inv, mul_comm]

end
end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

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

/-!
Verifier-defined NP over finite bitstring machines. This definition does not
mention SAT. Inputs and witnesses use a fixed explicit framing, verifiers return
one Boolean symbol, and all stacks have finite alphabets. The Cook–Levin target
separately requires an actual polynomial-time machine producing the established
`formulaBits` serialization, in addition to satisfiability equivalence.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin

/-- The demanded Cook–Levin endpoint: both the SAT equivalence and an actual
machine producing the fixed existing unary-token 3CNF encoding. This structure
contains obligations; its inhabitance is not assumed or asserted here. -/
structure PolynomialThreeSATReduction (language : List Bool → Prop) where
  reduce : List Bool → Target.Formula
  computation : Turing.TM2ComputableInPolyTime id formulaBits reduce
  correct : ∀ input, language input ↔ (reduce input).Satisfiable

end UniqueGamesTheorem.Foundations.Complexity.CookLevin

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_LinearEvaluationLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Integration.CutoffBudget

open scoped BigOperators

theorem cutoffSum_le (r : Nat) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    cutoffSum r ρ ≤
      (r + 1 : ℝ) * (2 : ℝ) ^ (30 * r * r) * ρ ^ ((1 : ℝ) / 4) := by
  have hroot : 0 ≤ ρ ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hρ.le _
  have hrho : ρ ≤ ρ ^ ((1 : ℝ) / 4) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge hρ hρ1
        (by norm_num : (1 : ℝ) / 4 ≤ 1))
  have hone : (1 : ℝ) ≤ 2 ^ (30 * r * r) := one_le_pow₀ (by norm_num)
  calc
    cutoffSum r ρ ≤ ∑ _d ∈ Finset.range (r + 1),
        (2 : ℝ) ^ (30 * r * r) * ρ ^ ((1 : ℝ) / 4) := by
      unfold cutoffSum
      apply Finset.sum_le_sum
      intro d hd
      have hdr : d ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
      split_ifs
      · exact hrho.trans (by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hone hroot)
      · apply mul_le_mul_of_nonneg_right _ hroot
        apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        exact Nat.mul_le_mul (Nat.mul_le_mul_left 30 hdr) hdr
    _ = _ := by simp [mul_assoc]

theorem rho_real_bounds {r s : Nat} (hs : r + 1 < s) :
    0 < (FinalParameters.rho r s : ℝ) ∧ (FinalParameters.rho r s : ℝ) < 1 := by
  constructor
  · exact_mod_cast FinalParameters.rho_pos r s
  · have hq : FinalParameters.rho r s < 1 := by
      unfold FinalParameters.rho
      exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    exact_mod_cast hq

theorem cutoffSum_le_budget {r s : Nat} {δ : ℚ} (hs : r + 1 < s)
    (hbudget : (FinalParameters.levelConstant r : ℝ) *
      (FinalParameters.rho r s : ℝ) ^ ((1 : ℝ) / 4) ≤ (δ : ℝ) / 8) :
    cutoffSum r (FinalParameters.rho r s : ℝ) ≤ (δ : ℝ) / 8 := by
  have hρ := rho_real_bounds hs
  apply (cutoffSum_le r hρ.1 hρ.2.le).trans
  simpa [FinalParameters.levelConstant, pow_two, mul_assoc] using hbudget

theorem exists_symbol_dimension_cutoff (r : Nat) {δ : ℚ} (hδ : 0 < δ) :
    ∃ s : Nat, r + 1 < s ∧
      cutoffSum r (FinalParameters.rho r s : ℝ) ≤ (δ : ℝ) / 8 := by
  obtain ⟨s, hs, hbudget⟩ := RealBounds.exists_symbol_dimension_real r hδ
  exact ⟨s, hs, cutoffSum_le_budget hs hbudget⟩

end UniqueGamesTheorem.Integration.CutoffBudget

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_MatrixInverseConstantsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.MatrixInverseConstants

open UniqueGamesTheorem.Appendix UniqueGamesTheorem.Fourier UniqueGamesTheorem.Integration

theorem exists_cutoff_density {η : ℝ} (hη : 0 < η) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      MatrixLevelBridge.levelCutoffConstant r ρ +
        RankLevelFilter.node (r + 1) < η := by
  obtain ⟨q, hq, hqη⟩ := exists_pos_rat_lt hη
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (show 0 < η / 2 by positivity)
    (by norm_num : (1 / 2 : ℝ) < 1)
  let r : ℕ := n + 1
  have hn' : RankLevelFilter.node n < η / 2 := by
    simpa only [RankLevelFilter.node_eq_inv_pow, one_div, inv_pow] using hn
  have htail : RankLevelFilter.node (r + 1) < η / 2 :=
    (RankLevelFilter.node_antitone (show n ≤ r + 1 by dsimp [r]; omega)).trans_lt hn'
  obtain ⟨s, hs, hcut⟩ := CutoffBudget.exists_symbol_dimension_cutoff r hq
  have hρ := CutoffBudget.rho_real_bounds hs
  refine ⟨r, by dsimp [r]; omega, (FinalParameters.rho r s : ℝ), hρ.1, hρ.2, ?_⟩
  have hcut' :
      MatrixLevelBridge.levelCutoffConstant r (FinalParameters.rho r s : ℝ) ≤
        (q : ℝ) / 8 := by
    simpa only [MatrixLevelBridge.levelCutoffConstant, CutoffBudget.cutoffSum] using hcut
  linarith

end PerfectCompleteness.MatrixInverseConstants

end

section

namespace PerfectCompleteness.LowerRankParameters

open UniqueGamesTheorem.Appendix UniqueGamesTheorem.Fourier

theorem exists_lower_parameters {η : ℝ} (hη : 0 < η) :
    ∃ r m s rowMinimum : Nat, 1 ≤ r ∧ 0 < m ∧ 1 ≤ s ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
        MatrixLevelBridge.levelCutoffConstant r ρ + RankLevelFilter.node (r + 1) < η ∧
        (∀ ℓ, rowMinimum ≤ ℓ → 2 * m + r ≤ ℓ) ∧
        ∀ s', s ≤ s' →
          (2 : ℝ) ^ m / (2 : ℝ) ^ (s' - 2 * r) +
            (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) < ρ := by
  obtain ⟨r, hr, ρ, hρ, hρ', hcut⟩ := MatrixInverseConstants.exists_cutoff_density hη
  obtain ⟨m, s, hm, hs, herror⟩ := exists_cross_parameters r hρ
  exact ⟨r, m, s, 2 * m + r, hr, hm, hs, ρ, hρ, hρ', hcut,
    fun _ h => h, herror⟩

end PerfectCompleteness.LowerRankParameters

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_UniformLinearImage
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.UniformLinearImage

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

noncomputable section

section Product

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

theorem law_uniform [∀ i, Nonempty (Ω i)] :
    FiniteProduct.law (fun i => FiniteDistribution.uniform (Ω i)) =
      FiniteDistribution.uniform ((i : I) → Ω i) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change (∏ i, 1 / (Fintype.card (Ω i) : ℝ)) =
    1 / (Fintype.card ((i : I) → Ω i) : ℝ)
  simp only [Fintype.card_pi, Nat.cast_prod, Finset.prod_div_distrib,
    Finset.prod_const_one]

end Product
end
end PerfectCompleteness.UniformLinearImage

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_OccurrenceGame
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
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

theorem success_le_one (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) : G.success strategy ≤ 1 :=
  G.occurrences.probability_le_one _


variable [Nonempty A₁] [Nonempty A₂]

theorem exists_optimal_strategy (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) :
    ∃ strategy : Strategy Q₁ Q₂ A₁ A₂, G.success strategy = G.value := by
  classical
  obtain ⟨strategy, _, h⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Strategy Q₁ Q₂ A₁ A₂))) Finset.univ_nonempty G.success
  exact ⟨strategy, h.symm⟩

theorem value_le_one (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) : G.value ≤ 1 :=
  (G.value_le_iff 1).2 G.success_le_one

end OccurrenceGame
end
end PerfectCompleteness

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_CoordinateReplacementLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CoordinateReplacement

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open FiniteProduct

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

def ratio (P Q : (i : I) → FiniteDistribution (Ω i)) (i : I) (a : Ω i) : ℝ :=
  (Q i).weight a / (P i).weight a

omit [Fintype I] [DecidableEq I] in
theorem ratio_nonnegative (P Q : (i : I) → FiniteDistribution (Ω i))
    (i : I) (a : Ω i) : 0 ≤ ratio P Q i a :=
  div_nonneg ((Q i).nonnegative a) ((P i).nonnegative a)

omit [Fintype I] [DecidableEq I] in
theorem weight_mul_ratio_of_support (P Q : (i : I) → FiniteDistribution (Ω i))
    (support : ∀ i a, (P i).weight a = 0 → (Q i).weight a = 0)
    (i : I) (a : Ω i) :
    (P i).weight a * ratio P Q i a = (Q i).weight a := by
  by_cases hzero : (P i).weight a = 0
  · simp only [hzero, zero_mul, support i a hzero]
  · exact mul_div_cancel₀ ((Q i).weight a) hzero

omit [Fintype I] [DecidableEq I] in
theorem ratio_mean_one_of_support (P Q : (i : I) → FiniteDistribution (Ω i))
    (support : ∀ i a, (P i).weight a = 0 → (Q i).weight a = 0) (i : I) :
    (P i).expectation (ratio P Q i) = 1 := by
  change (∑ a, (P i).weight a * ratio P Q i a) = 1
  simp_rw [weight_mul_ratio_of_support P Q support]
  exact (Q i).normalized


end
end PerfectCompleteness.CoordinateReplacement



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_AscendingBranchingLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.DescendingRows

open scoped BigOperators Classical
open UniqueGamesTheorem.Appendix UniqueGamesTheorem.Fourier
open UpperParameterScalars

noncomputable section

theorem exclusion_exists {threshold : ℝ} (h : 0 < threshold) :
    Nonempty (Exclusion threshold) := by
  obtain ⟨r, m, s, rowMin, hr, hm, hs, ρ, hρ, hρ', hcut, hrows, herror⟩ :=
    LowerRankParameters.exists_lower_parameters h
  exact ⟨⟨r, m, s, rowMin, ρ, hr, hm, hs, hρ, hρ', hcut, hrows, herror⟩⟩

variable {κ α η : ℝ} (hκ : 0 < κ) (hα : 0 < α) (hη : 0 < η)

def lowerChoice (r ℓ : Nat) : Exclusion (gamma κ α η r ℓ ^ 2 / 8) :=
  Classical.choice (exclusion_exists (by
    have := gamma_pos hκ hα hη r ℓ
    positivity))

def commonCutoff (r depth : Nat) (rows : Nat → Nat) : Nat :=
  1 + ∑ i : Fin depth, (lowerChoice hκ hα hη r (rows i.val)).cutoff

theorem commonCutoff_pos (r depth : Nat) (rows : Nat → Nat) :
    1 ≤ commonCutoff hκ hα hη r depth rows := Nat.le_add_right _ _

end
end PerfectCompleteness.DescendingRows

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_TreeCanonical
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
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

def key (side : CanonicalKeys.Side)
    (slots : RecursiveSpaces.Slots branch n → Fin t → Slot) (f : Domain slots → Y) :
    CanonicalKeys.Key (locationCount branch n t) :=
  CanonicalKeys.key side (numberedSlots slots) (numberedFunction slots f)

end

end PerfectCompleteness.TreeCanonical

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalArrays
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HierarchicalArrays

open TreeSourceSpaces

variable {branch : Nat → Nat} {n t : Nat}

variable {v m : Nat}

noncomputable section

def numberedEndpoints
    (endpoints : RecursiveSpaces.Slots branch n → Fin t → SourceKeys.Endpoint v m) :
    Fin (TreeCanonical.locationCount branch n t) → SourceKeys.Endpoint v m :=
  fun j => endpoints ((TreeCanonical.numbering branch n t).symm j).1
    ((TreeCanonical.numbering branch n t).symm j).2

def presentation (clauses : Fin m → SourceClause.NormalizedClause v)
    (endpoints : RecursiveSpaces.Slots branch n → Fin t → SourceKeys.Endpoint v m)
    (rows : Nat → Nat) (arrays : Arrays (sourceSlots clauses endpoints) rows) :
    SourceCompleteness.Presentation clauses (TreeCanonical.locationCount branch n t)
      (Output branch n rows) where
  endpoints := numberedEndpoints endpoints
  joint := TreeCanonical.numberedFunction (sourceSlots clauses endpoints) (fullJoint arrays)

end

end PerfectCompleteness.HierarchicalArrays

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

instance assembledFintype : Fintype (Assembled (C := C) slots rows) := Fintype.ofFinite _

end
end PerfectCompleteness.CutChildGrouping

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

/-- Exact execution of all concrete drains in the supplied ambient program. -/
theorem trace (chosen : List K) (labels : Label chosen → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction chosen labels exit l)
    (base : Tapes K) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps chosen base]
      (some ⟨entry chosen labels exit, (ambient, register), base⟩) =
    some ⟨exit, (ambient, finalRegister chosen register), finalTapes chosen base⟩ := by
  have run := MachineFiniteSequence.trace
    (LocalLabel := LocalLabel (K := K)) (main := fun _ => ())
    (localInstruction := localInstruction (σ := σ)) (result := result) (cost := cost)
    program (fun _ : Data K => True) (fun data => (ambient, data.2)) (fun data => data.1)
    chosen (by intros; trivial)
    (by
      intro source _ localLabels localExit atLocal data _
      rcases data with ⟨tapes, reg⟩
      simpa only [cost, result, Function.update_eq_self] using
        MachineDrain.drainTrace source (localLabels ()) localExit program (atLocal ())
          tapes (tapes source) ambient reg)
    labels exit atLabels (base, register) trivial
  simpa only [sequence_steps, sequence_result, entry] using run

end UniqueGamesTheorem.Foundations.Complexity.MachineDrainMany

/-!
Preserved comparisons of actual field stacks and their finite equality profile.
All whole-word equalities below are specifications of finite-head comparison.
-/

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

variable {σ : Type}

def compareLoop : TM2.Stmt Alphabet Label (State σ) :=
  .pop .work (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.peek .power (fun state head => (state.1, head))
        (.branch (fun state => state.2.getD false)
          (.pop .power (fun state _ => (state.1, none))
            (.push .saved (fun _ => true) (.goto fun _ => .compare)))
          (.load (fun state => ((state.1.1, true), none)) (.goto fun _ => .compare))))
      (.load (fun state => (state.1, none)) (.goto fun _ => .restore)))

/-- Each input tally emits the fixed block of `g` tallies. The delimiter
starts the new power and the level is incremented by an actual push. -/
def scaleLoop (g : Nat) : TM2.Stmt Alphabet Label (State σ) :=
  .pop .power (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (Reduction.MachineSubstitution.pushWord .product (List.replicate g true)
        (.goto fun _ => .scale))
      (.push .power (fun _ => false)
        (.push .level (fun _ => true)
          (.load (fun state => (state.1, none)) (.goto fun _ => .transfer)))))

def program (g : Nat) : Label → TM2.Stmt Alphabet Label (State σ)
  | .init => .push .power (fun _ => false) (.push .power (fun _ => true)
      (.push .level (fun _ => false) (.goto fun _ => .fuelFirst)))
  | .fuelFirst => Reduction.MachineTransfer.loopAt
      .input .spare id false .fuelFirst (some .fuelSecond)
  | .fuelSecond => MachineCopy.forkLoop
      .spare .input .fuel false .fuelSecond (some .guard)
  | .guard => MachineUnaryCounter.guard .fuel .copyFirst .cleanup
  | .copyFirst => Reduction.MachineTransfer.loopAt
      .input .spare id false .copyFirst (some .copySecond)
  | .copySecond => MachineCopy.forkLoop
      .spare .input .work false .copySecond (some .compare)
  | .compare => compareLoop
  | .restore => Reduction.MachineTransfer.loopAt
      .saved .power id false .restore (some .decide)
  | .decide => .branch (fun state => state.1.2)
      (.load (fun state => ((state.1.1, false), none)) (.goto fun _ => .scale))
      (.load (fun state => ((state.1.1, false), none)) (.goto fun _ => .cleanup))
  | .scale => scaleLoop g
  | .transfer => Reduction.MachineTransfer.loopAt
      .product .power id false .transfer (some .guard)
  | .cleanup => MachineDrain.drain .fuel .cleanup none

end UniqueGamesTheorem.Foundations.Complexity.MachineCeilingPower

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_CompletionSoundness
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FlexibleLocalCompletion.family_map _root_.OAI.PerfectCompleteness.FlexibleLocalCompletion.family_size _root_.OAI.PerfectCompleteness.FlexibleLocalCompletion.localLegalEquiv_apply_val _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.LocalCompletionGame.family_map _root_.OAI.PerfectCompleteness.LocalCompletionGame.family_size _root_.OAI.PerfectCompleteness.LocalCompletionGame.localLegalEquiv_apply_val _root_.OAI.PerfectCompleteness.OccurrenceVertexEmbedding.restrict_extend _root_.OAI.PerfectCompleteness.OccurrenceVertexEmbedding.success_restrict _root_.OAI.PerfectCompleteness.OccurrenceVertexEmbedding.wins_restrict _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SourceGame.questionGame_success _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
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

theorem sigmaLaw_probability (μ : FiniteDistribution E)
    (ν : ∀ e, FiniteDistribution (Seed e)) (event : (Σ e, Seed e) → Bool) :
    (sigmaLaw μ ν).probability event =
      μ.expectation (fun e => (ν e).probability (fun seed => event ⟨e, seed⟩)) := by
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
    sigmaLaw, Fintype.sum_sigma, Finset.mul_sum, mul_ite, mul_zero]

theorem sigmaLaw_probability_first (μ : FiniteDistribution E)
    (ν : ∀ e, FiniteDistribution (Seed e)) (event : E → Bool) :
    (sigmaLaw μ ν).probability (fun es => event es.1) = μ.probability event := by
  rw [sigmaLaw_probability]
  simp only [FiniteDistribution.expectation, FiniteDistribution.probability]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : event e = true <;> simp [he, (ν e).normalized]

end SeedLaws

theorem probability_uniform_eq_uniformProbability {Ω : Type*}
    [Fintype Ω] [Nonempty Ω] (event : Ω → Prop) :
    (FiniteDistribution.uniform Ω).probability (fun x => decide (event x)) =
      uniformProbability event := by
  calc
    _ = (FiniteDistribution.uniform Ω).expectation
        (fun x => if event x then (1 : ℝ) else 0) := by
      unfold FiniteDistribution.probability FiniteDistribution.expectation
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : event x <;> simp [hx]
    _ = (∑ x, if event x then (1 : ℝ) else 0) / (Fintype.card Ω : ℝ) :=
      FiniteDistribution.expectation_uniform _
    _ = uniformProbability event := by
      simp only [uniformProbability, Fintype.card_subtype, Finset.sum_boole]

theorem probability_decide_const {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) (P : Prop) :
    μ.probability (fun _ => decide P) = if P then 1 else 0 := by
  by_cases h : P <;> simp [h]

theorem seed_acceptance_le {L R A B Ω : Type*} [Fintype Ω]
    (ν : FiniteDistribution Ω) (legalL : L ↪ A) (legalR : R ↪ B)
    (defaultL : L) (defaultR : R) (p : L → R) (complete : Ω → A → B)
    (agrees : ∀ seed l, complete seed (legalL l) = legalR (p l))
    (ε : ℝ) (hε : 0 ≤ ε)
    (marginal : ∀ a, a ∉ Set.range legalL → ∀ b,
      ν.probability (fun seed => decide (complete seed a = b)) ≤ ε)
    (a : A) (b : B) :
    ν.probability (fun seed => decide (complete seed a = b)) ≤
      (if p (roundLabel legalL defaultL a) = roundLabel legalR defaultR b then 1 else 0) + ε := by
  by_cases ha : a ∈ Set.range legalL
  · obtain ⟨l, rfl⟩ := ha
    have hdom : ν.probability (fun seed => decide (complete seed (legalL l) = b)) ≤
        ν.probability (fun _ =>
          decide (p (roundLabel legalL defaultL (legalL l)) =
            roundLabel legalR defaultR b)) := by
      apply ν.probability_mono
      intro seed hwin
      have hw : complete seed (legalL l) = b := of_decide_eq_true hwin
      have hb : legalR (p l) = b := (agrees seed l).symm.trans hw
      apply decide_eq_true_iff.mpr
      rw [roundLabel_legal, ← hb, roundLabel_legal]
    rw [probability_decide_const] at hdom
    exact hdom.trans (le_add_of_nonneg_right hε)
  · have h := marginal a ha b
    have hind : (0 : ℝ) ≤
        if p (roundLabel legalL defaultL a) = roundLabel legalR defaultR b then 1 else 0 := by
      split <;> norm_num
    exact h.trans (le_add_of_nonneg_left hind)

namespace LegalProjectionGame

variable {E Q₁ Q₂ : Type*} {L : Q₁ → Type*} {R : Q₂ → Type*}
  [Fintype E] (G : LegalProjectionGame E Q₁ Q₂ L R)

section Value
variable [Fintype Q₁] [Fintype Q₂] [∀ x, Fintype (L x)] [∀ y, Fintype (R y)]
  [∀ x, Nonempty (L x)] [∀ y, Nonempty (R y)]

def value : ℝ := Finset.univ.sup' Finset.univ_nonempty G.success

theorem success_le_value (s : LegalStrategy L R) : G.success s ≤ G.value :=
  Finset.le_sup' G.success (Finset.mem_univ s)

theorem exists_optimal_strategy : ∃ s : LegalStrategy L R, G.success s = G.value := by
  obtain ⟨s, _, hs⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (LegalStrategy L R))) Finset.univ_nonempty G.success
  exact ⟨s, hs.symm⟩

end Value

section Completion
variable [Fintype Q₁] [Fintype Q₂]
  {A B : Type*} [Fintype A] [Fintype B]
  {Seed : E → Type*} [∀ e, Fintype (Seed e)]

theorem completed_success (ν : ∀ e, FiniteDistribution (Seed e))
    (complete : ∀ e, Seed e → A → B) (s : Strategy Q₁ Q₂ A B) :
    (G.completedGame ν complete).success s =
      G.occurrences.expectation (fun e => (ν e).probability
        (fun seed => decide (complete e seed (s.1 (G.left e)) = s.2 (G.right e)))) := by
  change (sigmaLaw G.occurrences ν).probability _ = _
  exact sigmaLaw_probability G.occurrences ν _

def roundStrategy (legalL : ∀ x, L x ↪ A) (legalR : ∀ y, R y ↪ B)
    (defaultL : ∀ x, L x) (defaultR : ∀ y, R y)
    (s : Strategy Q₁ Q₂ A B) : LegalStrategy L R :=
  (fun x => roundLabel (legalL x) (defaultL x) (s.1 x),
   fun y => roundLabel (legalR y) (defaultR y) (s.2 y))

def liftStrategy (legalL : ∀ x, L x ↪ A) (legalR : ∀ y, R y ↪ B)
    (s : LegalStrategy L R) : Strategy Q₁ Q₂ A B :=
  (fun x => legalL x (s.1 x), fun y => legalR y (s.2 y))

theorem completed_success_le (ν : ∀ e, FiniteDistribution (Seed e))
    (complete : ∀ e, Seed e → A → B)
    (legalL : ∀ x, L x ↪ A) (legalR : ∀ y, R y ↪ B)
    (defaultL : ∀ x, L x) (defaultR : ∀ y, R y)
    (agrees : ∀ e seed l, complete e seed (legalL (G.left e) l) =
      legalR (G.right e) (G.projection e l))
    (ε : E → ℝ) (hε : ∀ e, 0 ≤ ε e)
    (marginal : ∀ e a, a ∉ Set.range (legalL (G.left e)) → ∀ b,
      (ν e).probability (fun seed => decide (complete e seed a = b)) ≤ ε e)
    (s : Strategy Q₁ Q₂ A B) :
    (G.completedGame ν complete).success s ≤
      G.success (roundStrategy legalL legalR defaultL defaultR s) + G.occurrences.expectation ε := by
  rw [G.completed_success]
  unfold FiniteDistribution.expectation success wins FiniteDistribution.probability
  calc
    _ ≤ ∑ e, G.occurrences.weight e *
        ((if G.projection e (roundLabel (legalL (G.left e)) (defaultL (G.left e))
            (s.1 (G.left e))) = roundLabel (legalR (G.right e)) (defaultR (G.right e))
            (s.2 (G.right e)) then 1 else 0) + ε e) := by
      apply Finset.sum_le_sum
      intro e _
      exact mul_le_mul_of_nonneg_left
        (seed_acceptance_le (ν e) (legalL (G.left e)) (legalR (G.right e))
          (defaultL (G.left e)) (defaultR (G.right e)) (G.projection e) (complete e)
          (agrees e) (ε e) (hε e) (marginal e) _ _) (G.occurrences.nonnegative e)
    _ = _ := by
      simp only [roundStrategy, mul_add, Finset.sum_add_distrib, mul_ite,
        mul_one, mul_zero]
      apply congrArg (fun z : ℝ => z + ∑ e, G.occurrences.weight e * ε e)
      apply Finset.sum_congr rfl
      intro e _
      by_cases h : G.projection e
          (roundLabel (legalL (G.left e)) (defaultL (G.left e)) (s.1 (G.left e))) =
          roundLabel (legalR (G.right e)) (defaultR (G.right e)) (s.2 (G.right e))
      · simp [h]
      · simp [h]

theorem completed_success_lift (ν : ∀ e, FiniteDistribution (Seed e))
    (complete : ∀ e, Seed e → A → B)
    (legalL : ∀ x, L x ↪ A) (legalR : ∀ y, R y ↪ B)
    (agrees : ∀ e seed l, complete e seed (legalL (G.left e) l) =
      legalR (G.right e) (G.projection e l))
    (s : LegalStrategy L R) :
    (G.completedGame ν complete).success (liftStrategy legalL legalR s) = G.success s := by
  change (sigmaLaw G.occurrences ν).probability
    (fun es => decide (complete es.1 es.2 (legalL (G.left es.1) (s.1 (G.left es.1))) =
      legalR (G.right es.1) (s.2 (G.right es.1)))) = G.success s
  have hpoint : (fun es : Σ e, Seed e =>
      decide (complete es.1 es.2 (legalL (G.left es.1) (s.1 (G.left es.1))) =
        legalR (G.right es.1) (s.2 (G.right es.1)))) =
      (fun es => G.wins s es.1) := by
    funext es
    simp only [agrees, wins, (legalR (G.right es.1)).injective.eq_iff]
  rw [hpoint, sigmaLaw_probability_first]
  rfl

variable [∀ x, Fintype (L x)] [∀ y, Fintype (R y)]
  [∀ x, Nonempty (L x)] [∀ y, Nonempty (R y)] [Nonempty A] [Nonempty B]

theorem completed_value_le (ν : ∀ e, FiniteDistribution (Seed e))
    (complete : ∀ e, Seed e → A → B)
    (legalL : ∀ x, L x ↪ A) (legalR : ∀ y, R y ↪ B)
    (agrees : ∀ e seed l, complete e seed (legalL (G.left e) l) =
      legalR (G.right e) (G.projection e l))
    (ε : E → ℝ) (hε : ∀ e, 0 ≤ ε e)
    (marginal : ∀ e a, a ∉ Set.range (legalL (G.left e)) → ∀ b,
      (ν e).probability (fun seed => decide (complete e seed a = b)) ≤ ε e) :
    (G.completedGame ν complete).value ≤ G.value + G.occurrences.expectation ε := by
  apply ((G.completedGame ν complete).value_le_iff _).2
  intro s
  let defaultL : ∀ x, L x := fun x => Classical.choice inferInstance
  let defaultR : ∀ y, R y := fun y => Classical.choice inferInstance
  exact (G.completed_success_le ν complete legalL legalR defaultL defaultR agrees ε hε marginal s).trans
    (add_le_add (G.success_le_value _) (le_refl _))

theorem completed_value_le_of_bound (ν : ∀ e, FiniteDistribution (Seed e))
    (complete : ∀ e, Seed e → A → B)
    (legalL : ∀ x, L x ↪ A) (legalR : ∀ y, R y ↪ B)
    (agrees : ∀ e seed l, complete e seed (legalL (G.left e) l) =
      legalR (G.right e) (G.projection e l))
    (ε : E → ℝ) (hε : ∀ e, 0 ≤ ε e)
    (marginal : ∀ e a, a ∉ Set.range (legalL (G.left e)) → ∀ b,
      (ν e).probability (fun seed => decide (complete e seed a = b)) ≤ ε e)
    (δ : ℝ) (hδ : ∀ e, ε e ≤ δ) :
    (G.completedGame ν complete).value ≤ G.value + δ := by
  apply (G.completed_value_le ν complete legalL legalR agrees ε hε marginal).trans
  apply add_le_add (le_refl G.value)
  unfold FiniteDistribution.expectation
  calc
    _ ≤ ∑ e, G.occurrences.weight e * δ := by
      apply Finset.sum_le_sum
      intro e _
      exact mul_le_mul_of_nonneg_left (hδ e) (G.occurrences.nonnegative e)
    _ = δ := by rw [← Finset.sum_mul, G.occurrences.normalized, one_mul]

theorem completed_value_eq_one (ν : ∀ e, FiniteDistribution (Seed e))
    (complete : ∀ e, Seed e → A → B)
    (legalL : ∀ x, L x ↪ A) (legalR : ∀ y, R y ↪ B)
    (agrees : ∀ e seed l, complete e seed (legalL (G.left e) l) =
      legalR (G.right e) (G.projection e l))
    (hcomplete : G.value = 1) : (G.completedGame ν complete).value = 1 := by
  apply le_antisymm (G.completedGame ν complete).value_le_one
  obtain ⟨s, hs⟩ := G.exists_optimal_strategy
  calc
    1 = G.success s := (hs.trans hcomplete).symm
    _ = (G.completedGame ν complete).success (liftStrategy legalL legalR s) :=
      (G.completed_success_lift ν complete legalL legalR agrees s).symm
    _ ≤ _ := (G.completedGame ν complete).success_le_value _

end Completion

variable [Fintype Q₁] [Fintype Q₂] [∀ x, Fintype (L x)]
  {A B : Type*} [Fintype A] [Fintype B]

namespace CompletionFamily
variable {G} {legalL : ∀ x, L x ↪ A} {legalR : ∀ y, R y ↪ B}

omit [Fintype Q₁] [Fintype Q₂] [Fintype B] in
theorem marginal (F : G.CompletionFamily legalL legalR) (e : E)
    (a : A) (ha : a ∉ Set.range (legalL (G.left e))) (b : B) :
    (F.seedLaw e).probability (fun seed => decide (F.map e seed a = b)) ≤
      2 / (Fintype.card A - Fintype.card (L (G.left e)) : Nat) := by
  let : Nonempty (Fin (F.size e)) := ⟨⟨0, F.positive e⟩⟩
  change (FiniteDistribution.uniform (Fin (F.size e))).probability _ ≤ _
  rw [probability_uniform_eq_uniformProbability]
  exact F.illegal_probability e ⟨a, ha⟩ b

variable [∀ y, Fintype (R y)] [∀ x, Nonempty (L x)] [∀ y, Nonempty (R y)]
  [Nonempty A] [Nonempty B]

theorem value_le_of_bound (F : G.CompletionFamily legalL legalR)
    (δ : ℝ) (hδ : ∀ e,
      2 / (Fintype.card A - Fintype.card (L (G.left e)) : Nat) ≤ δ) :
    F.game.value ≤ G.value + δ := by
  apply G.completed_value_le_of_bound F.seedLaw F.map legalL legalR F.agrees
      (fun e => 2 / (Fintype.card A - Fintype.card (L (G.left e)) : Nat))
      (fun e => div_nonneg (by norm_num) (Nat.cast_nonneg _)) F.marginal δ hδ

theorem value_eq_one (F : G.CompletionFamily legalL legalR) (hcomplete : G.value = 1) :
    F.game.value = 1 :=
  G.completed_value_eq_one F.seedLaw F.map legalL legalR F.agrees hcomplete

end CompletionFamily

end LegalProjectionGame

end
end PerfectCompleteness.CompletionSoundness

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_RationalFiniteLawLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.RationalFiniteLaw

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

structure RationalLaw {E : Type*} [Fintype E] (μ : FiniteDistribution E) where
  weights : E → ℚ
  positive : ∀ e, 0 < weights e
  total : ∑ e, weights e = 1
  cast_weight : ∀ e, μ.weight e = (weights e : ℝ)

def uniform (E : Type*) [Fintype E] [Nonempty E] :
    RationalLaw (FiniteDistribution.uniform E) where
  weights _ := 1 / (Fintype.card E : ℚ)
  positive _ := div_pos zero_lt_one (Nat.cast_pos.mpr Fintype.card_pos)
  total := by
    have hn : (Fintype.card E : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_div]
    exact mul_inv_cancel₀ hn
  cast_weight _ := by
    change (1 / (Fintype.card E : ℝ)) = ((1 / (Fintype.card E : ℚ) : ℚ) : ℝ)
    simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast]

def pi {I : Type*} [Fintype I] [DecidableEq I]
    {E : I → Type*} [∀ i, Fintype (E i)]
    (P : (i : I) → FiniteDistribution (E i)) (r : ∀ i, RationalLaw (P i)) :
    RationalLaw (FiniteProduct.law P) where
  weights x := ∏ i, (r i).weights (x i)
  positive x := Finset.prod_pos (fun i _ => (r i).positive (x i))
  total := by
    rw [← Fintype.prod_sum]
    simp only [RationalLaw.total, Finset.prod_const_one]
  cast_weight x := by
    change (∏ i, (P i).weight (x i)) = ((∏ i, (r i).weights (x i) : ℚ) : ℝ)
    rw [Rat.cast_prod]
    exact Finset.prod_congr rfl (fun i _ => (r i).cast_weight (x i))

def product {E F : Type*} [Fintype E] [Fintype F]
    {μ : FiniteDistribution E} {ν : FiniteDistribution F}
    (r : RationalLaw μ) (s : RationalLaw ν) : RationalLaw (μ.product ν) where
  weights x := r.weights x.1 * s.weights x.2
  positive x := mul_pos (r.positive x.1) (s.positive x.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, s.total, mul_one]
    exact r.total
  cast_weight x := by
    change μ.weight x.1 * ν.weight x.2 = ((r.weights x.1 * s.weights x.2 : ℚ) : ℝ)
    rw [Rat.cast_mul, r.cast_weight, s.cast_weight]

def sigma {E : Type*} {F : E → Type*} [Fintype E] [∀ e, Fintype (F e)]
    {μ : FiniteDistribution E} {ν : ∀ e, FiniteDistribution (F e)}
    (r : RationalLaw μ) (s : ∀ e, RationalLaw (ν e)) :
    RationalLaw (CompletionSoundness.sigmaLaw μ ν) where
  weights x := r.weights x.1 * (s x.1).weights x.2
  positive x := mul_pos (r.positive x.1) ((s x.1).positive x.2)
  total := by
    rw [Fintype.sum_sigma]
    calc
      _ = ∑ e, r.weights e := by
        apply Finset.sum_congr rfl
        intro e _
        change (∑ f : F e, r.weights e * (s e).weights f) = r.weights e
        rw [← Finset.mul_sum, (s e).total, mul_one]
      _ = 1 := r.total
  cast_weight x := by
    change μ.weight x.1 * (ν x.1).weight x.2 =
      ((r.weights x.1 * (s x.1).weights x.2 : ℚ) : ℝ)
    rw [Rat.cast_mul, r.cast_weight, (s x.1).cast_weight]

end
end PerfectCompleteness.RationalFiniteLaw



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_CompletionAlphabetLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HierarchicalGame

open HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

structure Family {v m : Nat} (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows : Nat → Nat) (E : Type*) where
  endpoints : E → RecursiveSpaces.Slots branch n → Fin t → SourceKeys.Endpoint v m
  arrays : ∀ e, Arrays (sourceSlots clauses (endpoints e)) rows
  selected : E → Nodes branch n
  direction : ∀ e, Block rows (selected e)
  nonzero : ∀ e, direction e ≠ 0

noncomputable section

variable {v m n t : Nat} {clauses : Fin m → SourceClause.NormalizedClause v}
  {branch rows : Nat → Nat} {E : Type*}
  (F : Family clauses branch n t rows E)

def toBlockFamily : CanonicalGame.BlockFamily clauses
    (TreeCanonical.locationCount branch n t) E (Nodes branch n)
    (fun node : Nodes branch n => Block rows node) PUnit.{1} where
  presentation e := HierarchicalArrays.presentation clauses (F.endpoints e) rows (F.arrays e)
  selected := F.selected
  direction := F.direction
  nonzero := F.nonzero

abbrev LeftVertex := CanonicalGame.LeftVertex (toBlockFamily F)
abbrev RightVertex := CanonicalGame.RightVertex (toBlockFamily F)
abbrev LeftLabel (q : LeftVertex F) := CanonicalGame.LeftLabel (toBlockFamily F) q
abbrev RightLabel (q : RightVertex F) := CanonicalGame.RightLabel (toBlockFamily F) q

theorem leftKey_eq (e : E) :
    CanonicalGame.leftKey (toBlockFamily F) e =
      TreeCanonical.key .left (sourceSlots clauses (F.endpoints e)) (fullJoint (F.arrays e)) := rfl

theorem rightKey_eq (e : E) :
    CanonicalGame.rightKey (toBlockFamily F) e =
      TreeCanonical.key .right (sourceSlots clauses (F.endpoints e))
        (BlockQuotient.projectBlock (F.selected e) (F.direction e) ∘ fullJoint (F.arrays e)) := rfl

def game [Fintype E] (μ : FiniteDistribution E) :
    CompletionSoundness.LegalProjectionGame E (LeftVertex F) (RightVertex F)
      (LeftLabel F) (RightLabel F) :=
  CanonicalGame.game (toBlockFamily F) μ

def satisfyingStrategy (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true) :
    CompletionSoundness.LegalStrategy (LeftLabel F) (RightLabel F) :=
  CanonicalGame.satisfyingStrategy (toBlockFamily F) assignment hsat

theorem success_satisfyingStrategy [Fintype E] (μ : FiniteDistribution E)
    (assignment : Fin v → Bool) (hsat : ∀ c, (clauses c).clause.eval assignment = true) :
    (game F μ).success (satisfyingStrategy F assignment hsat) = 1 :=
  CanonicalGame.success_satisfyingStrategy (toBlockFamily F) μ assignment hsat

theorem value_eq_one [Fintype E]
    [Fintype (LeftVertex F)] [Fintype (RightVertex F)]
    [∀ q, Fintype (LeftLabel F q)] [∀ q, Fintype (RightLabel F q)]
    (μ : FiniteDistribution E) (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true) : (game F μ).value = 1 := by
  apply le_antisymm
  · obtain ⟨strategy, hs⟩ := (game F μ).exists_optimal_strategy
    rw [← hs]
    exact (game F μ).occurrences.probability_le_one _
  · have h := (game F μ).success_le_value (satisfyingStrategy F assignment hsat)
    simpa only [success_satisfyingStrategy F μ assignment hsat] using h

end

end PerfectCompleteness.HierarchicalGame


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_DependentDecoderSampling
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.DependentDecoderSampling

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {Q₁ Q₂ E : Type*} [Fintype Q₁] [Fintype Q₂] [Fintype E]
  [DecidableEq Q₁] [DecidableEq Q₂]
  {A : Q₁ → Type*} {B : Q₂ → Type*}
  [∀ q, Fintype (A q)] [∀ q, Fintype (B q)]

def seedLaw (leftKernel : (q : Q₁) → FiniteDistribution (A q))
    (rightKernel : (q : Q₂) → FiniteDistribution (B q)) :
    FiniteDistribution (Seed A B) :=
  (FiniteProduct.law leftKernel).product (FiniteProduct.law rightKernel)

end
end PerfectCompleteness.DependentDecoderSampling

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_RecordSeedSamplingLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
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

instance tapeNonempty (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) : Nonempty (Tape 𝕜 repeats p A) :=
  ⟨zeroTape 𝕜 repeats p A⟩

noncomputable section

variable [Finite 𝕜]

theorem tapeLaw_eq_uniform (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) [∀ s, Finite (A s)] :
    tapeLaw 𝕜 repeats p A = FiniteDistribution.uniform (Tape 𝕜 repeats p A) :=
  UniformLinearImage.law_uniform

end
end PerfectCompleteness.RecursiveSampler

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_WholeArraySampler
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype
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

def componentLaw (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    (k : StepIndex i) → FiniteDistribution
      (StepFactor (RootTape rows repeats (.step i p) slots)
        (Tape rows repeats p (childSlots slots i))
        (fun j => Arrays (childSlots slots j.val) rows) k)
  | .inl _ => BucketSampler.recursiveTapeLaw (rows (n + 1)) repeats (.step i p)
      (LeafDomain slots)
  | .inr (.inl _) => tapeLaw rows repeats p (childSlots slots i)
  | .inr (.inr j) => FiniteDistribution.uniform (Arrays (childSlots slots j.val) rows)

end

end PerfectCompleteness.WholeArraySampler

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_PreliminarySampler
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype
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

abbrev ArrayTape (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (b : Base branch n t m) :=
  WholeArraySampler.Tape rows repeats (GeometricPath.leafPath b.2)
    (sourceSlots clauses (endpoints b.1))

abbrev Raw (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) :=
  (b : Base branch n t m) × (ArrayTape clauses rows repeats b × Choice rows b.2)

def choiceLaw (leaf : Slots branch n) (hn : 0 < n)
    (hrows : ∀ k, 0 < rows (k + 1)) : FiniteDistribution (Choice rows leaf) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact CompletionSoundness.sigmaLaw (FiniteDistribution.uniform (Fin n)) fun level => by
    letI : Nonempty (BucketSampler.Direction
        (rows (Nodes.height (GeometricPath.nodeAtLevel leaf level)))) :=
      directionNonempty _ (by rw [GeometricPath.nodeAtLevel_height]; exact hrows level.val)
    exact FiniteDistribution.uniform _

def conditionalLaw (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hn : 0 < n)
    (hrows : ∀ k, 0 < rows (k + 1)) (b : Base branch n t m) :
    FiniteDistribution (ArrayTape clauses rows repeats b × Choice rows b.2) :=
  (WholeArraySampler.tapeLaw rows repeats (GeometricPath.leafPath b.2)
    (sourceSlots clauses (endpoints b.1))).product (choiceLaw b.2 hn hrows)

def law [NeZero m] (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1)) :
    FiniteDistribution (Raw clauses branch n t rows repeats) :=
  CompletionSoundness.sigmaLaw (baseLaw hbranch)
    (conditionalLaw clauses rows repeats hn hrows)

def family (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) :
    HierarchicalGame.Family clauses branch n t rows (Raw clauses branch n t rows repeats) where
  endpoints e := endpoints e.1.1
  arrays e := WholeArraySampler.evaluate rows repeats (GeometricPath.leafPath e.1.2)
    (sourceSlots clauses (endpoints e.1.1)) e.2.1
  selected e := GeometricPath.nodeAtLevel e.1.2 e.2.2.1
  direction e := e.2.2.2.val
  nonzero e := e.2.2.2.property

def game [NeZero m] (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1)) :=
  HierarchicalGame.game (family clauses branch n t rows repeats)
    (law clauses rows repeats hn hbranch hrows)

end
end PerfectCompleteness.PreliminarySampler

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceQuestionOrderLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype
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

def questionTupleEquiv (branch : Nat → Nat) (n t m : Nat) :
    PreliminarySampler.Questions branch n t m ≃
      (Fin (TreeCanonical.locationCount branch n t) → Fin m) where
  toFun := questionToTuple
  invFun := tupleToQuestion
  left_inv := tupleToQuestion_questionToTuple
  right_inv := questionToTuple_tupleToQuestion

theorem sourceOrder_nodup (branch : Nat → Nat) (n t m : Nat) :
    (sourceOrder branch n t m).Nodup := by
  apply List.Nodup.map (questionTupleEquiv branch n t m).symm.injective
  apply List.nodup_reverse.mpr
  exact List.nodup_ofFn.mpr
    (finFunctionFinEquiv (m := m) (n := TreeCanonical.locationCount branch n t)).symm.injective

theorem sum_map_sourceOrder {A : Type*} [AddCommMonoid A]
    (f : PreliminarySampler.Questions branch n t m → A) :
    ((sourceOrder branch n t m).map f).sum = ∑ question, f question := by
  rw [← List.sum_toFinset f (sourceOrder_nodup branch n t m), sourceOrder_toFinset]

end

end PerfectCompleteness.SourceQuestionOrder


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_OriginalChildScalars
attribute [-instance] _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype
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

def callContributions (calls : Nat) (repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : Fin calls → ScalarTape repeats chosen q slots) :
    (child : Fin (branch n)) → Fin calls → Square slots child :=
  fun child call => stepSquareMap repeats chosen q slots (ω call) child

end
end PerfectCompleteness.OriginalChildScalars

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_HonestTestLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.slotFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_variable_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_variables _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_current _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_remaining _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_dart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_vertex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.to_fromClauseAnswer _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace UniqueGamesTheorem.Foundations.Hastad.SourceGame

open scoped BigOperators
open Target PCP Games SourceContexts

def eventLaw (F : Formula) (hne : F.clauses ≠ []) :
    FiniteDistribution (RandomEvent F) := by
  let : Nonempty (RandomEvent F) := event_nonempty F hne
  exact FiniteDistribution.uniform _

def baseGame (F : Formula) (hne : F.clauses ≠ []) :
    Game (Fin F.variables) (Fin F.clauses.length) Bool ClauseAnswer where
  questions := (eventLaw F hne).pushforward (visibleQuestion F)
  accepts := baseAccepts F

@[simp] theorem baseGame_accepts (F : Formula) (hne : F.clauses ≠ [])
    (v : Fin F.variables) (c : Fin F.clauses.length) (i : Bool) (j : ClauseAnswer) :
    (baseGame F hne).accepts v c i j = baseAccepts F v c i j := rfl

end UniqueGamesTheorem.Foundations.Hastad.SourceGame

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_SourceOccurrences
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_variable_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_variables _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_current _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_remaining _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_dart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_vertex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Executable radix numbering of padded global long-code tables and an ordered
equation occurrence list. The code enumerates random tapes, not distinct
equations: coinciding equations and repeated variable occurrences are retained.
-/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences

open UniqueGamesTheorem.Reduction.CloneGap
open scoped BigOperators

section ConcreteSource

open SourceContexts
open UniqueGamesTheorem.Reduction.FiniteNoise

def clauseAnswerEncoding : Encoding PCP.ClauseAnswer := ⟨8, clauseAnswerFinEquiv⟩

def jEncoding (u : ℕ) : Encoding (J u) := (Encoding.fin u).function clauseAnswerEncoding
def variableEncoding (F : Target.Formula) (u : ℕ) : Encoding (VariableContext F u) :=
  (Encoding.fin u).function (Encoding.fin F.variables)
def clauseEncoding (F : Target.Formula) (u : ℕ) : Encoding (ClauseContext F u) :=
  (Encoding.fin u).function (Encoding.fin F.clauses.length)

def proofEncoding (F : Target.Formula) (u : ℕ) :
    Encoding (GlobalKey (VariableContext F u) (ClauseContext F u) (I u) (J u)) :=
  globalEncoding (variableEncoding F u) (clauseEncoding F u) (iEncoding u) (jEncoding u)

def nBits (F : Target.Formula) (u : ℕ) : ℕ := (proofEncoding F u).size

@[simp] theorem nBits_eq (F : Target.Formula) (u : ℕ) :
    nBits F u = F.variables ^ u * 2 ^ (2 ^ u) +
      (F.clauses.length ^ u * 2 ^ (8 ^ u) + 1) := rfl

def dummyIndex (F : Target.Formula) (u : ℕ) : Fin (nBits F u) :=
  (proofEncoding F u).code (.inr (.inr ()))

def rightAnchor (F : Target.Formula) {u : ℕ} (c : ClauseContext F u) :
    Option {j : J u // validJ F c j = true} := firstValid (jEncoding u) (validJ F c)

/-- Independent actual half-tables extend to the explicit padded key space.
Only the canonically selected right anchor is read at each clause context. -/
def halfTableKeyAssignment (F : Target.Formula) (u : ℕ)
    (a : VariableContext F u → HalfCube (leftAnchor u) → Bool)
    (b : ∀ c : ClauseContext F u, ∀ j₀ : {j : J u // validJ F c j = true},
      HalfCube j₀ → Bool) :
    GlobalKey (VariableContext F u) (ClauseContext F u) (I u) (J u) → Bool
  | .inl (v, f) => a v (canonicalInput (leftAnchor u) f)
  | .inr (.inl (c, g)) =>
    match rightAnchor F c with
    | none => false
    | some j₀ => b c j₀ (canonicalInput j₀ (restrictQuery (validJ F c) g))
  | .inr (.inr _) => false

def emptyAddress (F : Target.Formula) (u : ℕ) (v : VariableContext F u) :
    EmptyContext.Address (leftAnchor u) → Fin (nBits F u)
  | .inl h => (proofEncoding F u).code (.inl (v, h.val))
  | .inr _ => dummyIndex F u

/-- The private query law depends only on the two visible contexts.
In particular, the hidden sampled slots are not inputs to `pi`. -/
def contextEquation (F : Target.Formula) (u D : ℕ)
    (c : ClauseContext F u) (v : VariableContext F u)
    (t : SourceTape.TestTape (I u) (J u) D) : Equation (Fin (nBits F u)) :=
  match rightAnchor F c with
  | none => mapEquation (emptyAddress F u v) (EmptyContext.equation (leftAnchor u) t.1)
  | some j₀ => conditionedOccurrence (variableEncoding F u) (clauseEncoding F u)
      (iEncoding u) (jEncoding u) v c (validJ F c) (pi F c v) (leftAnchor u) j₀
      t.1 t.2.2 (realizedNoise t.2.1)

def leftResponse (F : Target.Formula) (u : ℕ) (bits : Fin (nBits F u) → Bool)
    (v : VariableContext F u) : Cube (I u) → Bool :=
  foldedAnswer (leftAnchor u) (fun h => bits ((proofEncoding F u).code (.inl (v, h.val))))

def testTapeEncoding (u D : ℕ) : Encoding (SourceTape.TestTape (I u) (J u) D) :=
  ((iEncoding u).function Encoding.bool).prod
    (((jEncoding u).function (Encoding.fin D)).prod ((jEncoding u).function Encoding.bool))

abbrev SourceIndex (F : Target.Formula) (u D : ℕ) :=
  (ClauseContext F u × SlotContext u) × SourceTape.TestTape (I u) (J u) D

def sourceIndexEncoding (F : Target.Formula) (u D : ℕ) : Encoding (SourceIndex F u D) :=
  ((clauseEncoding F u).prod (slotContextEncoding u)).prod (testTapeEncoding u D)

def sourceEquation (F : Target.Formula) (u D : ℕ) (p : SourceIndex F u D) :
    Equation (Fin (nBits F u)) :=
  contextEquation F u D p.1.1 (sampledVariables F p.1.1 p.1.2) p.2

/-- The entire finite random-tape population, including repeated visible
contexts and all equation multiplicities, in a fixed explicit order. -/
def rawSourceList (F : Target.Formula) (u D : ℕ) : List (Equation (Fin (nBits F u))) :=
  occurrenceList (sourceIndexEncoding F u D) (sourceEquation F u D)

@[simp] theorem rawSourceList_length (F : Target.Formula) (u D : ℕ) :
    (rawSourceList F u D).length =
      (F.clauses.length ^ u * 3 ^ u) *
        (2 ^ (2 ^ u) * (D ^ (8 ^ u) * 2 ^ (8 ^ u))) := by
  rw [rawSourceList, occurrenceList_length]
  rfl

/-- A satisfiable totalization for the empty input formula, without changing
or diluting the occurrence list of a nonempty formula. -/
def emptyFormulaEquation (F : Target.Formula) (u : ℕ) : Equation (Fin (nBits F u)) :=
  ⟨dummyIndex F u, dummyIndex F u, dummyIndex F u, false⟩

def sourceList (F : Target.Formula) (u D : ℕ) : List (Equation (Fin (nBits F u))) :=
  if F.clauses.isEmpty then [emptyFormulaEquation F u] else rawSourceList F u D

end ConcreteSource

end UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_SourceSignaturePrepareLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_variable_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_variables _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.card_event _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inl_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inr_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_address _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_cube _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_dart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_event _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_localEvent _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_pairCube _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_vertex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.inputCoordinateEquiv_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_edgeAddress_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_vertexAddress_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Queries.mask_idempotent _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Relations.relationAt_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.averagingOperator_cayleyGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.coefficient_zeroFrequency _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.cubeXor_zeroFrequency _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_dart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_vertex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual numbered equation list has exactly the acceptance bounded by
the private Fourier decoder. Only the repeated base-game value is an input
here; list semantics and all finite sampling laws are supplied. -/
noncomputable section
namespace UniqueGamesTheorem.Foundations.Hastad.SourceSoundness

open scoped BigOperators
open Target SourceContexts SourceOccurrences SourceGame

def leftTable (F : Formula) (u : ℕ) (bits : Fin (nBits F u) → Bool)
    (v : VariableContext F u) : HalfCube (leftAnchor u) → Bool :=
  fun h => bits ((proofEncoding F u).code (.inl (v, h.val)))

@[simp] theorem leftTable_answer (F : Formula) (u : ℕ)
    (bits : Fin (nBits F u) → Bool) (v : VariableContext F u) :
    foldedAnswer (leftAnchor u) (leftTable F u bits v) = leftResponse F u bits v := rfl

end UniqueGamesTheorem.Foundations.Hastad.SourceSoundness

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_SourceHeaderCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceHeaderCounts

open Turing Complexity
open MachineComposition

noncomputable section

def polynomial (u D : Nat) : Kind → Polynomial Nat
  | .left => Polynomial.C (2 ^ (2 ^ u)) * Polynomial.X ^ u
  | .right => Polynomial.C (2 ^ (8 ^ u)) * Polynomial.X ^ u
  | .occurrences => Polynomial.C (3 ^ u * (SourceOccurrences.testTapeEncoding u D).size) *
      Polynomial.X ^ u

@[simp] theorem polynomial_left_eval (u D n : Nat) :
    (polynomial u D .left).eval n = leftValue u n := by simp [polynomial, leftValue]
@[simp] theorem polynomial_right_eval (u D m : Nat) :
    (polynomial u D .right).eval m = rightValue u m := by simp [polynomial, rightValue]

abbrev Coefficients (u D : Nat) :=
  Fin (CookLevin.PolynomialMachine.width (polynomial u D .left)) ⊕
    (Fin (CookLevin.PolynomialMachine.width (polynomial u D .right)) ⊕
      Fin (CookLevin.PolynomialMachine.width (polynomial u D .occurrences)))

end

end UniqueGamesTheorem.Foundations.Hastad.SourceHeaderCounts

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_SourceQueryOrderLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_variable_count _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_variables _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_archive _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableWords.decode_rotationWords _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_dart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_vertex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorModel

open Turing Complexity SourceRuntimeModel


abbrev Extra (u D : Nat) := SourceHeaderCounts.Coefficients u D ⊕ Unit
abbrev Tape (u D : Nat) := SourceRuntimeModel.Arena u (Extra u D)
def accumulatorTape (u D : Nat) : Tape u D := workTape .accumulator

end UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorModel



namespace UniqueGamesTheorem.Foundations.Hastad.SourceStartup

open Turing Complexity SourceRuntimeModel SourceGeneratorModel
open MachineComposition


noncomputable section

variable {u D : Nat}

abbrev Tape (u D : Nat) := SourceGeneratorModel.Tape u D

local instance instDecidableEqExtra (u D : Nat) : DecidableEq (SourceGeneratorModel.Extra u D) := Classical.decEq _

def initialTapes (F : Target.Formula) : Tape u D → List Bool :=
  Function.update (fun _ => []) .formula (formulaBits F)

def initializedTapes (F : Target.Formula) : Tape u D → List Bool :=
  SourceLoopInit.outputTapes F (initialTapes F)

def readyTapes (F : Target.Formula) : Tape u D → List Bool
  | .extra (.inr .leftBlock) => encodeWord (SourceHeaderCounts.leftValue u F.variables)
  | .extra (.inr .dummy) => encodeWord (SourceHeaderCounts.dummyValue u F.variables F.clauses.length)
  | .extra (.inr .accumulator) =>
      (encodeWords [SourceOccurrences.nBits F u, (SourceOccurrences.sourceList F u D).length]).reverse
  | p => initializedTapes F p

@[simp] theorem ready_leftBlock (F : Target.Formula) :
    readyTapes (u := u) (D := D) F (workTape .leftBlock) =
      encodeWord (SourceHeaderCounts.leftValue u F.variables) := rfl

@[simp] theorem ready_dummy (F : Target.Formula) :
    readyTapes (u := u) (D := D) F (workTape .dummy) =
      encodeWord (SourceHeaderCounts.dummyValue u F.variables F.clauses.length) := rfl

@[simp] theorem ready_accumulator (F : Target.Formula) :
    readyTapes (u := u) (D := D) F (accumulatorTape u D) =
      (encodeWords [SourceOccurrences.nBits F u, (SourceOccurrences.sourceList F u D).length]).reverse := rfl

end

end UniqueGamesTheorem.Foundations.Hastad.SourceStartup



end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_FinalTableFormula
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_variable_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_variables _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_append _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_nil _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_nil _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_done _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_head _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_headIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_headValue _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_relation _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_reverseIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_row _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_head _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tableBits _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tableWords _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_vertices _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The exact table-to-formula converter used by the final CNF machine.
Its semantic count premise is explicit; amplification supplies that premise
elsewhere. The converter chooses no vertex or dart numbering. -/

namespace UniqueGamesTheorem.Foundations.PCP.FinalTableFormula

open Target Complexity

def output (table : GraphTables.Table) : Formula :=
  FinalBooleanVerifier.cnf (FinalCNFPattern.tableGraph table) (Equiv.refl _) (Equiv.refl _)

@[simp] theorem variable_count (table : GraphTables.Table) :
    (output table).variables = table.vertices * 6 + table.darts * 36864 :=
  FinalBooleanVerifier.cnf_variable_count _ (Equiv.refl _) (Equiv.refl _)

@[simp] theorem clause_count (table : GraphTables.Table) :
    (output table).clauses.length = table.darts * 40960 :=
  FinalBooleanVerifier.cnf_clause_count _ (Equiv.refl _) (Equiv.refl _)

theorem nonempty (table : GraphTables.Table) (hd : 0 < table.darts) :
    (output table).clauses ≠ [] :=
  FinalBooleanVerifier.cnf_nonempty _ (Equiv.refl _) (Equiv.refl _) hd

end UniqueGamesTheorem.Foundations.PCP.FinalTableFormula

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_TableIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Iteration of the concrete stored-table round, with the original formula's
actual initial graph size controlling the number of rounds. -/

namespace UniqueGamesTheorem.Foundations.PCP.TableIteration

open RoundTables
open Target Complexity

/-- The same data computation on all validated tables; positivity is an invariant,
and is erased from the runtime path. -/
def runTables (H : BaseTable) : Nat → GraphTables.Table → GraphTables.Table :=
  AmplificationIteration.run (build H)

theorem run_val (H : BaseTable) (n : Nat) (input : Input) :
    (run H n input).val = runTables H n input.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change build H (run H n input).val = build H (runTables H n input.val)
      rw [ih]

def iterationCount (F : Formula) : Nat := AmplificationIteration.rounds (size (initial F))

def output (H : BaseTable) (F : Formula) : Input := run H (iterationCount F) (initial F)

def outputTable (H : BaseTable) (F : Formula) : GraphTables.Table :=
  runTables H (iterationCount F) (RawInitialTables.table F)

theorem output_val (H : BaseTable) (F : Formula) : (output H F).val = outputTable H F :=
  run_val H (iterationCount F) (initial F)

def gapMap (H : BaseTable) (F : Formula) : Formula := FinalTableFormula.output (outputTable H F)

theorem output_darts_positive (H : BaseTable) (F : Formula) : 0 < (outputTable H F).darts := by
  rw [← output_val]
  exact (output H F).property

theorem gapMap_nonempty (H : BaseTable) (F : Formula) : (gapMap H F).clauses ≠ [] :=
  FinalTableFormula.nonempty (outputTable H F) (output_darts_positive H F)

end UniqueGamesTheorem.Foundations.PCP.TableIteration

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachinePaddedExpanderFamilyBoundsLemmas
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily

open Turing

section TableCoordinates

open PCP.ExpanderTables PCP.ExpanderRowControl

section Placement

variable {ρ : Type} [Fintype ρ]

/-- The ceiling program preserves the family state as its ambient component. -/
def ceilingSource : MachineCeilingPower.Label →
    TM2.Stmt MachineCeilingPower.Alphabet MachineCeilingPower.Label (State ρ) :=
  MachineStateEquiv.program (ceilingStates ρ)
    (MachineCeilingPower.program PCP.ExpanderFamily.growth)

/-- Actual composition on shared Boolean tapes. No runtime bridge operation
is required, because both programs use the same physical level tape. -/
def program (H : SmallTable) : Label → TM2.Stmt Alphabet Label (State ρ)
  | .inl label =>
    MachineCloudPadding.Placement.statement familyTape familyLabel none (familySource H label)
  | .inr label =>
    MachineCloudPadding.Placement.statement ceilingTape ceilingLabel (some familyEntry)
      (ceilingSource (ρ := ρ) label)

@[simp] theorem program_family (H : SmallTable)
    (label : MachineExpanderFamily.Label fixedDegree) :
    program (ρ := ρ) H (familyLabel label) =
      MachineCloudPadding.Placement.statement familyTape familyLabel none
        (familySource H label) := rfl

@[simp] theorem program_ceiling (H : SmallTable) (label : MachineCeilingPower.Label) :
    program (ρ := ρ) H (ceilingLabel label) =
      MachineCloudPadding.Placement.statement ceilingTape ceilingLabel (some familyEntry)
        (ceilingSource (ρ := ρ) label) := rfl

/-- Only the unary request is initially present. -/
def initialTapes (requested : Nat) : Tape → List Bool
  | .inr .input => encodeWord requested
  | _ => []

def retainedCeilingTapes (requested : Nat) : MachineCeilingPower.Tape → List Bool :=
  MachineCeilingPower.memory (encodeWord requested) []
    (encodeWord (PCP.PreprocessingLevels.paddedSize requested)) [] [] [] [] []

def handoffTapes (requested : Nat) : Tape → List Bool
  | .inl tape => MachineExpanderFamily.toBoolTapes
      (MachineExpanderFamily.initialTapes (PCP.PreprocessingLevels.boundedLevel requested) []) tape
  | .inr tape => retainedCeilingTapes requested tape

def finalTapes (H : SmallTable) (requested : Nat) : Tape → List Bool
  | .inl tape => MachineExpanderFamily.toBoolTapes
      (MachineExpanderFamily.familyTapes H (PCP.PreprocessingLevels.boundedLevel requested) []) tape
  | .inr tape => retainedCeilingTapes requested tape

@[simp] theorem initialTapes_input (requested : Nat) :
    initialTapes requested (.inr .input) = encodeWord requested := rfl

@[simp] theorem finalTapes_input (H : SmallTable) (requested : Nat) :
    finalTapes H requested (.inr .input) = encodeWord requested := rfl

@[simp] theorem finalTapes_power (H : SmallTable) (requested : Nat) :
    finalTapes H requested (.inr .power) =
      encodeWord (PCP.PreprocessingLevels.paddedSize requested) := rfl

end Placement

open MachineCloudPadding PCP.ExpanderTableWords

@[simp] theorem handoffTapes_level (requested : Nat) :
    handoffTapes requested (ceilingTape .level) =
      encodeWord (PCP.PreprocessingLevels.boundedLevel requested) := by
  simp [handoffTapes, ceilingTape, MachineExpanderFamily.toBoolTapes,
    MachineExpanderFamily.toBoolWord, MachineExpanderFamily.initialTapes,
    MachineEmbedding.tapes]

@[simp] theorem handoffTapes_level_shadow (requested : Nat) :
    handoffTapes requested (.inr .level) = [] := rfl

@[simp] theorem finalTapes_level_shadow (H : SmallTable) (requested : Nat) :
    finalTapes H requested (.inr .level) = [] := rfl

@[simp] theorem finalTapes_remainingLevel (H : SmallTable) (requested : Nat) :
    finalTapes H requested (ceilingTape .level) = encodeWord 0 := by
  simp [finalTapes, ceilingTape, MachineExpanderFamily.toBoolTapes,
    MachineExpanderFamily.toBoolWord, MachineExpanderFamily.familyTapes,
    MachineExpanderFamily.boundaryTapes, MachineExpanderFamily.extraFrame,
    MachineEmbedding.tapes]

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

abbrev Alphabet (_ : Tape) := Bool

end UniqueGamesTheorem.Foundations.Complexity.MachineCloudPrefix

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

abbrev Tape := Fin 27 ⊕ (MachineRegularMetadata.Extra ⊕ MachinePaddedExpanderFamily.Tape)

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBody

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOwnerCleanup
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup

open Turing MachineComposition

abbrev Tape := MachineRegularOriginalBody.Tape ⊕ Fin 2

/-- Every equality decision is explicitly assembled from fixed finite leaves.
There is no classical decision or recursive typeclass search on the tape sum. -/
instance tapeDecidableEq : DecidableEq Tape :=
  sumDecidableEq
    (sumDecidableEq (inferInstanceAs (DecidableEq (Fin 27)))
      (sumDecidableEq (inferInstanceAs (DecidableEq MachineRegularMetadata.Extra))
        (sumDecidableEq
          (sumDecidableEq
            (sumDecidableEq (inferInstanceAs (DecidableEq MachineExpanderRow.Tape))
              (inferInstanceAs (DecidableEq MachineExpanderTable.ExtraTape)))
            (inferInstanceAs (DecidableEq MachineExpanderFamily.ExtraTape)))
          (inferInstanceAs (DecidableEq MachineCeilingPower.Tape)))))
    (inferInstanceAs (DecidableEq (Fin 2)))

/-- List membership uses Boolean equality. These instances are
the explicit Boolean view of the executable equality procedure above. -/
instance tapeBEq : BEq Tape where
  beq a b := decide (a = b)

instance tapeLawfulBEq : LawfulBEq Tape where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _

def core (k : Fin 27) : Tape := .inl (.inl k)
def localRank : Tape := core 3
def count : Tape := core 4
def prefixTape : Tape := core 5
def rotor : Tape := core 7
def padding : Tape := .inl (.inr (.inl .padding))
def level : Tape := .inl (.inr (.inl .level))
def dummyFuel : Tape := .inr 0

/-- Every name is distinct, so the exact drain cost uses the entry lengths. -/
def cleanupTapes : List Tape := [localRank, count, rotor, padding, level, dummyFuel]

variable {Λ : Type}

def afterAddition (base : Tape → List Bool) (d o : Nat) : Tape → List Bool :=
  Function.update base prefixTape (encodeWord (d + o))

def finalTapes (base : Tape → List Bool) (d o : Nat) : Tape → List Bool :=
  MachineDrainMany.finalTapes cleanupTapes (afterAddition base d o)

theorem finalTapes_apply (base : Tape → List Bool) (d o : Nat) (k : Tape) :
    finalTapes base d o k =
      if k ∈ cleanupTapes then []
      else if k = prefixTape then encodeWord (d + o) else base k := by
  simp only [finalTapes, MachineDrainMany.finalTapes_apply, afterAddition,
    Function.update_apply]

@[simp] theorem finalTapes_prefix (base : Tape → List Bool) (d o : Nat) :
    finalTapes base d o prefixTape = encodeWord (d + o) := by
  simp [finalTapes_apply, cleanupTapes, prefixTape, localRank, count, rotor,
    padding, level, dummyFuel, core]

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedRows

open InitialParameters UpperParameterScalars
open UniqueGamesTheorem.Appendix UniqueGamesTheorem.Fourier

noncomputable section

structure Plan (δ : ℚ) where
  depth : Nat
  depth_ge : 2 ≤ depth
  depth_mass : 4 ≤ (depth : ℝ) * epsilon δ
  order : Nat
  order_pos : 1 ≤ order
  density : ℝ
  density_pos : 0 < density
  density_lt : density < 1
  spectral : MatrixLevelBridge.levelCutoffConstant order density +
    RankLevelFilter.node (order + 1) < inverse δ / 2
  rootFirstRows : Nat → Nat
  rows_order : ∀ k, order ≤ rootFirstRows k
  rows_pos : ∀ k, 1 ≤ rootFirstRows k
  rows_correction : ∀ k, 1 / (2 : ℝ) ^ (rootFirstRows k - order) <
    rhoPred (useful δ) density / 8
  repeatCount : Nat → Nat
  repeats_min : ∀ ℓ, 6 ≤ repeatCount ℓ
  repeats_error : ∀ ℓ, (7 / 8 : ℝ) ^ repeatCount ℓ ≤
    min (h order ℓ / 2) (tau (useful δ) density order ℓ ^ 2 / 2)
  lowerRequirements : ∀ (hδ : 0 < δ) k (i : Fin k),
    (DescendingRows.lowerChoice (useful_pos hδ) density_pos (inverse_pos hδ)
      order (rootFirstRows i.val)).minimumRows ≤ rootFirstRows k

variable {δ : ℚ} (plan : Plan δ)

def rows : Nat → Nat := DescendingRows.treeRows plan.depth plan.rootFirstRows

end
end PerfectCompleteness.FixedRows

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OriginalBelowCut
attribute [-instance] _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_refl _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_refl_right _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_step _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.TerminalCalls.card_refl _root_.OAI.PerfectCompleteness.TerminalCalls.drawIndex_refl _root_.OAI.PerfectCompleteness.TerminalCalls.drawIndex_step _root_.OAI.PerfectCompleteness.TerminalCalls.isTerminal_recursive _root_.OAI.PerfectCompleteness.TerminalCalls.isTerminal_refl _root_.OAI.PerfectCompleteness.TerminalCalls.not_isTerminal_ordinary _root_.OAI.PerfectCompleteness.TerminalCalls.terminalSubtypeEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalBelowCut

open TreeSourceSpaces HierarchicalArrays DescendantSpaces WholeArraySampler
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def below (rows repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : Tape rows repeats (.step chosen q) slots) :
    (child : Fin (branch n)) → Arrays (childSlots slots child) rows :=
  fun child node => WholeArraySampler.evaluate rows repeats (.step chosen q) slots ω
    (.inr (child, node))

@[simp] theorem below_selected (rows repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : Tape rows repeats (.step chosen q) slots) :
    below rows repeats chosen q slots ω chosen =
      WholeArraySampler.evaluate rows repeats q (childSlots slots chosen)
        (ω (.inr (.inl ()))) := by
  funext node
  exact WholeArraySampler.evaluate_selected rows repeats chosen q slots ω node

@[simp] theorem below_ordinary (rows repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : Tape rows repeats (.step chosen q) slots) (j : RecursiveSampler.OffPath chosen) :
    below rows repeats chosen q slots ω j.val = ω (.inr (.inr j)) := by
  funext node
  exact WholeArraySampler.evaluate_ordinary rows repeats chosen q slots ω j node

end

end PerfectCompleteness.OriginalBelowCut

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_CutSamplerRefinement
attribute [-instance] _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.stepFactorFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
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

def zeroFactor (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) → (A : Slots branch n → Type u) →
      (j : DrawIndex repeats p) → RefinedSpace 𝕜 repeats p A j
  | 0, _, .refl _, A, _ => (0 : space 𝕜 branch 0 A)
  | n + 1, _, .refl _, A, _ =>
      fun i => (0 : squareSpace (space 𝕜 branch n (childFamily A i)))
  | n + 1, _, .step i p, A, j =>
      match j with
      | Sum.inl j => (0 : squareSpace (space 𝕜 branch n (childFamily A j.val)))
      | Sum.inr j => zeroFactor 𝕜 repeats p (childFamily A i) j.2

instance refinedNonempty (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) (A : Slots branch n → Type u) (j : DrawIndex repeats p) :
    Nonempty (RefinedSpace 𝕜 repeats p A j) := ⟨zeroFactor 𝕜 repeats p A j⟩

end
end PerfectCompleteness.CutSamplerRefinement

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_CutTerminalSplit
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
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

variable (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
  (p : Path branch n (m + 1)) (A : Slots branch n → Type u)

variable [Finite 𝕜] [∀ s, Finite (A s)]

instance childSquareFintype (i : Fin (branch m)) :
    Fintype (squareSpace (space 𝕜 branch m (childFamily (p.family A) i))) :=
  Fintype.ofFinite _

end
end PerfectCompleteness.CutTerminalSplit

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_CutSamplerLocality
attribute [-instance] _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.stepFactorFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutSamplerLocality

open scoped BigOperators Classical
open RecursiveSpaces DescendantSpaces RecursiveSampler PointwiseSpaces
open CutSamplerRefinement

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m : Nat}

def subTape (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (i : Fin (branch n)) (p : Path branch n m)
    (A : Slots branch (n + 1) → Type u)
    (tape : CutSamplerRefinement.Tape 𝕜 repeats (.step i p) A)
    (h : Fin (repeats (n + 1))) (b : Bool) :
    CutSamplerRefinement.Tape 𝕜 repeats p (childFamily A i) :=
  fun j => tape (Sum.inr ((h, b), j))

def ZeroAtClean (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) → (A : Slots branch n → Type u) →
    (clean : Fin (branch m) → Prop) → CutSamplerRefinement.Tape 𝕜 repeats p A → Prop
  | _, _, .refl _, _, clean, tape => ∀ i, clean i → tape () i = 0
  | _ + 1, _, .step i p, A, clean, tape =>
      ∀ h b, ZeroAtClean 𝕜 repeats p (childFamily A i) clean
        (subTape 𝕜 repeats i p A tape h b)

end
end PerfectCompleteness.CutSamplerLocality

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_OriginalChildBlocks
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_refl _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_refl_right _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_step _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.OddListExtraction.form_atom_self _root_.OAI.PerfectCompleteness.OddListExtraction.multiplicationForm_apply _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalChildBlocks

open PointwiseSpaces RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalChildScalars
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def rawEquiv (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) (child : Fin (branch n)) :
    ((Fin calls → Square slots child) × Arrays (childSlots slots child) rows) ≃
      ChildBlockCardinality.Raw calls rows (childSlots slots child) := Equiv.refl _

abbrev SourceTape (calls : Nat) (rows repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :=
  (Fin calls → ScalarTape repeats chosen q slots) ×
    WholeArraySampler.Tape rows repeats (.step chosen q) slots

def rawMap (calls : Nat) (rows repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : SourceTape calls rows repeats chosen q slots) :
    (child : Fin (branch n)) → ChildBlockCardinality.Raw calls rows (childSlots slots child) :=
  fun child => rawEquiv calls rows slots child
    (callContributions calls repeats chosen q slots ω.1 child,
      OriginalBelowCut.below rows repeats chosen q slots ω.2 child)

@[simp] theorem rawMap_call (calls : Nat) (rows repeats : Nat → Nat)
    (chosen : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : SourceTape calls rows repeats chosen q slots) (child : Fin (branch n)) (call : Fin calls) :
    (rawMap calls rows repeats chosen q slots ω child).1 call =
      stepSquareMap repeats chosen q slots (ω.1 call) child := rfl

@[simp] theorem rawMap_array (calls : Nat) (rows repeats : Nat → Nat)
    (chosen : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : SourceTape calls rows repeats chosen q slots) (child : Fin (branch n))
    (node : Nodes branch n) :
    (rawMap calls rows repeats chosen q slots ω child).2 node =
      WholeArraySampler.evaluate rows repeats (.step chosen q) slots ω.2 (.inr (child, node)) := rfl

end
end PerfectCompleteness.OriginalChildBlocks

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_DependentPredictionDifferenceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.DependentPredictionDifference

noncomputable section

open scoped Classical
open UniqueGamesTheorem.Foundations.Games

variable {O : Type*}

variable [Fintype O] {Ω P A : O → Type*}
  [∀ o, Fintype (Ω o)] [∀ o, Fintype (P o)] [∀ o, Fintype (A o)]

def law (outer : FiniteDistribution O)
    (original : ∀ o, FiniteDistribution (Ω o))
    (advice : ∀ o, FiniteDistribution (A o)) : FiniteDistribution (Sample Ω A) :=
  CompletionSoundness.sigmaLaw outer (fun o => (original o).product (advice o))

end
end PerfectCompleteness.DependentPredictionDifference


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceQuestionPositionSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionPositionSplit

noncomputable section

open scoped Classical
open RecursiveSpaces SourceQuestionReconstruction TreeSourceSpaces
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n t m : Nat}

abbrev Questions := PreliminarySampler.Questions branch (n + 1) t m

end
end PerfectCompleteness.SourceQuestionPositionSplit

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalFrozenTablesLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawIndexDecidableEq _root_.OAI.PerfectCompleteness.RecursiveSampler.drawIndexFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PerfectCompleteness.DescendantSpaces.Path

open RecursiveSpaces

universe u

variable {branch : Nat → Nat} {n m k l : Nat}

theorem append_assoc (p : Path branch n m) :
    ∀ (q : Path branch m k) (r : Path branch k l),
      (p.append q).append r = p.append (q.append r) := by
  induction p with
  | refl n => intro q r; rfl
  | step i p ih =>
      intro q r
      exact congrArg (Path.step i) (ih q r)

end PerfectCompleteness.DescendantSpaces.Path

end


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_OwnInputReferenceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
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

abbrev ScalarSample (repeats : Nat → Nat) (cut : Cut upper lower) :=
  RecursiveSampler.Tape F2 repeats cut.path (LeafDomain (nodeSlots slots upper))

end
end PerfectCompleteness.OwnInputReference



namespace PerfectCompleteness.OwnInputCanonicalQuery

open scoped Classical
open TreeSourceSpaces HierarchicalArrays

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat) (upper lower : Nodes branch n)

def exteriorOf (arrays : Arrays slots rows) : OwnInputReference.Exterior slots rows upper lower where
  otherArrays node := arrays node.val
  lowerRows := arrays lower

end
end PerfectCompleteness.OwnInputCanonicalQuery

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_DecoderSourcePullback
attribute [-instance] _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype
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

def relativeCut :
    {n : Nat} → (upper : Nodes branch n) →
      (lower : Nodes branch (Nodes.height upper)) →
      Nodes.height lower < Nodes.height upper →
      Cut upper (RelativeDescendantProducts.relativeNode upper lower)
  | 0, upper, _, _ => nomatch upper
  | _ + 1, .inl _, lower, h =>
      { proper := h
        path := Nodes.path lower
        slots_agree := fun _ => rfl }
  | _ + 1, .inr (i, upper), lower, h =>
      let c := relativeCut upper lower h
      { proper := c.proper
        path := c.path
        slots_agree := fun s => congrArg (fun z => (i, z)) (c.slots_agree s) }

def selectedCut (upper : Nodes branch n) (level : Nat)
    (d : HierarchicalFrozenTables.LowerNodes upper level) :
    Cut upper (HierarchicalLeftDecoder.LowerNode upper level d) :=
  relativeCut upper d.val.val d.val.property


end
end PerfectCompleteness.DecoderSourcePullback

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_HierarchicalAllDecoderTables
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
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

local instance rowSpaceFintype_re23f58_1 (node : Nodes branch n) :
    Fintype (NodeEmbedding.RowSpace slots node) := Fintype.ofFinite _
local instance nodeSpaceFintype_re23f58_1 (node : Nodes branch n) :
    Fintype (NodeEmbedding.NodeH slots node) := Fintype.ofFinite _
abbrev UpperAnswer := Module.Dual F2 (NodeEmbedding.RowSpace slots upper)

local instance upperDualFintype : Fintype (UpperAnswer slots upper) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)

end
end PerfectCompleteness.HierarchicalAllDecoderTables

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerDirectionFiber
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BucketUniform.evaluateLinear_apply _root_.OAI.PerfectCompleteness.BucketUsefulCollision.fill_self _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerDirectionFiber

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open BucketSampler (F2 Direction)

variable {ℓ : Nat}

theorem exists_pivot (a : Direction ℓ) : ∃ i : Fin ℓ, a.val i = 1 := by
  by_contra h
  apply a.property
  funext i
  rcases UniqueGamesTheorem.Integration.BinaryLinear.scalar_cases (a.val i) with hz | ho
  · exact hz
  · exact False.elim (h ⟨i, ho⟩)

def pivot (a : Direction ℓ) : Fin ℓ := Classical.choose (exists_pivot a)

@[simp] theorem pivot_value (a : Direction ℓ) : a.val (pivot a) = 1 :=
  Classical.choose_spec (exists_pivot a)

abbrev Other (a : Direction ℓ) := {i : Fin ℓ // i ≠ pivot a}
abbrev Complement (a : Direction ℓ) (H : Type*) := Other a → H

variable {H : Type*} [AddCommGroup H] [Module F2 H]

def complement (a : Direction ℓ) (S : Rows H ℓ) : Complement a H :=
  fun j => S j.val - a.val j.val • S (pivot a)

def restore (a : Direction ℓ) (c : Complement a H) (h : H) : Rows H ℓ :=
  fun i => if hi : i = pivot a then h else c ⟨i, hi⟩ + a.val i • h

@[simp] theorem restore_pivot (a : Direction ℓ) (c : Complement a H) (h : H) :
    restore a c h (pivot a) = h := by simp [restore]

@[simp] theorem restore_other (a : Direction ℓ) (c : Complement a H) (h : H)
    (j : Other a) : restore a c h j.val = c j + a.val j.val • h := by
  simp only [restore, dite_eq_right j.property]

@[simp] theorem complement_restore (a : Direction ℓ) (c : Complement a H) (h : H) :
    complement a (restore a c h) = c := by
  funext j
  simp only [complement, restore_other, restore_pivot, add_sub_cancel_right]

@[simp] theorem restore_complement (a : Direction ℓ) (S : Rows H ℓ) :
    restore a (complement a S) (S (pivot a)) = S := by
  funext i
  by_cases hi : i = pivot a
  · subst i
    exact restore_pivot a (complement a S) (S (pivot a))
  · simp only [restore, dite_eq_right hi, complement, sub_add_cancel]

def split (a : Direction ℓ) : Rows H ℓ ≃ Complement a H × H where
  toFun S := (complement a S, S (pivot a))
  invFun z := restore a z.1 z.2
  left_inv := restore_complement a
  right_inv z := Prod.ext (complement_restore a z.1 z.2) (restore_pivot a z.1 z.2)

@[simp] theorem split_apply (a : Direction ℓ) (S : Rows H ℓ) :
    split a S = (complement a S, S (pivot a)) := rfl

def replace (a : Direction ℓ) (S : Rows H ℓ) (fresh : H) : Rows H ℓ :=
  restore a (complement a S) fresh

@[simp] theorem complement_replace (a : Direction ℓ) (S : Rows H ℓ) (fresh : H) :
    complement a (replace a S fresh) = complement a S :=
  complement_restore a _ _

section Laws

variable [Fintype H]

def pairCoordinates (a : Direction ℓ) :
    (Rows H ℓ × H) ≃ Complement a H × (H × H) where
  toFun z := (complement a z.1, (z.1 (pivot a), z.2))
  invFun z := (restore a z.1 z.2.1, z.2.2)
  left_inv z := Prod.ext (restore_complement a z.1) rfl
  right_inv z := Prod.ext (complement_restore a z.1 z.2.1)
    (Prod.ext (restore_pivot a z.1 z.2.1) rfl)

omit [Fintype H] in
@[simp] theorem pairCoordinates_apply (a : Direction ℓ) (z : Rows H ℓ × H) :
    pairCoordinates a z = (complement a z.1, (z.1 (pivot a), z.2)) := rfl

end Laws

end
end PerfectCompleteness.LowerDirectionFiber

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_CommonAccuracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CommonAccuracy

open FixedRows InitialParameters UpperParameterScalars

noncomputable section

variable {δ : ℚ} (plan : Plan δ)

def tolerance (j : Nat) : ℝ :=
  min (epsilon δ ^ 2 / 40)
    (min (simultaneous δ ^ 2 / 160)
      (min (plan.density * q (inverse δ) plan.order (rows plan j) / 160)
        (min (gamma (useful δ) plan.density (inverse δ) plan.order (rows plan j) ^ 2 / 640)
          (gamma (useful δ) plan.density (inverse δ) plan.order (rows plan j) / 40))))

end
end PerfectCompleteness.CommonAccuracy

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_MetadataFreeSampler
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.MetadataFreeSampler

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open scoped Classical

noncomputable section

abbrev SignTuple (branch : Nat → Nat) (n t : Nat) :=
  Slots branch n → Fin t → SourceClause.Triple

abbrev EncodedAssignment (branch : Nat → Nat) (n t : Nat) :=
  Slots branch n → Fin t → Fin 7

variable {branch : Nat → Nat} {n t : Nat}

abbrev SignedLeaf (signs : SignTuple branch n t) (leaf : Slots branch n) :=
  (k : Fin t) → ClauseSupport.Answer (signs leaf k)

abbrev SignedDomain (signs : SignTuple branch n t) := Assignment (SignedLeaf signs)

def assignmentEquiv (signs : SignTuple branch n t) :
    SignedDomain signs ≃ EncodedAssignment branch n t :=
  Equiv.piCongrRight (fun leaf => Equiv.piCongrRight (fun k =>
    CanonicalKeys.answerEquivFinSeven (signs leaf k)))

abbrev ArrayTables (branch : Nat → Nat) (n t : Nat) (rows : Nat → Nat) :=
  (node : Nodes branch n) → Fin (rows (Nodes.height node)) →
    EncodedAssignment branch n t → F2

abbrev Input (branch : Nat → Nat) (n t : Nat) (rows : Nat → Nat) :=
  SignTuple branch n t × ArrayTables branch n t rows

def tableJoint {rows : Nat → Nat} (tables : ArrayTables branch n t rows)
    (x : EncodedAssignment branch n t) : Output branch n rows :=
  (fun node row => tables node row x, PUnit.unit)

section Source

variable {v m : Nat}

def sourceSigns (clauses : Fin m → SourceClause.NormalizedClause v)
    (q : PreliminarySampler.Questions branch n t m) : SignTuple branch n t :=
  fun leaf k => (clauses (q leaf k)).signs

abbrev sourceSlots (clauses : Fin m → SourceClause.NormalizedClause v)
    (q : PreliminarySampler.Questions branch n t m) :=
  HierarchicalArrays.sourceSlots clauses (PreliminarySampler.endpoints q)

def sourceAssignmentEquiv (clauses : Fin m → SourceClause.NormalizedClause v)
    (q : PreliminarySampler.Questions branch n t m) :
    Domain (sourceSlots clauses q) ≃ EncodedAssignment branch n t :=
  assignmentEquiv (sourceSigns clauses q)

def encodeArrays (clauses : Fin m → SourceClause.NormalizedClause v)
    (q : PreliminarySampler.Questions branch n t m) {rows : Nat → Nat}
    (arrays : Arrays (sourceSlots clauses q) rows) : ArrayTables branch n t rows :=
  fun node row x => joint arrays ((sourceAssignmentEquiv clauses q).symm x) node row

def encodeInput (clauses : Fin m → SourceClause.NormalizedClause v)
    (q : PreliminarySampler.Questions branch n t m) {rows : Nat → Nat}
    (arrays : Arrays (sourceSlots clauses q) rows) : Input branch n t rows :=
  (sourceSigns clauses q, encodeArrays clauses q arrays)

def encodeTape (clauses : Fin m → SourceClause.NormalizedClause v)
    (q : PreliminarySampler.Questions branch n t m) (rows repeats : Nat → Nat)
    {d : Nat} (p : Path branch n d)
    (tape : WholeArraySampler.Tape rows repeats p (sourceSlots clauses q)) :
    Input branch n t rows :=
  encodeInput clauses q (WholeArraySampler.evaluate rows repeats p (sourceSlots clauses q) tape)

end Source

def outputEquiv (branch : Nat → Nat) (n : Nat) (rows : Nat → Nat) :
    Output branch n rows ≃ Fin (Fintype.card (Output branch n rows)) :=
  Fintype.equivFin _

def numberedShapes (signs : SignTuple branch n t) :
    Fin (TreeCanonical.locationCount branch n t) → CanonicalKeyShape.Shape :=
  fun j => .clause (signs ((TreeCanonical.numbering branch n t).symm j).1
    ((TreeCanonical.numbering branch n t).symm j).2)

def dummyTreeSlots (signs : SignTuple branch n t) :
    Slots branch n → Fin t → MixedSupport.Slot :=
  fun leaf k => CanonicalKeyShape.dummy (.clause (signs leaf k))

def dummyNumberedEquiv (signs : SignTuple branch n t) :
    MixedSupport.Assignment (CanonicalKeyShape.dummySlots (numberedShapes signs)) ≃
      EncodedAssignment branch n t :=
  (TreeCanonical.assignmentEquiv (dummyTreeSlots signs)).symm.trans (assignmentEquiv signs)

def shapeInput {rows : Nat → Nat} (data : Input branch n t rows) :
    CanonicalKeyShape.Input (TreeCanonical.locationCount branch n t)
      (Fintype.card (Output branch n rows)) :=
  ⟨numberedShapes data.1,
    fun x => outputEquiv branch n rows (tableJoint data.2 (dummyNumberedEquiv data.1 x))⟩


variable {v m : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (q : PreliminarySampler.Questions branch n t m) {rows : Nat → Nat}
  (arrays : Arrays (sourceSlots clauses q) rows)

theorem shapeInput_encodeInput :
    shapeInput (encodeInput clauses q arrays) =
      CanonicalKeyShape.input (TreeCanonical.numberedSlots (sourceSlots clauses q))
        (outputEquiv branch n rows ∘
          TreeCanonical.numberedFunction (sourceSlots clauses q) (fullJoint arrays)) := by
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    funext x
    change outputEquiv branch n rows
        (fullJoint arrays ((sourceAssignmentEquiv clauses q).symm
          (sourceAssignmentEquiv clauses q
            ((TreeCanonical.assignmentEquiv (sourceSlots clauses q)).symm x)))) =
      outputEquiv branch n rows
        (fullJoint arrays ((TreeCanonical.assignmentEquiv (sourceSlots clauses q)).symm x))
    rw [Equiv.symm_apply_apply]

end
end PerfectCompleteness.MetadataFreeSampler

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_MetadataFreeTapeLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftKeys_length _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_accepts _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightKeys_length _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_refl _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_refl_right _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_step _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.actualProjection_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightEquiv_apply _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_length _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset _root_.OAI.PerfectCompleteness.SourceQuestionOrder.tupleToQuestion_questionToTuple _root_.OAI.PerfectCompleteness.TerminalCalls.card_refl _root_.OAI.PerfectCompleteness.TerminalCalls.drawIndex_refl _root_.OAI.PerfectCompleteness.TerminalCalls.drawIndex_step _root_.OAI.PerfectCompleteness.TerminalCalls.isTerminal_recursive _root_.OAI.PerfectCompleteness.TerminalCalls.isTerminal_refl _root_.OAI.PerfectCompleteness.TerminalCalls.not_isTerminal_ordinary _root_.OAI.PerfectCompleteness.TerminalCalls.terminalSubtypeEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.MetadataFreeTape

open RecursiveSpaces DescendantSpaces TreeSourceSpaces
open HierarchicalArrays (Arrays Nodes)
open MetadataFreeSampler
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n d t v m : Nat}

def tapeEquiv (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (p : Path branch n d) :
    ∀ q : PreliminarySampler.Questions branch n t m,
      WholeArraySampler.Tape rows repeats p (sourceSlots clauses q) ≃
        WholeArraySampler.Tape rows repeats p (dummyTreeSlots (sourceSigns clauses q)) := by
  induction p with
  | refl n =>
      intro q
      exact Equiv.refl _
  | @step n d i p ih =>
      intro q
      refine Equiv.piCongrRight (fun k => ?_)
      rcases k with u | (u | j)
      · exact Equiv.refl _
      · exact ih (fun leaf k => q (i, leaf) k)
      · exact Equiv.refl _

@[simp] theorem tapeEquiv_root (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n d)
    (q : PreliminarySampler.Questions branch (n + 1) t m)
    (ω : WholeArraySampler.Tape rows repeats (.step i p) (sourceSlots clauses q)) :
    tapeEquiv clauses rows repeats (.step i p) q ω (.inl ()) = ω (.inl ()) := rfl

@[simp] theorem tapeEquiv_selected (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n d)
    (q : PreliminarySampler.Questions branch (n + 1) t m)
    (ω : WholeArraySampler.Tape rows repeats (.step i p) (sourceSlots clauses q)) :
    tapeEquiv clauses rows repeats (.step i p) q ω (.inr (.inl ())) =
      tapeEquiv clauses rows repeats p (fun leaf k => q (i, leaf) k)
        (ω (.inr (.inl ()))) := rfl

@[simp] theorem tapeEquiv_ordinary (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n d)
    (q : PreliminarySampler.Questions branch (n + 1) t m)
    (ω : WholeArraySampler.Tape rows repeats (.step i p) (sourceSlots clauses q))
    (j : RecursiveSampler.OffPath i) :
    tapeEquiv clauses rows repeats (.step i p) q ω (.inr (.inr j)) =
      ω (.inr (.inr j)) := rfl

theorem evaluate_tapeEquiv (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (p : Path branch n d) :
    ∀ (q : PreliminarySampler.Questions branch n t m)
      (ω : WholeArraySampler.Tape rows repeats p (sourceSlots clauses q)),
      WholeArraySampler.evaluate rows repeats p (dummyTreeSlots (sourceSigns clauses q))
          (tapeEquiv clauses rows repeats p q ω) =
        WholeArraySampler.evaluate rows repeats p (sourceSlots clauses q) ω := by
  induction p with
  | refl n =>
      intro q ω
      rfl
  | @step n d i p ih =>
      intro q ω
      funext node
      rcases node with u | ⟨j, node⟩
      · cases u
        rfl
      · by_cases hji : j = i
        · subst j
          have hinner := congrFun
            (ih (fun leaf k => q (i, leaf) k) (ω (.inr (.inl ())))) node
          exact (WholeArraySampler.evaluate_selected rows repeats i p
            (dummyTreeSlots (sourceSigns clauses q))
            (tapeEquiv clauses rows repeats (.step i p) q ω) node).trans
              (hinner.trans (WholeArraySampler.evaluate_selected rows repeats i p
                (sourceSlots clauses q) ω node).symm)
        · let off : RecursiveSampler.OffPath i := ⟨j, hji⟩
          exact (WholeArraySampler.evaluate_ordinary rows repeats i p
            (dummyTreeSlots (sourceSigns clauses q))
            (tapeEquiv clauses rows repeats (.step i p) q ω) off node).trans
              (WholeArraySampler.evaluate_ordinary rows repeats i p
                (sourceSlots clauses q) ω off node).symm

def evaluateSignedTape (signs : SignTuple branch n t) (rows repeats : Nat → Nat)
    (p : Path branch n d)
    (ω : WholeArraySampler.Tape rows repeats p (dummyTreeSlots signs)) :
    MetadataFreeSampler.Input branch n t rows :=
  (signs, fun node row x =>
    HierarchicalArrays.joint
      (WholeArraySampler.evaluate rows repeats p (dummyTreeSlots signs) ω)
      ((assignmentEquiv signs).symm x) node row)

theorem evaluateSignedTape_tapeEquiv
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (q : PreliminarySampler.Questions branch n t m) (rows repeats : Nat → Nat)
    (p : Path branch n d)
    (ω : WholeArraySampler.Tape rows repeats p (sourceSlots clauses q)) :
    evaluateSignedTape (sourceSigns clauses q) rows repeats p
        (tapeEquiv clauses rows repeats p q ω) =
      MetadataFreeSampler.encodeTape clauses q rows repeats p ω := by
  apply Prod.ext
  · rfl
  · funext node row x
    exact congrArg
      (fun arrays : Arrays (sourceSlots clauses q) rows =>
        HierarchicalArrays.joint arrays ((sourceAssignmentEquiv clauses q).symm x) node row)
      (evaluate_tapeEquiv clauses rows repeats p q ω)

abbrev Input (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) :=
  Σ signs : SignTuple branch n t, Σ leaf : Slots branch n,
    WholeArraySampler.Tape rows repeats (GeometricPath.leafPath leaf) (dummyTreeSlots signs) ×
      PreliminarySampler.Choice rows leaf

def evaluate {rows repeats : Nat → Nat} (data : Input branch n t rows repeats) :
    MetadataFreeSampler.Input branch n t rows :=
  evaluateSignedTape data.1 rows repeats (GeometricPath.leafPath data.2.1) data.2.2.1

def encodeRaw (clauses : Fin m → SourceClause.NormalizedClause v) (rows repeats : Nat → Nat)
    (e : PreliminarySampler.Raw clauses branch n t rows repeats) : Input branch n t rows repeats :=
  ⟨sourceSigns clauses e.1.1, e.1.2,
    tapeEquiv clauses rows repeats (GeometricPath.leafPath e.1.2) e.1.1 e.2.1, e.2.2⟩

theorem evaluate_encodeRaw (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    evaluate (encodeRaw clauses rows repeats e) =
      MetadataFreeSampler.encodeTape clauses e.1.1 rows repeats
        (GeometricPath.leafPath e.1.2) e.2.1 :=
  evaluateSignedTape_tapeEquiv clauses e.1.1 rows repeats (GeometricPath.leafPath e.1.2) e.2.1

def keyInput {rows repeats : Nat → Nat} (data : Input branch n t rows repeats) :
    CanonicalKeyShape.Input (TreeCanonical.locationCount branch n t)
      (Fintype.card (HierarchicalArrays.Output branch n rows)) :=
  MetadataFreeSampler.shapeInput (evaluate data)

theorem keyInput_encodeRaw (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    keyInput (encodeRaw clauses rows repeats e) =
      CanonicalKeyShape.input (TreeCanonical.numberedSlots (sourceSlots clauses e.1.1))
        (outputEquiv branch n rows ∘ TreeCanonical.numberedFunction (sourceSlots clauses e.1.1)
          (HierarchicalArrays.fullJoint
            (WholeArraySampler.evaluate rows repeats (GeometricPath.leafPath e.1.2)
              (sourceSlots clauses e.1.1) e.2.1))) := by
  rw [keyInput, evaluate_encodeRaw]
  exact shapeInput_encodeInput clauses e.1.1 _

end
end PerfectCompleteness.MetadataFreeTape


namespace PerfectCompleteness.MetadataTapeMachine

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MetadataFreeTape MetadataFreeSampler

noncomputable section

variable {branch : Nat → Nat} {n t : Nat} {rows repeats : Nat → Nat}

variable {v m : Nat}

theorem recoverKey_encodeRaw (side : CanonicalKeys.Side)
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    CanonicalKeyShapeMachine.recoverKey side
        (TreeCanonical.numberedSlots (sourceSlots clauses e.1.1))
        (MetadataFreeTape.keyInput (MetadataFreeTape.encodeRaw clauses rows repeats e)) =
      CanonicalKeys.key side (TreeCanonical.numberedSlots (sourceSlots clauses e.1.1))
        (TreeCanonical.numberedFunction (sourceSlots clauses e.1.1)
          (HierarchicalArrays.fullJoint
            (WholeArraySampler.evaluate rows repeats (GeometricPath.leafPath e.1.2)
              (sourceSlots clauses e.1.1) e.2.1))) := by
  rw [MetadataFreeTape.keyInput_encodeRaw, CanonicalKeyShapeMachine.recoverKey_input]
  exact CanonicalKeys.key_postcomp_equiv side _ _ (outputEquiv branch n rows)

end
end PerfectCompleteness.MetadataTapeMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_SamplerCardinalityLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SamplerRationality

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open RationalFiniteLaw
open scoped BigOperators Classical

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m t : Nat}

def recursiveTapeLaw (𝕜 : Type w) [Field 𝕜] [Finite 𝕜]
    (repeats : Nat → Nat) (p : Path branch n m) (A : Slots branch n → Type u)
    [∀ s, Finite (A s)] : RationalLaw (RecursiveSampler.tapeLaw 𝕜 repeats p A) := by
  rw [RecursiveSampler.tapeLaw_eq_uniform]
  exact RationalFiniteLaw.uniform (RecursiveSampler.Tape 𝕜 repeats p A)

def bucketTapeLaw (ℓ : Nat) (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) [∀ s, Finite (A s)] :
    RationalLaw (BucketSampler.recursiveTapeLaw ℓ repeats p A) :=
  RationalFiniteLaw.pi
    (fun _ : BucketSampler.Direction ℓ => RecursiveSampler.tapeLaw F2 repeats p A)
    (fun _ => recursiveTapeLaw F2 repeats p A)

def wholeArrayTapeLaw (rows repeats : Nat → Nat) (p : Path branch n m) :
    ∀ (slots : Slots branch n → Fin t → MixedSupport.Slot),
      RationalLaw (WholeArraySampler.tapeLaw rows repeats p slots) := by
  induction p with
  | refl n =>
      intro slots
      exact RationalFiniteLaw.uniform (Arrays slots rows)
  | @step n m i p ih =>
      intro slots
      letI : (k : WholeArraySampler.StepIndex i) → Fintype
          (WholeArraySampler.StepFactor
            (WholeArraySampler.RootTape rows repeats (.step i p) slots)
            (WholeArraySampler.Tape rows repeats p (childSlots slots i))
            (fun j => Arrays (childSlots slots j.val) rows) k) :=
        fun k => WholeArraySampler.stepFactorFintype _ _ _ k
      change RationalLaw (FiniteProduct.law (WholeArraySampler.componentLaw rows repeats i p slots))
      refine RationalFiniteLaw.pi (WholeArraySampler.componentLaw rows repeats i p slots) ?_
      intro k
      rcases k with u | (u | j)
      · exact bucketTapeLaw (rows (n + 1)) repeats (.step i p) (LeafDomain slots)
      · exact ih (childSlots slots i)
      · exact RationalFiniteLaw.uniform (Arrays (childSlots slots j.val) rows)


variable {v : Nat} {rows repeats : Nat → Nat}

def pathLaw (hbranch : ∀ k < n, 0 < branch k) :
    RationalLaw (GeometricPath.law n hbranch) := by
  letI := GeometricPath.slots_nonempty n hbranch
  exact RationalFiniteLaw.uniform (Slots branch n)

def choiceLaw (leaf : Slots branch n) (hn : 0 < n)
    (hrows : ∀ k, 0 < rows (k + 1)) :
    RationalLaw (PreliminarySampler.choiceLaw leaf hn hrows) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  apply RationalFiniteLaw.sigma (RationalFiniteLaw.uniform (Fin n))
  intro level
  letI : Nonempty (BucketSampler.Direction
      (rows (Nodes.height (GeometricPath.nodeAtLevel leaf level)))) :=
    PreliminarySampler.directionNonempty _ (by
      rw [GeometricPath.nodeAtLevel_height]
      exact hrows level.val)
  exact RationalFiniteLaw.uniform _

end
end PerfectCompleteness.SamplerRationality

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_MetadataFreeLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.MetadataFreeLaw

open RecursiveSpaces DescendantSpaces TreeSourceSpaces
open MetadataFreeSampler MetadataFreeTape
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n d t v m : Nat}

theorem tape_weight_eq (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (p : Path branch n d) :
    ∀ (q : PreliminarySampler.Questions branch n t m)
      (ω : WholeArraySampler.Tape rows repeats p (sourceSlots clauses q)),
      (WholeArraySampler.tapeLaw rows repeats p (sourceSlots clauses q)).weight ω =
        (WholeArraySampler.tapeLaw rows repeats p (dummyTreeSlots (sourceSigns clauses q))).weight
          (tapeEquiv clauses rows repeats p q ω) := by
  induction p with
  | refl n =>
      intro q ω
      rfl
  | @step n d i p ih =>
      intro q ω
      change (∏ k : WholeArraySampler.StepIndex i,
        (WholeArraySampler.componentLaw rows repeats i p (sourceSlots clauses q) k).weight (ω k)) =
        ∏ k : WholeArraySampler.StepIndex i,
          (WholeArraySampler.componentLaw rows repeats i p
            (dummyTreeSlots (sourceSigns clauses q)) k).weight
              (tapeEquiv clauses rows repeats (.step i p) q ω k)
      apply Finset.prod_congr rfl
      intro k _
      rcases k with u | (u | j)
      · rfl
      · cases u
        exact ih (fun leaf k => q (i, leaf) k) (ω (.inr (.inl ())))
      · rfl

abbrev SignedOutcome (signs : SignTuple branch n t) (rows repeats : Nat → Nat) :=
  Σ leaf : Slots branch n,
    WholeArraySampler.Tape rows repeats (GeometricPath.leafPath leaf) (dummyTreeSlots signs) ×
      PreliminarySampler.Choice rows leaf

def signedLaw (signs : SignTuple branch n t) (rows repeats : Nat → Nat)
    (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
    (hrows : ∀ k, 0 < rows (k + 1)) : FiniteDistribution (SignedOutcome signs rows repeats) :=
  CompletionSoundness.sigmaLaw (GeometricPath.law n hbranch) fun leaf =>
    (WholeArraySampler.tapeLaw rows repeats (GeometricPath.leafPath leaf) (dummyTreeSlots signs)).product
      (PreliminarySampler.choiceLaw leaf hn hrows)

def signedRationalLaw (signs : SignTuple branch n t) (rows repeats : Nat → Nat)
    (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1)) :
    RationalFiniteLaw.RationalLaw (signedLaw signs rows repeats hn hbranch hrows) :=
  RationalFiniteLaw.sigma (SamplerRationality.pathLaw hbranch) fun leaf =>
    RationalFiniteLaw.product
      (SamplerRationality.wholeArrayTapeLaw rows repeats (GeometricPath.leafPath leaf)
        (dummyTreeSlots signs))
      (SamplerRationality.choiceLaw leaf hn hrows)

def encodeOutcome (clauses : Fin m → SourceClause.NormalizedClause v) (rows repeats : Nat → Nat)
    (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    SignedOutcome (sourceSigns clauses e.1.1) rows repeats :=
  ⟨e.1.2, tapeEquiv clauses rows repeats (GeometricPath.leafPath e.1.2) e.1.1 e.2.1, e.2.2⟩

theorem raw_weight_eq [NeZero m] (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
    (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    (PreliminarySampler.law clauses rows repeats hn hbranch hrows).weight e =
      (1 / (Fintype.card (PreliminarySampler.Questions branch n t m) : ℝ)) *
        (signedLaw (sourceSigns clauses e.1.1) rows repeats hn hbranch hrows).weight
          (encodeOutcome clauses rows repeats e) := by
  change ((1 / (Fintype.card (PreliminarySampler.Questions branch n t m) : ℝ)) *
      (GeometricPath.law n hbranch).weight e.1.2) *
      ((WholeArraySampler.tapeLaw rows repeats (GeometricPath.leafPath e.1.2)
        (sourceSlots clauses e.1.1)).weight e.2.1 *
        (PreliminarySampler.choiceLaw e.1.2 hn hrows).weight e.2.2) =
    (1 / (Fintype.card (PreliminarySampler.Questions branch n t m) : ℝ)) *
      ((GeometricPath.law n hbranch).weight e.1.2 *
        ((WholeArraySampler.tapeLaw rows repeats (GeometricPath.leafPath e.1.2)
          (dummyTreeSlots (sourceSigns clauses e.1.1))).weight
            (tapeEquiv clauses rows repeats (GeometricPath.leafPath e.1.2) e.1.1 e.2.1) *
          (PreliminarySampler.choiceLaw e.1.2 hn hrows).weight e.2.2))
  rw [tape_weight_eq clauses rows repeats (GeometricPath.leafPath e.1.2) e.1.1 e.2.1]
  exact mul_assoc _ _ _

def rawEquiv (clauses : Fin m → SourceClause.NormalizedClause v) (rows repeats : Nat → Nat) :
    PreliminarySampler.Raw clauses branch n t rows repeats ≃
      (Σ q : PreliminarySampler.Questions branch n t m,
        SignedOutcome (sourceSigns clauses q) rows repeats) where
  toFun e := ⟨e.1.1, encodeOutcome clauses rows repeats e⟩
  invFun y := ⟨(y.1, y.2.1),
    (tapeEquiv clauses rows repeats (GeometricPath.leafPath y.2.1) y.1).symm y.2.2.1,
    y.2.2.2⟩
  left_inv := by
    rintro ⟨⟨q, leaf⟩, ω, choice⟩
    simp only [encodeOutcome]
    exact congrArg
      (fun tape : WholeArraySampler.Tape rows repeats (GeometricPath.leafPath leaf)
          (sourceSlots clauses q) =>
        (⟨(q, leaf), tape, choice⟩ : PreliminarySampler.Raw clauses branch n t rows repeats))
      ((tapeEquiv clauses rows repeats (GeometricPath.leafPath leaf) q).symm_apply_apply ω)
  right_inv := by
    rintro ⟨q, leaf, ω, choice⟩
    simp only [encodeOutcome, Equiv.apply_symm_apply]

end
end PerfectCompleteness.MetadataFreeLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_RawOccurrenceOrderLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SignedMultiplicity

open RecursiveSpaces MetadataFreeSampler MetadataFreeLaw
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat)
    (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))

def weights (signs : SignTuple branch n t) : SignedOutcome signs rows repeats → ℚ :=
  (signedRationalLaw signs rows repeats hn hbranch hrows).weights

theorem weights_positive (signs : SignTuple branch n t) (e : SignedOutcome signs rows repeats) :
    0 < weights branch n t rows repeats hn hbranch hrows signs e :=
  (signedRationalLaw signs rows repeats hn hbranch hrows).positive e

theorem weights_total (signs : SignTuple branch n t) :
    (∑ e, weights branch n t rows repeats hn hbranch hrows signs e) = 1 :=
  (signedRationalLaw signs rows repeats hn hbranch hrows).total

def baseDenominator : Nat :=
  ExactRationalMultiplicity.commonDenominator (weights branch n t rows repeats hn hbranch hrows)

def baseCopies (signs : SignTuple branch n t) (e : SignedOutcome signs rows repeats) : Nat :=
  ExactRationalMultiplicity.multiplicity (weights branch n t rows repeats hn hbranch hrows) signs e

theorem baseDenominator_positive : 0 < baseDenominator branch n t rows repeats hn hbranch hrows :=
  ExactRationalMultiplicity.commonDenominator_pos _

theorem baseCopies_positive (signs : SignTuple branch n t) (e : SignedOutcome signs rows repeats) :
    0 < baseCopies branch n t rows repeats hn hbranch hrows signs e :=
  ExactRationalMultiplicity.multiplicity_pos _
    (weights_positive branch n t rows repeats hn hbranch hrows) signs e

theorem baseCopies_total (signs : SignTuple branch n t) :
    (∑ e, baseCopies branch n t rows repeats hn hbranch hrows signs e) =
      baseDenominator branch n t rows repeats hn hbranch hrows :=
  ExactRationalMultiplicity.multiplicity_sum _
    (weights_positive branch n t rows repeats hn hbranch hrows)
    (weights_total branch n t rows repeats hn hbranch hrows) signs

theorem baseCopies_ratio (signs : SignTuple branch n t) (e : SignedOutcome signs rows repeats) :
    (baseCopies branch n t rows repeats hn hbranch hrows signs e : ℚ) /
        baseDenominator branch n t rows repeats hn hbranch hrows =
      weights branch n t rows repeats hn hbranch hrows signs e :=
  ExactRationalMultiplicity.multiplicity_div _
    (weights_positive branch n t rows repeats hn hbranch hrows) signs e

def denominator (q : Nat) : Nat :=
  ExactSeedMultiplicity.denominator (baseDenominator branch n t rows repeats hn hbranch hrows) (2 * q)

theorem denominator_positive (q : Nat) :
    0 < denominator branch n t rows repeats hn hbranch hrows q :=
  ExactSeedMultiplicity.denominator_positive
    (baseDenominator_positive branch n t rows repeats hn hbranch hrows) (2 * q)

end
end PerfectCompleteness.SignedMultiplicity

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedQueryCodec
attribute [-instance] _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftKeys_length _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_accepts _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightKeys_length _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.actualProjection_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.FixedQueryCodec

open HierarchicalArrays (Nodes Block)
open MixedSupport
open scoped Classical

noncomputable section

abbrev LeftOutput (branch : Nat → Nat) (n : Nat) (rows : Nat → Nat) :=
  HierarchicalArrays.Output branch n rows

def leftCount (branch : Nat → Nat) (n : Nat) (rows : Nat → Nat) : Nat :=
  Fintype.card (LeftOutput branch n rows)

def leftEquiv (branch : Nat → Nat) (n : Nat) (rows : Nat → Nat) :
    LeftOutput branch n rows ≃ Fin (leftCount branch n rows) :=
  MetadataFreeSampler.outputEquiv branch n rows

def leftEncode (branch : Nat → Nat) (n : Nat) (rows : Nat → Nat) :
    LeftOutput branch n rows → Fin (leftCount branch n rows) :=
  leftEquiv branch n rows

theorem leftEncode_injective (branch : Nat → Nat) (n : Nat) (rows : Nat → Nat) :
    Function.Injective (leftEncode branch n rows) :=
  (leftEquiv branch n rows).injective

abbrev TestIndex (branch : Nat → Nat) (n : Nat) (rows : Nat → Nat) :=
  Σ node : Nodes branch n, BucketSampler.Direction (rows (Nodes.height node))

instance testIndexFintype (branch : Nat → Nat) (n : Nat) (rows : Nat → Nat) :
    Fintype (TestIndex branch n rows) := by
  unfold TestIndex
  infer_instance

variable {branch : Nat → Nat} {n t v m : Nat} {rows repeats : Nat → Nat}

abbrev RightOutput (θ : TestIndex branch n rows) : Type :=
  DirectionQuotient.Space θ.2.val ×
    (BlockQuotient.OtherBlocks (fun node : Nodes branch n => Block rows node) θ.1 × PUnit.{1})

instance rightOutputFintype (θ : TestIndex branch n rows) : Fintype (RightOutput θ) :=
  Fintype.ofFinite _

def project (θ : TestIndex branch n rows) : LeftOutput branch n rows → RightOutput θ :=
  BlockQuotient.projectBlock (I := Nodes branch n)
    (V := fun node : Nodes branch n => Block rows node) (B := PUnit.{1}) θ.1 θ.2.val

abbrev TaggedRight (branch : Nat → Nat) (n : Nat) (rows : Nat → Nat) : Type :=
  Σ θ : TestIndex branch n rows, RightOutput θ

instance taggedRightFintype (branch : Nat → Nat) (n : Nat) (rows : Nat → Nat) :
    Fintype (TaggedRight branch n rows) := by
  letI : (θ : TestIndex branch n rows) → Fintype (RightOutput θ) :=
    fun θ => rightOutputFintype θ
  unfold TaggedRight
  infer_instance

def rightCount (branch : Nat → Nat) (n : Nat) (rows : Nat → Nat) : Nat :=
  Fintype.card (TaggedRight branch n rows)

def rightEquiv (branch : Nat → Nat) (n : Nat) (rows : Nat → Nat) :
    TaggedRight branch n rows ≃ Fin (rightCount branch n rows) :=
  Fintype.equivFin _

def rightEncode (θ : TestIndex branch n rows) :
    RightOutput θ → Fin (rightCount branch n rows) :=
  fun z => rightEquiv branch n rows ⟨θ, z⟩

theorem rightEncode_injective (θ : TestIndex branch n rows) :
    Function.Injective (rightEncode θ) :=
  (rightEquiv branch n rows).injective.comp (sigma_mk_injective (i := θ))

def outputMap (θ : TestIndex branch n rows) :
    Fin (leftCount branch n rows) → Fin (rightCount branch n rows) :=
  fun a => rightEncode θ (project θ ((leftEquiv branch n rows).symm a))

@[simp] theorem outputMap_leftEncode (θ : TestIndex branch n rows)
    (y : LeftOutput branch n rows) :
    outputMap θ (leftEncode branch n rows y) = rightEncode θ (project θ y) := by
  change rightEncode θ (project θ
    ((leftEquiv branch n rows).symm (leftEquiv branch n rows y))) = _
  rw [(leftEquiv branch n rows).symm_apply_apply]

def decodedFiberEquiv (θ : TestIndex branch n rows) (z : RightOutput θ) :
    {a : Fin (leftCount branch n rows) //
      project θ ((leftEquiv branch n rows).symm a) = z} ≃
    {y : LeftOutput branch n rows // project θ y = z} :=
  Equiv.subtypeEquivOfSubtype (p := fun y : LeftOutput branch n rows => project θ y = z)
    (leftEquiv branch n rows).symm

theorem outputMap_fiber_le_two (θ : TestIndex branch n rows)
    (b : Fin (rightCount branch n rows)) :
    Nat.card {a : Fin (leftCount branch n rows) // outputMap θ a = b} ≤ 2 := by
  have hsmall : ∀ z : RightOutput θ,
      Nat.card {a : Fin (leftCount branch n rows) //
        project θ ((leftEquiv branch n rows).symm a) = z} ≤ 2 := by
    intro z
    have hc := (Nat.card_congr (decodedFiberEquiv θ z)).trans
      (BlockQuotient.card_projectBlock_fiber (I := Nodes branch n)
        (V := fun node : Nodes branch n => Block rows node) (B := PUnit.{1})
        θ.1 θ.2.val θ.2.property z)
    exact hc.le
  by_cases hb : ∃ z : RightOutput θ, rightEncode θ z = b
  · obtain ⟨z, rfl⟩ := hb
    let e :
        {a : Fin (leftCount branch n rows) // outputMap θ a = rightEncode θ z} ≃
        {a : Fin (leftCount branch n rows) //
          project θ ((leftEquiv branch n rows).symm a) = z} :=
      Equiv.subtypeEquivRight (fun a => by
        change (rightEncode θ (project θ ((leftEquiv branch n rows).symm a)) =
          rightEncode θ z) ↔ _
        exact ⟨fun h => (rightEncode_injective θ) h,
          fun h => congrArg (rightEncode θ) h⟩)
    exact (Nat.card_congr e).le.trans (hsmall z)
  · let : IsEmpty {a : Fin (leftCount branch n rows) // outputMap θ a = b} :=
      ⟨fun a => hb
        ⟨project θ ((leftEquiv branch n rows).symm a.val), a.property⟩⟩
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le 2

section Keys

variable {k : Nat}

theorem left_key (side : CanonicalKeys.Side) (slots : Fin k → Slot)
    (f : Assignment slots → LeftOutput branch n rows) :
    CanonicalKeys.key side slots (leftEncode branch n rows ∘ f) =
      CanonicalKeys.key side slots f :=
  CanonicalCoarseningEncoding.key_fine side slots f
    (leftEncode branch n rows) (leftEncode_injective branch n rows)

theorem right_key (side : CanonicalKeys.Side) (slots : Fin k → Slot)
    (f : Assignment slots → LeftOutput branch n rows) (θ : TestIndex branch n rows) :
    CanonicalKeys.key side slots (outputMap θ ∘ (leftEncode branch n rows ∘ f)) =
      CanonicalKeys.key side slots (project θ ∘ f) :=
  CanonicalCoarseningEncoding.key_coarse side slots f (project θ)
    (leftEncode branch n rows) (rightEncode θ) (outputMap θ)
    (rightEncode_injective θ) (outputMap_leftEncode θ)

end Keys

def leftTable {slots : RecursiveSpaces.Slots branch n → Fin t → Slot}
    (arrays : HierarchicalArrays.Arrays slots rows) :
    Assignment (TreeCanonical.numberedSlots slots) → Fin (leftCount branch n rows) :=
  leftEncode branch n rows ∘
    TreeCanonical.numberedFunction slots (HierarchicalArrays.fullJoint arrays)

theorem leftTable_key (side : CanonicalKeys.Side)
    {slots : RecursiveSpaces.Slots branch n → Fin t → Slot}
    (arrays : HierarchicalArrays.Arrays slots rows) :
    CanonicalKeys.key side (TreeCanonical.numberedSlots slots) (leftTable arrays) =
      TreeCanonical.key side slots (HierarchicalArrays.fullJoint arrays) :=
  left_key side (TreeCanonical.numberedSlots slots)
    (TreeCanonical.numberedFunction slots (HierarchicalArrays.fullJoint arrays))

def testIndex (data : MetadataFreeTape.Input branch n t rows repeats) :
    TestIndex branch n rows :=
  ⟨GeometricPath.nodeAtLevel data.2.1 data.2.2.2.1, data.2.2.2.2⟩

def rawTestIndex (clauses : Fin m → SourceClause.NormalizedClause v)
    (e : PreliminarySampler.Raw clauses branch n t rows repeats) : TestIndex branch n rows :=
  ⟨GeometricPath.nodeAtLevel e.1.2 e.2.2.1, e.2.2.2⟩

@[simp] theorem testIndex_encodeRaw (clauses : Fin m → SourceClause.NormalizedClause v)
    (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    testIndex (MetadataFreeTape.encodeRaw clauses rows repeats e) = rawTestIndex clauses e := rfl

def withProjection {a k l : Nat} (fine : CanonicalKeyShape.Input a k)
    (p : Fin k → Fin l) : CanonicalPartialTable.Input a k l :=
  ⟨fine.1, fine.2, p⟩

def partialInput (data : MetadataFreeTape.Input branch n t rows repeats) :
    CanonicalPartialTable.Input (TreeCanonical.locationCount branch n t)
      (leftCount branch n rows) (rightCount branch n rows) :=
  withProjection (MetadataFreeTape.keyInput data) (outputMap (testIndex data))

theorem partialInput_encodeRaw (clauses : Fin m → SourceClause.NormalizedClause v)
    (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    partialInput (MetadataFreeTape.encodeRaw clauses rows repeats e) =
      CanonicalPartialTable.input
        (TreeCanonical.numberedSlots (MetadataFreeSampler.sourceSlots clauses e.1.1))
        (leftTable (WholeArraySampler.evaluate rows repeats (GeometricPath.leafPath e.1.2)
          (MetadataFreeSampler.sourceSlots clauses e.1.1) e.2.1))
        (outputMap (rawTestIndex clauses e)) := by
  unfold partialInput
  rw [MetadataFreeTape.keyInput_encodeRaw, testIndex_encodeRaw]
  rfl

def rightInputOfPartial {a k l : Nat} (data : CanonicalPartialTable.Input a k l) :
    CanonicalKeyShape.Input a l :=
  ⟨data.1, data.2.2 ∘ data.2.1⟩

def rightKeyInput (data : MetadataFreeTape.Input branch n t rows repeats) :
    CanonicalKeyShape.Input (TreeCanonical.locationCount branch n t)
      (rightCount branch n rows) :=
  rightInputOfPartial (partialInput data)

theorem rightKeyInput_encodeRaw (clauses : Fin m → SourceClause.NormalizedClause v)
    (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    rightKeyInput (MetadataFreeTape.encodeRaw clauses rows repeats e) =
      CanonicalKeyShape.input
        (TreeCanonical.numberedSlots (MetadataFreeSampler.sourceSlots clauses e.1.1))
        (outputMap (rawTestIndex clauses e) ∘
          leftTable (WholeArraySampler.evaluate rows repeats (GeometricPath.leafPath e.1.2)
            (MetadataFreeSampler.sourceSlots clauses e.1.1) e.2.1)) := by
  rw [rightKeyInput, partialInput_encodeRaw]
  rfl

theorem partialInput_admissible {q : Nat} (hq : 0 < q)
    (large : CanonicalKeyEncoding.partitionWidth (TreeCanonical.locationCount branch n t) ≤ q)
    (data : MetadataFreeTape.Input branch n t rows repeats) :
    LocalCompletionFamily.Admissible
      (CanonicalPartialTable.lookup hq large (partialInput data)) :=
  CanonicalPartialTable.admissible_of_output_fibers hq large (partialInput data)
    (outputMap_fiber_le_two (testIndex data))

end
end PerfectCompleteness.FixedQueryCodec

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_FiniteConstraintMachine
attribute [-instance] _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FiniteConstraintMachine

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MetadataFreeSampler

noncomputable section

variable {branch : Nat → Nat} {n t q : Nat} {rows repeats : Nat → Nat}
    (hq : 0 < q)
    (large : CanonicalKeyEncoding.partitionWidth (TreeCanonical.locationCount branch n t) ≤ q)

def localInput (data : MetadataFreeTape.Input branch n t rows repeats) :
    LocalCompletionFamily.Input q :=
  CanonicalPartialTable.lookup hq large (FixedQueryCodec.partialInput data)

def result (data : MetadataFreeTape.Input branch n t rows repeats) : LocalCompletionFamily.Result q :=
  LocalCompletionFamily.lookup hq (localInput hq large data)

theorem result_correct (data : MetadataFreeTape.Input branch n t rows repeats) :
    LocalCompletionFamily.Correct (localInput hq large data) (result hq large data) :=
  LocalCompletionFamily.lookup_correct hq _ (FixedQueryCodec.partialInput_admissible hq large data)

variable {v m : Nat}

theorem recover_right_key (clauses : Fin m → SourceClause.NormalizedClause v)
    (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    CanonicalKeyShapeMachine.recoverKey .right
        (TreeCanonical.numberedSlots (sourceSlots clauses e.1.1))
        (FixedQueryCodec.rightKeyInput (MetadataFreeTape.encodeRaw clauses rows repeats e)) =
      CanonicalKeys.key .right (TreeCanonical.numberedSlots (sourceSlots clauses e.1.1))
        (FixedQueryCodec.project (FixedQueryCodec.rawTestIndex clauses e) ∘
          TreeCanonical.numberedFunction (sourceSlots clauses e.1.1)
            (HierarchicalArrays.fullJoint
              (WholeArraySampler.evaluate rows repeats (GeometricPath.leafPath e.1.2)
                (sourceSlots clauses e.1.1) e.2.1))) := by
  rw [FixedQueryCodec.rightKeyInput_encodeRaw, CanonicalKeyShapeMachine.recoverKey_input]
  exact FixedQueryCodec.right_key .right _ _ (FixedQueryCodec.rawTestIndex clauses e)

theorem parsed_projection (data : MetadataFreeTape.Input branch n t rows repeats)
    (seed : Fin (LocalCompletionFamily.activeCount (result hq large data))) (a : Fin (2 * q)) :
    (LocalCompletionSerialization.projection (result_correct hq large data) seed).images[a] =
      LocalCompletionFamily.table (result hq large data) seed a :=
  LocalCompletionSerialization.projection_apply (result_correct hq large data) seed a

end
end PerfectCompleteness.FiniteConstraintMachine

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_SignedCompletionSchedule
attribute [-instance] _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketUniform.evaluateLinear_apply _root_.OAI.PerfectCompleteness.BucketUsefulCollision.fill_self _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.LowerDirectionFiber.complement_replace _root_.OAI.PerfectCompleteness.LowerDirectionFiber.complement_restore _root_.OAI.PerfectCompleteness.LowerDirectionFiber.pairCoordinates_apply _root_.OAI.PerfectCompleteness.LowerDirectionFiber.pivot_value _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_complement _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_other _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_pivot _root_.OAI.PerfectCompleteness.LowerDirectionFiber.split_apply _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SignedCompletionSchedule


open MetadataFreeSampler MetadataFreeLaw
open UniqueGamesTheorem.Foundations.Games
open Turing UniqueGamesTheorem.Foundations.Complexity
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t q : Nat} {rows repeats : Nat → Nat}
  (hq : 0 < q)
  (large : CanonicalKeyEncoding.partitionWidth (TreeCanonical.locationCount branch n t) ≤ q)

def result (signs : SignTuple branch n t) (e : SignedOutcome signs rows repeats) :
    LocalCompletionFamily.Result q := FiniteConstraintMachine.result hq large ⟨signs, e⟩

def active (signs : SignTuple branch n t) (e : SignedOutcome signs rows repeats) : Nat :=
  LocalCompletionFamily.activeCount (result (rows := rows) (repeats := repeats) hq large signs e)

theorem active_positive (signs : SignTuple branch n t) (e : SignedOutcome signs rows repeats) :
    0 < active (rows := rows) (repeats := repeats) hq large signs e := LocalCompletionFamily.activeCount_positive _

theorem active_le (signs : SignTuple branch n t) (e : SignedOutcome signs rows repeats) :
    active (rows := rows) (repeats := repeats) hq large signs e ≤ 2 * q := LocalCompletionFamily.activeCount_le _

abbrev Completed (signs : SignTuple branch n t) :=
  Σ e : SignedOutcome signs rows repeats, Fin (active (rows := rows) (repeats := repeats) hq large signs e)

abbrev Descriptor := Σ signs : SignTuple branch n t, Completed (rows := rows) (repeats := repeats) hq large signs

def descriptorTable (descriptor : Descriptor (rows := rows) (repeats := repeats) hq large) : Fin (2 * q) → Fin q :=
  LocalCompletionFamily.table (result (rows := rows) (repeats := repeats) hq large descriptor.1 descriptor.2.1) descriptor.2.2

theorem descriptorTable_eq_parsed (signs : SignTuple branch n t)
    (e : Completed (rows := rows) (repeats := repeats) hq large signs) (a : Fin (2 * q)) :
    descriptorTable (rows := rows) (repeats := repeats) hq large ⟨signs, e⟩ a =
      (LocalCompletionSerialization.projection
        (FiniteConstraintMachine.result_correct (rows := rows) (repeats := repeats) hq large ⟨signs, e.1⟩) e.2).images[a] :=
  (FiniteConstraintMachine.parsed_projection (rows := rows) (repeats := repeats) hq large ⟨signs, e.1⟩ e.2 a).symm

def seedLaw (signs : SignTuple branch n t) (e : SignedOutcome signs rows repeats) :
    FiniteDistribution (Fin (active (rows := rows) (repeats := repeats) hq large signs e)) := by
  letI : Nonempty (Fin (active (rows := rows) (repeats := repeats) hq large signs e)) := ⟨⟨0, active_positive (rows := rows) (repeats := repeats) hq large signs e⟩⟩
  exact FiniteDistribution.uniform _

variable (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1))

def law (signs : SignTuple branch n t) : FiniteDistribution (Completed (rows := rows) (repeats := repeats) hq large signs) :=
  CompletionSoundness.sigmaLaw (signedLaw signs rows repeats hn hbranch hrows)
    (seedLaw (rows := rows) (repeats := repeats) hq large signs)

theorem law_weight (signs : SignTuple branch n t) (e : Completed (rows := rows) (repeats := repeats) hq large signs) :
    (law (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs).weight e =
      (signedLaw signs rows repeats hn hbranch hrows).weight e.1 /
        active (rows := rows) (repeats := repeats) hq large signs e.1 := by
  change (signedLaw signs rows repeats hn hbranch hrows).weight e.1 *
    (1 / (Fintype.card (Fin (active (rows := rows) (repeats := repeats) hq large signs e.1)) : ℝ)) = _
  simp only [Fintype.card_fin, div_eq_mul_inv, one_mul]

def count (signs : SignTuple branch n t) (e : Completed (rows := rows) (repeats := repeats) hq large signs) : Nat :=
  ExactSeedMultiplicity.perSeed (2 * q) (active (rows := rows) (repeats := repeats) hq large signs e.1)
    (SignedMultiplicity.baseCopies branch n t rows repeats hn hbranch hrows signs e.1)

theorem count_positive (signs : SignTuple branch n t) (e : Completed (rows := rows) (repeats := repeats) hq large signs) :
    0 < count (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs e :=
  ExactSeedMultiplicity.perSeed_positive (active_positive (rows := rows) (repeats := repeats) hq large signs e.1)
    (active_le (rows := rows) (repeats := repeats) hq large signs e.1)
    (SignedMultiplicity.baseCopies_positive branch n t rows repeats hn hbranch hrows signs e.1)

theorem count_total (signs : SignTuple branch n t) :
    (∑ e, count (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs e) =
      SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q :=
  ExactSeedMultiplicity.sum_multiplicity
    (SignedMultiplicity.baseCopies branch n t rows repeats hn hbranch hrows signs)
    (active (rows := rows) (repeats := repeats) hq large signs) (active_positive (rows := rows) (repeats := repeats) hq large signs) (active_le (rows := rows) (repeats := repeats) hq large signs)
    (SignedMultiplicity.baseCopies_total branch n t rows repeats hn hbranch hrows signs)

theorem count_ratio (signs : SignTuple branch n t) (e : Completed (rows := rows) (repeats := repeats) hq large signs) :
    (count (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs e : ℚ) /
        SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q =
      SignedMultiplicity.weights branch n t rows repeats hn hbranch hrows signs e.1 /
        active (rows := rows) (repeats := repeats) hq large signs e.1 := by
  change (ExactSeedMultiplicity.perSeed (2 * q) (active (rows := rows) (repeats := repeats) hq large signs e.1)
      (SignedMultiplicity.baseCopies branch n t rows repeats hn hbranch hrows signs e.1) : ℚ) /
    ExactSeedMultiplicity.denominator
      (SignedMultiplicity.baseDenominator branch n t rows repeats hn hbranch hrows) (2 * q) = _
  rw [ExactSeedMultiplicity.perSeed_ratio
    (SignedMultiplicity.baseDenominator_positive branch n t rows repeats hn hbranch hrows)
    (active_positive (rows := rows) (repeats := repeats) hq large signs e.1) (active_le (rows := rows) (repeats := repeats) hq large signs e.1),
    SignedMultiplicity.baseCopies_ratio]

theorem count_mass (signs : SignTuple branch n t) (e : Completed (rows := rows) (repeats := repeats) hq large signs) :
    (count (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs e : ℝ) /
        SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q =
      (law (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs).weight e := by
  have h := congrArg (fun z : ℚ => (z : ℝ)) (count_ratio (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs e)
  simp only [Rat.cast_div, Rat.cast_natCast] at h
  rw [law_weight, (signedRationalLaw signs rows repeats hn hbranch hrows).cast_weight]
  exact h

def schedule (signs : SignTuple branch n t) : List (Completed (rows := rows) (repeats := repeats) hq large signs) :=
  ExactConditionalOutput.copies (count (rows := rows) (repeats := repeats) hq large hn hbranch hrows) signs

theorem schedule_length (signs : SignTuple branch n t) :
    (schedule (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs).length =
      SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q := by
  rw [schedule, ExactConditionalOutput.copies_length, count_total]

theorem schedule_acceptance (signs : SignTuple branch n t)
    (accepts : Completed (rows := rows) (repeats := repeats) hq large signs → Bool) :
    (((schedule (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs).filter accepts).length : ℝ) /
        (schedule (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs).length =
      (law (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs).probability accepts := by
  rw [schedule_length]
  change (((ExactConditionalOutput.copies (count (rows := rows) (repeats := repeats) hq large hn hbranch hrows) signs).filter
    accepts).length : ℝ) / _ = _
  rw [ExactConditionalOutput.copies_filter_length, Nat.cast_sum, Finset.sum_div,
    FiniteDistribution.probability]
  apply Finset.sum_congr rfl
  intro e _
  cases accepts e <;> simp [count_mass]

end
end PerfectCompleteness.SignedCompletionSchedule

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_DescriptorKeyTemplate
attribute [-instance] _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.actualProjection_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.clauseAnswerEquiv_decode _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.clauseAnswerEquiv_symm_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.DescriptorKeyTemplate

open CanonicalKeys CanonicalKeyShape MixedSupport MetadataFreeSampler ClauseSupport
open scoped Classical

noncomputable section

def occurrence : Slot → Nat
  | .clause c _ _ => c
  | .bit _ => 0

def variableIDs : Slot → Fin 3 → Nat
  | .clause _ ids _ => ids
  | .bit v => fun _ => v

@[simp] theorem actualSlot_erase (slot : Slot) :
    KeyMetadataMachine.actualSlot (erase slot) (occurrence slot) (variableIDs slot) = slot := by
  cases slot <;> rfl

structure Template (width : Nat) where
  shapes : Fin width → Shape
  modes : Fin width → SupportMode
  partition : Set (Set (Fin width → ReducedValue))

instance instFiniteTemplate (width : Nat) : Finite (Template width) := by
  let : Finite ReducedValue := ReducedDomains.reducedValue_finite
  apply Finite.of_injective
    (fun template : Template width => (template.shapes, template.modes, template.partition))
  intro a b h
  cases a
  cases b
  cases h
  rfl

def ofInput {width k : Nat} (data : CanonicalKeyShape.Input width k) : Template width :=
  ⟨data.1, inputModes data, inputPartition data⟩

def recover {width : Nat} (side : Side) (template : Template width)
    (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat) : Key width :=
  CanonicalKeyMachine.recoveredKey template.shapes template.modes side template.partition ids vars

theorem recover_ofInput {width k : Nat} (side : Side) (slots : Fin width → Slot)
    (data : CanonicalKeyShape.Input width k) (sameShape : data.1 = shape slots) :
    recover side (ofInput data) (fun i => occurrence (slots i)) (fun i => variableIDs (slots i)) =
      CanonicalKeyShapeMachine.recoverKey side slots data := by
  have restored : CanonicalKeyMachine.actualSlots data.1
      (fun i => occurrence (slots i)) (fun i => variableIDs (slots i)) = slots := by
    funext i
    rw [sameShape]
    exact actualSlot_erase (slots i)
  change CanonicalKeyMachine.recoveredKey data.1 (inputModes data) side
    (inputPartition data) _ _ = _
  unfold CanonicalKeyMachine.recoveredKey
  rw [restored]
  rfl

variable {branch : Nat → Nat} {n t q : Nat} {rows repeats : Nat → Nat}
    (hq : 0 < q)
    (large : CanonicalKeyEncoding.partitionWidth (TreeCanonical.locationCount branch n t) ≤ q)

def tapeInput (descriptor : SignedCompletionSchedule.Descriptor
    (rows := rows) (repeats := repeats) hq large) :
    MetadataFreeTape.Input branch n t rows repeats := ⟨descriptor.1, descriptor.2.1⟩

def ofTape (side : Side) (data : MetadataFreeTape.Input branch n t rows repeats) :
    Template (TreeCanonical.locationCount branch n t) :=
  match side with
  | .left => ofInput (MetadataFreeTape.keyInput data)
  | .right => ofInput (FixedQueryCodec.rightKeyInput data)

def ofDescriptor (side : Side) (descriptor : SignedCompletionSchedule.Descriptor
    (rows := rows) (repeats := repeats) hq large) :
    Template (TreeCanonical.locationCount branch n t) := ofTape side (tapeInput hq large descriptor)

variable {v m : Nat}

theorem recover_left (clauses : Fin m → SourceClause.NormalizedClause v)
    (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    let slots := TreeCanonical.numberedSlots (sourceSlots clauses e.1.1)
    recover .left (ofTape .left (MetadataFreeTape.encodeRaw clauses rows repeats e))
        (fun i => occurrence (slots i)) (fun i => variableIDs (slots i)) =
      CanonicalKeys.key .left slots
        (TreeCanonical.numberedFunction (sourceSlots clauses e.1.1)
          (HierarchicalArrays.fullJoint
            (WholeArraySampler.evaluate rows repeats (GeometricPath.leafPath e.1.2)
              (sourceSlots clauses e.1.1) e.2.1))) := by
  dsimp only
  rw [ofTape, recover_ofInput]
  · exact MetadataTapeMachine.recoverKey_encodeRaw .left clauses e
  · rw [MetadataFreeTape.keyInput_encodeRaw]
    rfl

theorem recover_right (clauses : Fin m → SourceClause.NormalizedClause v)
    (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    let slots := TreeCanonical.numberedSlots (sourceSlots clauses e.1.1)
    recover .right (ofTape .right (MetadataFreeTape.encodeRaw clauses rows repeats e))
        (fun i => occurrence (slots i)) (fun i => variableIDs (slots i)) =
      CanonicalKeys.key .right slots
        (FixedQueryCodec.project (FixedQueryCodec.rawTestIndex clauses e) ∘
          TreeCanonical.numberedFunction (sourceSlots clauses e.1.1)
            (HierarchicalArrays.fullJoint
              (WholeArraySampler.evaluate rows repeats (GeometricPath.leafPath e.1.2)
                (sourceSlots clauses e.1.1) e.2.1))) := by
  dsimp only
  rw [ofTape, recover_ofInput]
  · exact FiniteConstraintMachine.recover_right_key clauses e
  · rw [FixedQueryCodec.rightKeyInput_encodeRaw]
    rfl

end
end PerfectCompleteness.DescriptorKeyTemplate

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_OwnInputAffineSliceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.OwnInputRawAssembly

noncomputable section

open scoped Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays
open OwnInputReference (ScalarSample UpperSpace UpperVector Cut)

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat) (upper lower : Nodes branch n)

variable (W : Submodule F2 (UpperVector rows upper))
  (repeats : Nat → Nat) (cut : Cut upper lower)

def scalarEval : ScalarSample slots upper lower repeats cut → UpperSpace slots upper :=
  RecursiveSampler.evaluate F2 repeats cut.path (LeafDomain (nodeSlots slots upper))

end
end PerfectCompleteness.OwnInputRawAssembly

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalProjectedSliceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HierarchicalProjectedMeeting

noncomputable section

open scoped Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype
attribute [local instance] RightDecoder.characterFintype RightDecoder.scalarFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots projected : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ s j, MixedSupport.Projection (slots s j) (projected s j))
  (upper : Nodes branch n) (lowerLevel : Nat)
  (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)

local instance rowSpaceFintype_re23f58_2 : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _
local instance valueFintype_re23f58_1 : Fintype
    (Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :=
  Fintype.ofFinite _
local instance upperDualFintype : Fintype (Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)

end
end PerfectCompleteness.HierarchicalProjectedMeeting


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SignedScheduleIndex
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SignedScheduleIndex

open MetadataFreeSampler SignedCompletionSchedule
open Turing UniqueGamesTheorem.Foundations.Complexity
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t q : Nat} {rows repeats : Nat → Nat}
  (hq : 0 < q)
  (large : CanonicalKeyEncoding.partitionWidth (TreeCanonical.locationCount branch n t) ≤ q)
  (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1))

local notation "D" => SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q

def atIndex (signs : SignTuple branch n t) (i : Fin D) : Descriptor (rows := rows) (repeats := repeats) hq large :=
  ⟨signs, (schedule (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs).get
    (Fin.cast (schedule_length (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs).symm i)⟩

@[simp] theorem atIndex_signs (signs : SignTuple branch n t) (i : Fin D) :
    (atIndex hq large hn hbranch hrows signs i).1 = signs := rfl

def instruction {K Λ σ : Type} [Finite σ]
    (selectSigns : σ → SignTuple branch n t) (save : σ → Descriptor (rows := rows) (repeats := repeats) hq large → σ)
    (i : Fin D) (exit : Λ) : TM2.Stmt (fun _ : K => Bool) Λ σ :=
  .load (fun state => save state (atIndex hq large hn hbranch hrows (selectSigns state) i))
    (.goto (fun _ => exit))

theorem instruction_trace {K Λ σ : Type} [DecidableEq K] [Finite σ]
    (selectSigns : σ → SignTuple branch n t) (save : σ → Descriptor (rows := rows) (repeats := repeats) hq large → σ)
    (i : Fin D) (exit : Λ) (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (instruction hq large hn hbranch hrows selectSigns save i exit) state tapes =
      ⟨some exit, save state (atIndex hq large hn hbranch hrows (selectSigns state) i), tapes⟩ :=
  rfl

theorem step {K Λ σ : Type} [DecidableEq K] [Finite σ]
    (selectSigns : σ → SignTuple branch n t) (save : σ → Descriptor (rows := rows) (repeats := repeats) hq large → σ)
    (i : Fin D) (exit : Λ) (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (entry : Λ)
    (atEntry : program entry = instruction hq large hn hbranch hrows selectSigns save i exit)
    (state : σ) (tapes : K → List Bool) :
    TM2.step program ⟨some entry, state, tapes⟩ =
      some ⟨some exit, save state (atIndex hq large hn hbranch hrows (selectSigns state) i),
        tapes⟩ := by
  change some (TM2.stepAux (program entry) state tapes) = _
  rw [atEntry, instruction_trace]

def inTime {K Λ σ : Type} [DecidableEq K] [Finite σ]
    (selectSigns : σ → SignTuple branch n t) (save : σ → Descriptor (rows := rows) (repeats := repeats) hq large → σ)
    (i : Fin D) (exit : Λ) (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (entry : Λ)
    (atEntry : program entry = instruction hq large hn hbranch hrows selectSigns save i exit)
    (state : σ) (tapes : K → List Bool) :
    StateTransition.EvalsToInTime (TM2.step program) ⟨some entry, state, tapes⟩
      (some ⟨some exit,
        save state (atIndex hq large hn hbranch hrows (selectSigns state) i), tapes⟩) 1 where
  steps := 1
  evals_in_steps := step hq large hn hbranch hrows selectSigns save i exit
    program entry atEntry state tapes
  steps_le_m := Nat.le_refl 1

end
end PerfectCompleteness.SignedScheduleIndex

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourceClauseReaderMachineLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryFormula.compactLiteral_positive _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_variable_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_variables _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_current _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_remaining _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.baseAccepts_eq_true_iff _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.card_ClauseContext _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.card_VariableContext _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.localConsistent_eq_true_iff _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.validJ_eq_true_iff _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature.ofContext_sameName _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature.ofContext_selected _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature.ofContext_signs _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature.signatureSatisfies_ofContext _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.nBits_eq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.rawSourceList_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceSoundness.leftTable_answer _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_dart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_vertex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceClauseReaderMachine


open Turing
open UniqueGamesTheorem.Foundations
open Complexity Complexity.MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

def shape (signs : Signs) : CanonicalKeyShape.Shape :=
  .clause (signs 0, signs 1, signs 2)

def clauseShape {n : Nat} (clause : Target.Clause n) : CanonicalKeyShape.Shape :=
  shape (NormalizationReadMachine.clauseSigns clause)

@[simp] theorem clauseShape_eq {n : Nat} (clause : Target.Clause n) :
    clauseShape clause = .clause (clause[0].positive, clause[1].positive, clause[2].positive) := rfl

section Placement

variable {K Λ A : Type} [DecidableEq K]

def instruction (tape : Fin 4 → K) (labels : Label → Λ) (done rejected : Option Λ)
    (save : A → CanonicalKeyShape.Shape → A) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .read label => NormalizationReadMachine.instruction tape
      (fun label => labels (.read label)) (some (labels .publish)) rejected label
  | .publish =>
      .load (fun state => clean (save state.1.1 (shape state.1.2)) state.1.2)
        (exitAt (tape 0) done)

end Placement

end PerfectCompleteness.SourceClauseReaderMachine


namespace PerfectCompleteness.SourceOccurrenceEncoding

open UniqueGamesTheorem.Foundations Complexity Target

def recordWords {n : Nat} (index : Nat) (clause : Clause n) : List Nat :=
  index :: clauseWords clause

def records {n : Nat} (first : Nat) : List (Clause n) → List Nat
  | [] => []
  | clause :: clauses => recordWords first clause ++ records (first + 1) clauses

def body {n : Nat} (first : Nat) (clauses : List (Clause n)) : List Bool :=
  encodeWords (records first clauses)

def words (formula : Formula) : List Nat :=
  [formula.variables, formula.clauses.length] ++ records 0 formula.clauses

def bits (formula : Formula) : List Bool := encodeWords (words formula)

@[simp] theorem recordWords_length {n : Nat} (index : Nat) (clause : Clause n) :
    (recordWords index clause).length = 7 := by simp [recordWords]

@[simp] theorem records_length {n : Nat} (first : Nat) (clauses : List (Clause n)) :
    (records first clauses).length = 7 * clauses.length := by
  induction clauses generalizing first with
  | nil => rfl
  | cons clause clauses ih => simp [records, ih, Nat.mul_add]; omega

@[simp] theorem words_length (formula : Formula) :
    (words formula).length = 2 + 7 * formula.clauses.length := by simp [words]; omega

@[simp] theorem body_nil {n : Nat} (first : Nat) : body first ([] : List (Clause n)) = [] := rfl

theorem bits_eq (formula : Formula) :
    bits formula = encodeWord formula.variables ++ encodeWord formula.clauses.length ++
      body 0 formula.clauses := by
  simp only [bits, words, encodeWords_append, encodeWords, List.append_nil,
    body, List.append_assoc]

end PerfectCompleteness.SourceOccurrenceEncoding

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourceClauseLookupMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceClauseLookupMachine


open Turing UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition UniqueGamesTheorem.Reduction.MachineTransfer

def suffix (formula : Formula) (k : Nat) : List Bool :=
  SourceOccurrenceEncoding.body (k + 1) (formula.clauses.drop (k + 1))

end PerfectCompleteness.SourceClauseLookupMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourceCoordinateMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceCoordinateMachine


open Turing UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition UniqueGamesTheorem.Reduction.MachineTransfer

variable {K Λ A : Type} [DecidableEq K]

def instruction (tape : Fin 10 → K) (labels : Label → Λ) (done rejected : Option Λ)
    (save : A → CanonicalKeyShape.Shape → A) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .lookup l => SourceClauseLookupMachine.instruction (lookupTapes tape)
      (fun l => labels (.lookup l)) (some (labels .restore)) rejected l
  | .restore => loopAt (tape 5) (tape 6) id false (labels .restore)
      (some (labels (.read SourceClauseReaderMachine.main)))
  | .read l => SourceClauseReaderMachine.instruction (readerTapes tape)
      (fun l => labels (.read l)) done rejected save l

end PerfectCompleteness.SourceCoordinateMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceTupleData
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryFormula.compactLiteral_positive _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_variable_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_variables _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_current _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_remaining _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.baseAccepts_eq_true_iff _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.card_ClauseContext _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.card_VariableContext _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.localConsistent_eq_true_iff _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.validJ_eq_true_iff _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature.ofContext_sameName _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature.ofContext_selected _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature.ofContext_signs _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature.signatureSatisfies_ofContext _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.nBits_eq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.rawSourceList_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceSoundness.leftTable_answer _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_dart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_vertex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceTupleData


open UniqueGamesTheorem.Foundations Target

variable {width : Nat}

def selectedClause (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (position : Fin width) :
    Clause formula.variables := formula.clauses[(indices position).val]

def «stacks» (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (prepared : Fin width → Bool) : Tape width → List Bool
  | .table => SourceOccurrenceEncoding.bits formula
  | .digit position => List.replicate (indices position).val true
  | .work _ => []
  | .variableName position slot =>
      if prepared position then
        NormalizationReadMachine.clauseCounters (selectedClause formula indices position) slot
      else []

@[simp] theorem table_at (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (prepared : Fin width → Bool) :
    «stacks» formula indices prepared .table = SourceOccurrenceEncoding.bits formula := rfl

@[simp] theorem digits_at (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (prepared : Fin width → Bool)
    (position : Fin width) :
    «stacks» formula indices prepared (.digit position) =
      List.replicate (indices position).val true := rfl

@[simp] theorem work_at (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (prepared : Fin width → Bool)
    (slot : Fin 5) : «stacks» formula indices prepared (.work slot) = [] := rfl

@[simp] theorem variables_at (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (prepared : Fin width → Bool)
    (position : Fin width) (slot : Fin 3) :
    «stacks» formula indices prepared (.variableName position slot) =
      if prepared position then
        List.replicate (selectedClause formula indices position)[slot].variableIndex.val true
      else [] := rfl

end PerfectCompleteness.SourceTupleData

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourceTupleMachine
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceTupleMachine


open Turing UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition
open SourceTupleData

abbrev Shape := CanonicalKeyShape.Shape
abbrev Alphabet {width : Nat} (_ : Tape width) := Bool
abbrev State (width : Nat) (A : Type) := SourceCoordinateMachine.State (A × (Fin width → Shape))

structure Data (width : Nat) where
  prepared : Fin width → Bool
  shapes : Fin width → Shape
  signs : Signs

def state {width : Nat} {A : Type} (ambient : A) (data : Data width) : State width A :=
  SourceClauseReaderMachine.clean (ambient, data.shapes) data.signs

def initial {width : Nat} (shapes : Fin width → Shape) (signs : Signs) : Data width :=
  ⟨fun _ => false, shapes, signs⟩

def update {width : Nat} (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (position : Fin width)
    (data : Data width) : Data width where
  prepared := Function.update data.prepared position true
  shapes := Function.update data.shapes position
    (SourceClauseReaderMachine.clauseShape (selectedClause formula indices position))
  signs := NormalizationReadMachine.clauseSigns (selectedClause formula indices position)

def result {width : Nat} (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) : List (Fin width) → Data width → Data width
  | [], data => data
  | position :: positions, data => result formula indices positions (update formula indices position data)

def save {width : Nat} {A : Type} (position : Fin width)
    (ambient : A × (Fin width → Shape)) (shape : Shape) : A × (Fin width → Shape) :=
  (ambient.1, Function.update ambient.2 position shape)

variable {width : Nat} {Λ A : Type}

def localInstruction (rejected : Option Λ) (position : Fin width)
    (labels : SourceCoordinateMachine.Label → Λ) (done : Option Λ) :
    SourceCoordinateMachine.Label → TM2.Stmt (Alphabet (width := width)) Λ (State width A) :=
  SourceCoordinateMachine.instruction (localTape position) labels done rejected (save position)

def instruction (positions : List (Fin width)) (labels : Label positions → Λ)
    (done rejected : Option Λ) :
    Label positions → TM2.Stmt (Alphabet (width := width)) Λ (State width A) :=
  MachineFiniteSequence.instruction LocalLabel localMain
    (localInstruction rejected) positions labels done

end PerfectCompleteness.SourceTupleMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceTuplePlacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceTuplePlacement


open Turing UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition

open MachineCloudPadding

abbrev Tape (width : Nat) := SourceTupleData.Tape width
abbrev State (width : Nat) (A : Type) := SourceTupleMachine.State width A

variable {width : Nat} {K Λ A : Type}

def nativeProgram : Label width →
    TM2.Stmt (Alphabet (K := Tape width)) (Label width) (State width A) :=
  SourceTupleMachine.instruction (List.finRange width) id none none

end PerfectCompleteness.SourceTuplePlacement

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourceTupleResetMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceTupleResetMachine


open Turing
open UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition
open SourceTupleData

theorem clause_count_le_table (formula : Formula) :
    formula.clauses.length ≤ (SourceOccurrenceEncoding.bits formula).length := by
  rw [SourceOccurrenceEncoding.bits_eq]
  simp only [List.length_append, encodeWord_length]
  omega

end PerfectCompleteness.SourceTupleResetMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceTupleResetPlacementLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceTupleBodyPlacement


open Turing UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition MachineCloudPadding

abbrev Shape := CanonicalKeyShape.Shape
abbrev Tape (width : Nat) := SourceTupleData.Tape width
abbrev State (width : Nat) (U D : Type) :=
  ((SourceTupleMachine.State width U × Option D) × (Bool × Option Bool)) × Option Bool

def registers {width : Nat} {U D : Type} :
    (SourceTupleMachine.State width U × Frame D) ≃ State width U D where
  toFun value := (((value.1, value.2.1.1), value.2.1.2), value.2.2)
  invFun value := (value.1.1.1, ((value.1.1.2, value.1.2), value.2))
  left_inv := by rintro ⟨source, ⟨⟨descriptor, comparison⟩, head⟩⟩; rfl
  right_inv := by rintro ⟨⟨⟨source, descriptor⟩, comparison⟩, head⟩; rfl

variable {width : Nat} {K Λ U D : Type}

def instruction (tape : Tape width → K) (labels : Label width → Λ) (exit : Option Λ) :
    Label width → TM2.Stmt (Alphabet (K := K)) Λ (State width U D) :=
  fun label => MachineRegularTable.Lift.statement tape labels exit registers
    (SourceTuplePlacement.nativeProgram label)

end PerfectCompleteness.SourceTupleBodyPlacement

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_DescriptorProjectionMachine
attribute [-instance] _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.SignedScheduleIndex.atIndex_signs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.DescriptorProjectionMachine

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open SignedCompletionSchedule
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t q : Nat} {rows repeats : Nat → Nat}
  (hq : 0 < q)
  (large : CanonicalKeyEncoding.partitionWidth (TreeCanonical.locationCount branch n t) ≤ q)

def projection (descriptor : Descriptor (rows := rows) (repeats := repeats) hq large) :
    ProjectionTable q :=
  LocalCompletionSerialization.projection
    (FiniteConstraintMachine.result_correct hq large ⟨descriptor.1, descriptor.2.1⟩)
    descriptor.2.2

theorem projection_apply
    (descriptor : Descriptor (rows := rows) (repeats := repeats) hq large)
    (a : Fin (2 * q)) :
    (projection hq large descriptor).images[a] = descriptorTable hq large descriptor a :=
  (descriptorTable_eq_parsed hq large descriptor.1 descriptor.2 a).symm

def outputWords (descriptor : Descriptor (rows := rows) (repeats := repeats) hq large) :
    List Nat := Encoding.tableWords (projection hq large descriptor)

@[simp] theorem outputWords_length
    (descriptor : Descriptor (rows := rows) (repeats := repeats) hq large) :
    (outputWords hq large descriptor).length = 2 * q :=
  Encoding.tableWords_length _

def outputBits (descriptor : Descriptor (rows := rows) (repeats := repeats) hq large) :
    List Bool := encodeWords (outputWords hq large descriptor)


variable {σ : Type} [Fintype σ] [DecidableEq σ]
  (select : σ → Descriptor (rows := rows) (repeats := repeats) hq large)

def reverseStatement {K Λ : Type} (dst : K) (exit : Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ σ :=
  MachineFiniteTable.emit dst (fun state => (outputBits hq large (select state)).reverse)
    (keys σ) (.goto (fun _ => exit))

def reverseEmitInTime {K Λ : Type} [DecidableEq K]
    (dst : K) (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (label exit : Λ)
    (atLabel : program label = reverseStatement hq large select dst exit)
    (state : σ) (tapes : K → List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some label, state, tapes⟩
      (some ⟨some exit, state,
        Function.update tapes dst
          ((outputBits hq large (select state)).reverse ++ tapes dst)⟩) 1 :=
  MachineFiniteTable.emitInTime (Γ := fun _ : K => Bool) dst
    (fun state => (outputBits hq large (select state)).reverse)
    (keys σ) keys_complete program label exit
    (by simpa only [reverseStatement] using atLabel) state tapes

end
end PerfectCompleteness.DescriptorProjectionMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_CompletedEdgeMachine
attribute [-instance] _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftKeys_length _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightKeys_length _root_.OAI.PerfectCompleteness.SignedScheduleIndex.atIndex_signs _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_power _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_remainingLevel _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.handoffTapes_level _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.initialTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.finalTapes_prefix _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CompletedEdgeMachine


open Turing UniqueGamesTheorem.Foundations.Complexity
open CanonicalKeys
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t q : Nat} {rows repeats : Nat → Nat}
  (hq : 0 < q)
  (large : CanonicalKeyEncoding.partitionWidth (TreeCanonical.locationCount branch n t) ≤ q)

local notation "width" => TreeCanonical.locationCount branch n t

variable (descriptor : SignedCompletionSchedule.Descriptor
  (rows := rows) (repeats := repeats) hq large)

def key (side : Side) (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat) : Key width :=
  DescriptorKeyTemplate.recover side (DescriptorKeyTemplate.ofDescriptor hq large side descriptor)
    ids vars

def edge (leftPrefix rightPrefix : List (Key width))
    (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat) :
    Edge (leftPrefix.length + 1) (rightPrefix.length + 1) q where
  left := CanonicalOnlineNames.onlineName leftPrefix (key hq large descriptor .left ids vars)
  right := CanonicalOnlineNames.onlineName rightPrefix (key hq large descriptor .right ids vars)
  projection := DescriptorProjectionMachine.projection hq large descriptor

def edgeBits (leftPrefix rightPrefix : List (Key width))
    (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat) : List Bool :=
  encodeWords (Encoding.edgeWords (edge hq large descriptor leftPrefix rightPrefix ids vars))

theorem edgeBits_eq (leftPrefix rightPrefix : List (Key width))
    (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat) :
    edgeBits hq large descriptor leftPrefix rightPrefix ids vars =
      encodeWord (CanonicalOnlineNames.onlineID leftPrefix (key hq large descriptor .left ids vars)) ++
      encodeWord (CanonicalOnlineNames.onlineID rightPrefix (key hq large descriptor .right ids vars)) ++
      DescriptorProjectionMachine.outputBits hq large descriptor := by
  simp only [edgeBits, edge, Encoding.edgeWords, CanonicalOnlineNames.onlineName_val,
    encodeWords_append, encodeWords, List.append_nil, DescriptorProjectionMachine.outputBits,
    DescriptorProjectionMachine.outputWords, List.append_assoc]

variable {K Λ A : Type} [DecidableEq K]

abbrev State (A : Type) := CanonicalEndpointMachine.State A
abbrev clean (ambient : A) : State A := CanonicalEndpointMachine.clean ambient

inductive Label (locations : Nat)
  | left (label : CanonicalEndpointMachine.Label locations)
  | right (label : CanonicalEndpointMachine.Label locations)
  | projection
  deriving DecidableEq, Fintype

def main (locations : Nat) : Label locations := .left (CanonicalEndpointMachine.main locations)

variable [Fintype A] [DecidableEq A]

def instruction (source : Fin width → Fin 6 → K) (work : Fin 10 → K)
    (labels : Label width → Λ) (done : Λ) (rejected : Option Λ) :
    Label width → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .left label =>
      let template := DescriptorKeyTemplate.ofDescriptor hq large .left descriptor
      CanonicalEndpointMachine.instruction template.shapes template.modes .left template.partition
        source (work 9) (leftTapes work) (fun l => labels (.left l))
        (some (labels (.right (CanonicalEndpointMachine.main width)))) rejected label
  | .right label =>
      let template := DescriptorKeyTemplate.ofDescriptor hq large .right descriptor
      CanonicalEndpointMachine.instruction template.shapes template.modes .right template.partition
        source (work 9) (rightTapes work) (fun l => labels (.right l))
        (some (labels .projection)) rejected label
  | .projection =>
      DescriptorProjectionMachine.reverseStatement hq large
        (fun _ : State A => descriptor) (work 7) done

def finalTapes (work : Fin 10 → K) (base : K → List Bool)
    (leftPrefix rightPrefix : List (Key width))
    (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat) : K → List Bool :=
  Function.update
    (Function.update
      (Function.update base (work 1) (BinaryNameSearch.stream (CanonicalVertexNames.tokens
        (leftPrefix ++ [key hq large descriptor .left ids vars]))))
      (work 8) (BinaryNameSearch.stream (CanonicalVertexNames.tokens
        (rightPrefix ++ [key hq large descriptor .right ids vars]))))
    (work 7) ((edgeBits hq large descriptor leftPrefix rightPrefix ids vars).reverse ++ base (work 7))

def budget (source : Fin width → Fin 6 → K) (base : K → List Bool)
    (leftPrefix rightPrefix : List (Key width))
    (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat) : Nat :=
  CanonicalEndpointMachine.budget source base leftPrefix (key hq large descriptor .left ids vars) +
    CanonicalEndpointMachine.budget source base rightPrefix (key hq large descriptor .right ids vars) + 1

def edgeInTime (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat)
    (source : Fin width → Fin 6 → K) (sourceDistinct : ∀ i, Function.Injective (source i))
    (work : Fin 10 → K) (workDistinct : Function.Injective work)
    (sharedScratch : ∀ i, source i 4 = work 5) (sharedOutput : ∀ i, source i 5 = work 9)
    (sourceAvoid : ∀ i field j, KeyMetadataMachine.idTape (source i) field ≠ work j)
    (labels : Label width → Λ) (done : Λ) (rejected : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction hq large descriptor source work labels done rejected l)
    (base : K → List Bool) (ambient : A) (leftPrefix rightPrefix : List (Key width))
    (sourceWords : ∀ i field, base (KeyMetadataMachine.idTape (source i) field) =
      encodeWord (KeyMetadataMachine.fieldValue (ids i) (vars i) field))
    (leftDictionary : base (work 1) = BinaryNameSearch.stream (CanonicalVertexNames.tokens leftPrefix))
    (rightDictionary : base (work 8) = BinaryNameSearch.stream (CanonicalVertexNames.tokens rightPrefix))
    (empty : ∀ j : Fin 10, j ≠ 1 → j ≠ 7 → j ≠ 8 → base (work j) = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (main width)), clean ambient, base⟩
      (some ⟨some done, clean ambient,
        finalTapes hq large descriptor work base leftPrefix rightPrefix ids vars⟩)
      (budget hq large descriptor source base leftPrefix rightPrefix ids vars) := by
  let leftKey := key hq large descriptor .left ids vars
  let rightKey := key hq large descriptor .right ids vars
  let leftTemplate := DescriptorKeyTemplate.ofDescriptor hq large .left descriptor
  let rightTemplate := DescriptorKeyTemplate.ofDescriptor hq large .right descriptor
  let first := CanonicalEndpointMachine.finalTapes (leftTapes work) base leftPrefix leftKey
  let second := CanonicalEndpointMachine.finalTapes (rightTapes work) first rightPrefix rightKey
  have hd (i j : Fin 10) (different : i ≠ j) : work i ≠ work j :=
    fun same => different (workDistinct same)
  have leftEmpty (i : Fin 8) (lo : 2 ≤ i.val) (hi : i.val ≤ 6) :
      base (leftTapes work i) = [] := by
    obtain ⟨h1, h7, h8⟩ := leftMap_work i lo hi
    exact empty (leftMap i) h1 h7 h8
  have leftRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (main width)), clean ambient, base⟩
      (some ⟨some (labels (.right (CanonicalEndpointMachine.main width))), clean ambient, first⟩)
      (CanonicalEndpointMachine.budget source base leftPrefix leftKey) := by
    exact CanonicalEndpointMachine.endpointInTime
      leftTemplate.shapes leftTemplate.modes .left leftTemplate.partition ids vars
      source sourceDistinct (work 9) (leftTapes work)
      (workDistinct.comp leftMap_injective)
      (fun i same => forward_ne_left i (workDistinct same)) sharedScratch sharedOutput
      (fun l => labels (.left l)) (some (labels (.right (CanonicalEndpointMachine.main width))))
      rejected program (fun l => atLabels (.left l)) base ambient leftPrefix sourceWords
      (empty 9 (by decide) (by decide) (by decide))
      (empty 0 (by decide) (by decide) (by decide)) leftDictionary leftEmpty
  have firstAt (i : Fin 10) (h1 : i ≠ 1) (h7 : i ≠ 7) : first (work i) = base (work i) :=
    CanonicalEndpointMachine.finalTapes_frame (leftTapes work) base leftPrefix leftKey
      (work i) (hd i 1 h1) (hd i 7 h7)
  have firstSource (i : Fin width) (field : Fin 4) :
      first (KeyMetadataMachine.idTape (source i) field) =
        base (KeyMetadataMachine.idTape (source i) field) :=
    CanonicalEndpointMachine.finalTapes_sources source (leftTapes work) base leftPrefix leftKey
      (fun i field => sourceAvoid i field 1) (fun i field => sourceAvoid i field 7) i field
  have rightEmpty (i : Fin 8) (lo : 2 ≤ i.val) (hi : i.val ≤ 6) :
      first (rightTapes work i) = [] := by
    obtain ⟨h1, h7, h8⟩ := rightMap_work i lo hi
    exact (firstAt (rightMap i) h1 h7).trans (empty (rightMap i) h1 h7 h8)
  have firstSourceLength : CanonicalKeyMachine.sourceLength source first =
      CanonicalKeyMachine.sourceLength source base := by
    simp only [CanonicalKeyMachine.sourceLength, KeyMetadataMachine.sourceLength, firstSource]
  have rightRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.right (CanonicalEndpointMachine.main width))), clean ambient, first⟩
      (some ⟨some (labels .projection), clean ambient, second⟩)
      (CanonicalEndpointMachine.budget source base rightPrefix rightKey) := by
    have run := CanonicalEndpointMachine.endpointInTime
      rightTemplate.shapes rightTemplate.modes .right rightTemplate.partition ids vars
      source sourceDistinct (work 9) (rightTapes work)
      (workDistinct.comp rightMap_injective)
      (fun i same => forward_ne_right i (workDistinct same)) sharedScratch sharedOutput
      (fun l => labels (.right l)) (some (labels .projection)) rejected program
      (fun l => atLabels (.right l)) first ambient rightPrefix
      (fun i field => (firstSource i field).trans (sourceWords i field))
      ((firstAt 9 (by decide) (by decide)).trans (empty 9 (by decide) (by decide) (by decide)))
      ((firstAt 0 (by decide) (by decide)).trans (empty 0 (by decide) (by decide) (by decide)))
      ((firstAt 8 (by decide) (by decide)).trans rightDictionary) rightEmpty
    change StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.right (CanonicalEndpointMachine.main width))), clean ambient, first⟩
      (some ⟨some (labels .projection), clean ambient, second⟩)
      (CanonicalEndpointMachine.budget source first rightPrefix rightKey) at run
    simpa only [CanonicalEndpointMachine.budget, firstSourceLength] using run
  have projectionRun := DescriptorProjectionMachine.reverseEmitInTime hq large
    (fun _ : State A => descriptor) (work 7) program (labels .projection) done
    (atLabels .projection) (clean ambient) second
  have finalEq : Function.update second (work 7)
      ((DescriptorProjectionMachine.outputBits hq large descriptor).reverse ++ second (work 7)) =
      finalTapes hq large descriptor work base leftPrefix rightPrefix ids vars := by
    funext k
    by_cases hk : k = work 7
    · subst k
      simp [first, second, finalTapes, CanonicalEndpointMachine.finalTapes,
        edgeBits_eq, leftKey, rightKey, leftTapes, rightTapes, leftMap, rightMap,
        List.reverse_append, List.append_assoc]
    · simp [first, second, finalTapes, CanonicalEndpointMachine.finalTapes,
        leftKey, rightKey, leftTapes, rightTapes, leftMap, rightMap,
        Function.update_apply, hk]
  rw [finalEq] at projectionRun
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ leftRun rightRun) projectionRun
  simpa only [budget, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

end
end PerfectCompleteness.CompletedEdgeMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SignedTupleLayout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SignedTupleLayout

open UniqueGamesTheorem.Foundations Complexity Target
open scoped Classical

noncomputable section

inductive Tape (width : Nat) (Extra : Type) where
  | source (tape : SourceTupleData.Tape width)
  | current (position : Fin width)
  | remaining (position : Fin width)
  | encodedVariable (position : Fin width) (slot : Fin 3)
  | adapterScratch
  | edgeWork (slot : Fin 10)
  | edgeCount
  | extra (value : Extra)
  deriving DecidableEq, Fintype

variable {width : Nat} {Extra U Desc : Type}

abbrev State (width : Nat) (U Desc : Type) := SourceTupleBodyPlacement.State width U Desc

def initialSource (ambient : U) : SourceTupleMachine.State width U :=
  SourceTupleMachine.state ambient
    (SourceTupleMachine.initial (fun _ => CanonicalKeyShape.Shape.bit) (fun _ => false))

def clean (ambient : U) : State width U Desc :=
  SourceTupleBodyPlacement.registers (initialSource ambient, frame Desc)

def preparedSource (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (ambient : U) : SourceTupleMachine.State width U :=
  SourceClauseReaderMachine.clean
    (ambient, fun position => SourceClauseReaderMachine.clauseShape
      (SourceTupleData.selectedClause formula indices position))
    (SourceTupleMachine.result formula indices (List.finRange width)
      (SourceTupleMachine.initial (fun _ => CanonicalKeyShape.Shape.bit) (fun _ => false))).signs

def preparedState (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (ambient : U) : State width U Desc :=
  SourceTupleBodyPlacement.registers (preparedSource formula indices ambient, frame Desc)

def sourceView : Tape width Extra → Option (SourceTupleData.Tape width)
  | .source tape => some tape
  | _ => none

@[simp] theorem sourceView_left (tape : SourceTupleData.Tape width) :
    sourceView (Tape.source (Extra := Extra) tape) = some tape := rfl

def metadata (position : Fin width) : Fin 6 → Tape width Extra
  | 0 => .current position
  | 1 => .encodedVariable position 0
  | 2 => .encodedVariable position 1
  | 3 => .encodedVariable position 2
  | 4 => .edgeWork 5
  | 5 => .edgeWork 9

def ids (formula : Formula) (indices : Fin width → Fin formula.clauses.length) : Fin width → Nat :=
  fun position => (indices position).val

def vars (formula : Formula) (indices : Fin width → Fin formula.clauses.length) :
    Fin width → Fin 3 → Nat :=
  fun position slot => (SourceTupleData.selectedClause formula indices position)[slot].variableIndex.val

structure Clear (base : Tape width Extra → List Bool) : Prop where
  rawDigits : ∀ i, base (.source (.digit i)) = []
  rawVariables : ∀ i j, base (.source (.variableName i j)) = []
  sourceWork : ∀ j, base (.source (.work j)) = []
  encodedVariables : ∀ i j, base (.encodedVariable i j) = []
  scratch : base .adapterScratch = []

structure Input (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (base : Tape width Extra → List Bool) : Prop extends Clear base where
  table : base (.source .table) = SourceOccurrenceEncoding.bits formula
  current : ∀ i, base (.current i) = encodeWord (indices i).val

def preparedTapes (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (base : Tape width Extra → List Bool) : Tape width Extra → List Bool
  | .source (.digit i) => List.replicate (indices i).val true
  | .source (.variableName i j) => List.replicate (vars formula indices i j) true
  | .encodedVariable i j => encodeWord (vars formula indices i j)
  | tape => base tape

end
end PerfectCompleteness.SignedTupleLayout

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceVisitOrder
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.DescriptorProjectionMachine.outputWords_length _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SignedScheduleIndex.atIndex_signs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceVisitOrder

open UniqueGamesTheorem.Foundations.Complexity
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t m : Nat}

def visitOrder (branch : Nat → Nat) (n t m : Nat) :
    List (PreliminarySampler.Questions branch n t m) :=
  (SourceQuestionOrder.sourceOrder branch n t m).reverse

theorem visitOrder_eq_tupleOrder (branch : Nat → Nat) (n t m : Nat) :
    visitOrder branch n t m =
      (MachineTupleOdometer.tupleOrder m (TreeCanonical.locationCount branch n t)).map
        SourceQuestionOrder.tupleToQuestion := by
  simp only [visitOrder, SourceQuestionOrder.sourceOrder, ← List.map_reverse,
    List.reverse_reverse]

@[simp] theorem visitOrder_reverse (branch : Nat → Nat) (n t m : Nat) :
    (visitOrder branch n t m).reverse = SourceQuestionOrder.sourceOrder branch n t m := by
  simp only [visitOrder, List.reverse_reverse]

@[simp] theorem visitOrder_length (branch : Nat → Nat) (n t m : Nat) :
    (visitOrder branch n t m).length = m ^ TreeCanonical.locationCount branch n t := by
  simp only [visitOrder, List.length_reverse, SourceQuestionOrder.sourceOrder_length]

theorem mem_visitOrder (question : PreliminarySampler.Questions branch n t m) :
    question ∈ visitOrder branch n t m := by
  simpa only [visitOrder, List.mem_reverse] using SourceQuestionOrder.mem_sourceOrder question

@[simp] theorem visitOrder_toFinset (branch : Nat → Nat) (n t m : Nat) :
    (visitOrder branch n t m).toFinset = Finset.univ := by
  ext question
  simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
  exact mem_visitOrder question

theorem sum_map_visitOrder {A : Type*} [AddCommMonoid A]
    (f : PreliminarySampler.Questions branch n t m → A) :
    ((visitOrder branch n t m).map f).sum = ∑ question, f question := by
  rw [visitOrder, List.map_reverse, List.sum_reverse]
  exact SourceQuestionOrder.sum_map_sourceOrder f

end

end PerfectCompleteness.SourceVisitOrder

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FinitePreliminaryCompletion
attribute [-instance] _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BucketUniform.evaluateLinear_apply _root_.OAI.PerfectCompleteness.BucketUsefulCollision.fill_self _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftKeys_length _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_accepts _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightKeys_length _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.DescriptorProjectionMachine.outputWords_length _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.LowerDirectionFiber.complement_replace _root_.OAI.PerfectCompleteness.LowerDirectionFiber.complement_restore _root_.OAI.PerfectCompleteness.LowerDirectionFiber.pairCoordinates_apply _root_.OAI.PerfectCompleteness.LowerDirectionFiber.pivot_value _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_complement _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_other _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_pivot _root_.OAI.PerfectCompleteness.LowerDirectionFiber.split_apply _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SignedScheduleIndex.atIndex_signs _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.actualProjection_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightEquiv_apply _root_.OAI.PerfectCompleteness.SourceQuestionOrder.questionToTuple_tupleToQuestion _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_length _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset _root_.OAI.PerfectCompleteness.SourceQuestionOrder.tupleToQuestion_questionToTuple _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_length _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_reverse _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FinitePreliminaryCompletion

open MixedSupport CanonicalKeys CanonicalEdges CanonicalLabelEncoding
open UniqueGamesTheorem.Foundations.Games
open CompletionSoundness CompletionSoundness.LegalProjectionGame
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat} {rows repeats : Nat → Nat}

abbrev alphabet (branch : Nat → Nat) (n t : Nat) (δ : ℚ) : Nat :=
  CanonicalLocalCompletion.alphabet (TreeCanonical.locationCount branch n t) δ

def finiteInput (δ : ℚ) (data : MetadataFreeTape.Input branch n t rows repeats) :
    LocalCompletionFamily.Input (alphabet branch n t δ) :=
  CanonicalPartialTable.lookup
    (CanonicalLocalCompletion.alphabet_positive (TreeCanonical.locationCount branch n t) δ)
    (CanonicalLocalCompletion.partitionWidth_le_alphabet
      (TreeCanonical.locationCount branch n t) δ)
    (FixedQueryCodec.partialInput data)

def finiteResult (δ : ℚ) (data : MetadataFreeTape.Input branch n t rows repeats) :
    LocalCompletionFamily.Result (alphabet branch n t δ) :=
  LocalCompletionFamily.lookup
    (CanonicalLocalCompletion.alphabet_positive (TreeCanonical.locationCount branch n t) δ)
    (finiteInput δ data)

abbrev blockFamily (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) :=
  HierarchicalGame.toBlockFamily
    (PreliminarySampler.family clauses branch n t rows repeats)

variable (clauses : Fin m → SourceClause.NormalizedClause v)

local notation "F" => blockFamily clauses branch n t rows repeats

def rawInput (δ : ℚ) (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    LocalCompletionFamily.Input (alphabet branch n t δ) :=
  finiteInput δ (MetadataFreeTape.encodeRaw clauses rows repeats e)

theorem rawInput_mask (δ : ℚ)
    (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    (rawInput clauses δ e).1 = paddedMask (CanonicalGame.leftKey F e) := by
  unfold rawInput finiteInput
  rw [FixedQueryCodec.partialInput_encodeRaw, CanonicalPartialTable.lookup_mask_actual,
    FixedQueryCodec.leftTable_key]
  rfl

theorem rawInput_image_legal (δ : ℚ)
    (e : PreliminarySampler.Raw clauses branch n t rows repeats)
    (P : CanonicalGame.LeftLabel F (CanonicalGame.leftAt F e)) :
    (rawInput clauses δ e).2
        (CanonicalLocalCompletion.legalL F δ (CanonicalGame.leftAt F e) P) =
      CanonicalLocalCompletion.legalR F δ (CanonicalGame.rightAt F e)
        (CanonicalGame.edge F e P) := by
  let slots := MetadataFreeSampler.sourceSlots clauses e.1.1
  let arrays := WholeArraySampler.evaluate rows repeats
    (GeometricPath.leafPath e.1.2) slots e.2.1
  let S := TreeCanonical.numberedSlots slots
  let f := TreeCanonical.numberedFunction slots (HierarchicalArrays.fullJoint arrays)
  let θ := FixedQueryCodec.rawTestIndex clauses e
  let Pencoded : Label S (FixedQueryCodec.leftEncode branch n rows ∘ f) :=
    CanonicalCoarseningEncoding.transportFine S f
      (FixedQueryCodec.leftEncode branch n rows)
      (FixedQueryCodec.leftEncode_injective branch n rows) P
  have hfinite := CanonicalPartialTable.image_actual_legal
    (CanonicalLocalCompletion.alphabet_positive (TreeCanonical.locationCount branch n t) δ)
    (CanonicalLocalCompletion.partitionWidth_le_alphabet
      (TreeCanonical.locationCount branch n t) δ)
    S (FixedQueryCodec.leftTable arrays) (FixedQueryCodec.outputMap θ) Pencoded
  have hcoarse := CanonicalCoarseningEncoding.labelEmbedding_coarsen .right
    (CanonicalLocalCompletion.partitionWidth_le_alphabet
      (TreeCanonical.locationCount branch n t) δ)
    S f (FixedQueryCodec.project θ) (FixedQueryCodec.leftEncode branch n rows)
    (FixedQueryCodec.rightEncode θ) (FixedQueryCodec.outputMap θ)
    (FixedQueryCodec.leftEncode_injective branch n rows)
    (FixedQueryCodec.rightEncode_injective θ) (FixedQueryCodec.outputMap_leftEncode θ) P
  unfold rawInput finiteInput
  rw [FixedQueryCodec.partialInput_encodeRaw]
  exact hfinite.trans hcoarse.symm

local instance leftVertex_fintype : Fintype (CanonicalGame.LeftVertex F) :=
  Fintype.ofFinite _

local instance rightVertex_fintype : Fintype (CanonicalGame.RightVertex F) :=
  Fintype.ofFinite _

local instance leftLabel_fintype (x : CanonicalGame.LeftVertex F) :
    Fintype (CanonicalGame.LeftLabel F x) := Fintype.ofFinite _

local instance rightLabel_fintype (y : CanonicalGame.RightVertex F) :
    Fintype (CanonicalGame.RightLabel F y) := Fintype.ofFinite _

local instance rightAlphabet_nonempty (δ : ℚ) : Nonempty (Fin (alphabet branch n t δ)) :=
  ⟨⟨0, CanonicalLocalCompletion.alphabet_positive (TreeCanonical.locationCount branch n t) δ⟩⟩

local instance leftAlphabet_nonempty (δ : ℚ) : Nonempty (Fin (2 * alphabet branch n t δ)) :=
  ⟨⟨0, Nat.mul_pos (by decide)
    (CanonicalLocalCompletion.alphabet_positive (TreeCanonical.locationCount branch n t) δ)⟩⟩

theorem compatible (μ : FiniteDistribution (PreliminarySampler.Raw clauses branch n t rows repeats))
    (δ : ℚ) :
    FlexibleLocalCompletion.Compatible (CanonicalGame.game F μ)
      (CanonicalLocalCompletion.legalL F δ) (CanonicalLocalCompletion.legalR F δ)
      (rawInput clauses δ) where
  mask e a := by
    rw [rawInput_mask]
    exact paddedMask_eq_true_iff (CanonicalGame.leftKey F e)
      (CanonicalLocalCompletion.partitionWidth_le_leftAlphabet
        (TreeCanonical.locationCount branch n t) δ) a
  image e P := rawInput_image_legal clauses δ e P

def family (μ : FiniteDistribution (PreliminarySampler.Raw clauses branch n t rows repeats))
    (δ : ℚ) :
    (CanonicalGame.game F μ).CompletionFamily
      (CanonicalLocalCompletion.legalL F δ) (CanonicalLocalCompletion.legalR F δ) :=
  FlexibleLocalCompletion.family (CanonicalGame.game F μ)
    (CanonicalLocalCompletion.legalL F δ) (CanonicalLocalCompletion.legalR F δ)
    (rawInput clauses δ) (compatible clauses μ δ)
    (CanonicalLocalCompletion.alphabet_positive (TreeCanonical.locationCount branch n t) δ)
    (by
      intro e b
      rw [Fintype.card_eq_nat_card]
      have h := CanonicalLocalCompletion.small F μ e b
      rw [Fintype.card_eq_nat_card] at h
      exact h)

@[simp] theorem family_size
    (μ : FiniteDistribution (PreliminarySampler.Raw clauses branch n t rows repeats))
    (δ : ℚ) (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    (family clauses μ δ).size e = LocalCompletionFamily.activeCount
      (finiteResult δ (MetadataFreeTape.encodeRaw clauses rows repeats e)) := rfl

@[simp] theorem family_map
    (μ : FiniteDistribution (PreliminarySampler.Raw clauses branch n t rows repeats))
    (δ : ℚ) (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    (family clauses μ δ).map e = LocalCompletionFamily.table
      (finiteResult δ (MetadataFreeTape.encodeRaw clauses rows repeats e)) := rfl

theorem family_value_le
    (μ : FiniteDistribution (PreliminarySampler.Raw clauses branch n t rows repeats))
    (δ : ℚ) (hδ : 0 < δ) :
    (family clauses μ δ).game.value ≤ (CanonicalGame.game F μ).value + (δ : ℝ) / 3 := by
  apply (family clauses μ δ).value_le_of_bound ((δ : ℝ) / 3)
  intro e
  have hδreal : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have h := CompletionParameters.residual_le_third
    (CanonicalLocalCompletion.alphabet_positive (TreeCanonical.locationCount branch n t) δ)
    (CanonicalLocalCompletion.leftLabel_card_le F δ (CanonicalGame.leftAt F e)) hδreal
    (CompletionAlphabet.size_budget
      (CanonicalKeyEncoding.partitionWidth (TreeCanonical.locationCount branch n t)) δ hδ)
  simp only [Fintype.card_fin]
  rw [Fintype.card_eq_nat_card]
  rw [Fintype.card_eq_nat_card] at h
  simpa only [CanonicalGame.game] using h

theorem family_value_of_satisfying
    (μ : FiniteDistribution (PreliminarySampler.Raw clauses branch n t rows repeats))
    (δ : ℚ) (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true) :
    (family clauses μ δ).game.value = 1 := by
  apply (family clauses μ δ).value_eq_one
  exact HierarchicalGame.value_eq_one
    (PreliminarySampler.family clauses branch n t rows repeats) μ assignment hsat

def actualFamily [NeZero m] (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ) :=
  family clauses (PreliminarySampler.law (t := t) clauses rows repeats hn hbranch hrows) δ

def actualValue [NeZero m] (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ) : ℝ :=
  (actualFamily (t := t) clauses rows repeats hn hbranch hrows δ).game.value

theorem actualValue_le [NeZero m] (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
    (δ : ℚ) (hδ : 0 < δ) :
    actualValue (t := t) clauses rows repeats hn hbranch hrows δ ≤
      (PreliminarySampler.game clauses branch n t rows repeats hn hbranch hrows).value +
        (δ : ℝ) / 3 := by
  exact family_value_le clauses
    (PreliminarySampler.law (t := t) clauses rows repeats hn hbranch hrows) δ hδ

theorem actualValue_of_satisfying [NeZero m] (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
    (δ : ℚ) (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true) :
    actualValue (t := t) clauses rows repeats hn hbranch hrows δ = 1 :=
  family_value_of_satisfying clauses
    (PreliminarySampler.law (t := t) clauses rows repeats hn hbranch hrows) δ assignment hsat

end
end PerfectCompleteness.FinitePreliminaryCompletion

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_CompletedSignedLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BucketUniform.evaluateLinear_apply _root_.OAI.PerfectCompleteness.BucketUsefulCollision.fill_self _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftKeys_length _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_accepts _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightKeys_length _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.DescriptorProjectionMachine.outputWords_length _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.LowerDirectionFiber.complement_replace _root_.OAI.PerfectCompleteness.LowerDirectionFiber.complement_restore _root_.OAI.PerfectCompleteness.LowerDirectionFiber.pairCoordinates_apply _root_.OAI.PerfectCompleteness.LowerDirectionFiber.pivot_value _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_complement _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_other _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_pivot _root_.OAI.PerfectCompleteness.LowerDirectionFiber.split_apply _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SignedScheduleIndex.atIndex_signs _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.actualProjection_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightEquiv_apply _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_length _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_reverse _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CompletedSignedLaw

open MetadataFreeSampler MetadataFreeLaw
open UniqueGamesTheorem.Foundations.Games
open CompletionSoundness CompletionSoundness.LegalProjectionGame
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v) (rows repeats : Nat → Nat)

local notation "locationCount" => TreeCanonical.locationCount branch n t
local notation "hq" δ => CanonicalLocalCompletion.alphabet_positive locationCount δ
local notation "large" δ => CanonicalLocalCompletion.partitionWidth_le_alphabet locationCount δ

local notation "F" => FinitePreliminaryCompletion.blockFamily clauses branch n t rows repeats

local instance leftVertex_fintype : Fintype (CanonicalGame.LeftVertex F) := Fintype.ofFinite _

local instance rightVertex_fintype : Fintype (CanonicalGame.RightVertex F) := Fintype.ofFinite _

local instance leftLabel_fintype_re23f58_1 (x : CanonicalGame.LeftVertex F) :
    Fintype (CanonicalGame.LeftLabel F x) := Fintype.ofFinite _
local instance rightLabel_fintype_re23f58_1 (y : CanonicalGame.RightVertex F) :
    Fintype (CanonicalGame.RightLabel F y) := Fintype.ofFinite _
abbrev SignedCompleted (δ : ℚ) :=
  Σ source : PreliminarySampler.Questions branch n t m,
    SignedCompletionSchedule.Completed (rows := rows) (repeats := repeats)
      (hq δ) (large δ) (sourceSigns clauses source)

variable [NeZero m] (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)

abbrev Completed :=
  Σ raw : PreliminarySampler.Raw clauses branch n t rows repeats,
    Fin ((FinitePreliminaryCompletion.actualFamily (t := t)
      clauses rows repeats hn hbranch hrows δ).size raw)

theorem size_eq_active (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    (FinitePreliminaryCompletion.actualFamily (t := t)
      clauses rows repeats hn hbranch hrows δ).size e =
        SignedCompletionSchedule.active (hq δ) (large δ)
      (sourceSigns clauses e.1.1) (encodeOutcome clauses rows repeats e) := rfl

def completedEquiv :
    Completed (t := t) clauses rows repeats hn hbranch hrows δ ≃
      SignedCompleted (branch := branch) (n := n) (t := t) clauses rows repeats δ :=
  (Equiv.sigmaCongrLeft
    (β := fun y : (Σ source : PreliminarySampler.Questions branch n t m,
      SignedOutcome (sourceSigns clauses source) rows repeats) =>
        Fin (SignedCompletionSchedule.active (hq δ) (large δ)
          (sourceSigns clauses y.1) y.2))
    (rawEquiv clauses rows repeats)).trans
    (Equiv.sigmaAssoc (fun source outcome =>
      Fin (SignedCompletionSchedule.active (hq δ) (large δ)
        (sourceSigns clauses source) outcome)))

@[simp] theorem completedEquiv_apply
    (e : PreliminarySampler.Raw clauses branch n t rows repeats)
    (seed : Fin ((FinitePreliminaryCompletion.actualFamily (t := t)
      clauses rows repeats hn hbranch hrows δ).size e)) :
    completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ ⟨e, seed⟩ =
      ⟨e.1.1, encodeOutcome clauses rows repeats e, seed⟩ := rfl

@[simp] theorem completedEquiv_source
    (e : Completed (t := t) clauses rows repeats hn hbranch hrows δ) :
    (completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ e).1 = e.1.1.1 := rfl

theorem completedEquiv_symm_source
    (e : SignedCompleted (branch := branch) (n := n) (t := t) clauses rows repeats δ) :
    ((completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ).symm e).1.1.1 = e.1 := by
  have h := congrArg Sigma.fst
    ((completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ).apply_symm_apply e)
  exact h

theorem descriptorTable_eq_map
    (e : Completed (t := t) clauses rows repeats hn hbranch hrows δ)
    (a : Fin (2 * FinitePreliminaryCompletion.alphabet branch n t δ)) :
    SignedCompletionSchedule.descriptorTable (hq δ) (large δ)
        ⟨sourceSigns clauses (completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ e).1,
          (completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ e).2⟩ a =
      (FinitePreliminaryCompletion.actualFamily (t := t)
        clauses rows repeats hn hbranch hrows δ).map e.1 e.2 a := rfl

def law : FiniteDistribution
    (SignedCompleted (branch := branch) (n := n) (t := t) clauses rows repeats δ) :=
  sigmaLaw PreliminarySampler.questionsLaw (fun source =>
    SignedCompletionSchedule.law (rows := rows) (repeats := repeats)
      (hq δ) (large δ) hn hbranch hrows (sourceSigns clauses source))

theorem completed_weight (e : Completed (t := t) clauses rows repeats hn hbranch hrows δ) :
    (FinitePreliminaryCompletion.actualFamily (t := t)
      clauses rows repeats hn hbranch hrows δ).game.occurrences.weight e =
      (law (t := t) clauses rows repeats hn hbranch hrows δ).weight
        (completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ e) := by
  rcases e with ⟨raw, seed⟩
  change (PreliminarySampler.law (t := t) clauses rows repeats hn hbranch hrows).weight raw *
      (1 / (Fintype.card (Fin ((FinitePreliminaryCompletion.actualFamily (t := t)
        clauses rows repeats hn hbranch hrows δ).size raw)) : ℝ)) =
    (1 / (Fintype.card (PreliminarySampler.Questions branch n t m) : ℝ)) *
      (SignedCompletionSchedule.law (rows := rows) (repeats := repeats)
        (hq δ) (large δ) hn hbranch hrows
        (sourceSigns clauses raw.1.1)).weight
          ⟨encodeOutcome clauses rows repeats raw, seed⟩
  rw [Fintype.card_fin, raw_weight_eq, SignedCompletionSchedule.law_weight]
  rw [size_eq_active (t := t) clauses rows repeats hn hbranch hrows δ raw]
  simp only [div_eq_mul_inv, one_mul, mul_assoc]

theorem actualcompletedLaw_transport :
    (FinitePreliminaryCompletion.actualFamily (t := t)
      clauses rows repeats hn hbranch hrows δ).game.occurrences.transport
        (completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ) =
      sigmaLaw PreliminarySampler.questionsLaw (fun source =>
        SignedCompletionSchedule.law (rows := rows) (repeats := repeats)
          (hq δ) (large δ) hn hbranch hrows
          (sourceSigns clauses source)) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro e
  change (FinitePreliminaryCompletion.actualFamily (t := t)
      clauses rows repeats hn hbranch hrows δ).game.occurrences.weight
      ((completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ).symm e) =
    (law (t := t) clauses rows repeats hn hbranch hrows δ).weight e
  simpa only [Equiv.apply_symm_apply] using
    completed_weight (t := t) clauses rows repeats hn hbranch hrows δ
      ((completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ).symm e)

theorem probability_reindex
    (event : SignedCompleted (branch := branch) (n := n) (t := t) clauses rows repeats δ → Bool) :
    (FinitePreliminaryCompletion.actualFamily (t := t)
      clauses rows repeats hn hbranch hrows δ).game.occurrences.probability
        (fun e => event (completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ e)) =
      (law (t := t) clauses rows repeats hn hbranch hrows δ).probability event := by
  rw [← FiniteDistribution.probability_transport]
  rw [actualcompletedLaw_transport]
  rfl

theorem probability_eq
    (event : Completed (t := t) clauses rows repeats hn hbranch hrows δ → Bool) :
    (FinitePreliminaryCompletion.actualFamily (t := t)
      clauses rows repeats hn hbranch hrows δ).game.occurrences.probability event =
      (law (t := t) clauses rows repeats hn hbranch hrows δ).probability
        (fun e => event ((completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ).symm e)) := by
  simpa only [Equiv.symm_apply_apply] using
    probability_reindex (t := t) clauses rows repeats hn hbranch hrows δ
      (fun e => event ((completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ).symm e))

theorem probability_iterated
    (event : Completed (t := t) clauses rows repeats hn hbranch hrows δ → Bool) :
    (FinitePreliminaryCompletion.actualFamily (t := t)
      clauses rows repeats hn hbranch hrows δ).game.occurrences.probability event =
      PreliminarySampler.questionsLaw.expectation (fun source =>
        (SignedCompletionSchedule.law (rows := rows) (repeats := repeats)
          (hq δ) (large δ) hn hbranch hrows
          (sourceSigns clauses source)).probability (fun outcome =>
            event ((completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ).symm
              ⟨source, outcome⟩))) := by
  rw [probability_eq]
  exact sigmaLaw_probability _ _ _

theorem probability_schedule
    (event : Completed (t := t) clauses rows repeats hn hbranch hrows δ → Bool) :
    (FinitePreliminaryCompletion.actualFamily (t := t)
      clauses rows repeats hn hbranch hrows δ).game.occurrences.probability event =
      PreliminarySampler.questionsLaw.expectation (fun source =>
        (((SignedCompletionSchedule.schedule (rows := rows) (repeats := repeats)
          (hq δ) (large δ) hn hbranch hrows
          (sourceSigns clauses source)).filter (fun outcome =>
            event ((completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ).symm
              ⟨source, outcome⟩))).length : ℝ) /
          (SignedCompletionSchedule.schedule (rows := rows) (repeats := repeats)
            (hq δ) (large δ) hn hbranch hrows
            (sourceSigns clauses source)).length) := by
  rw [probability_iterated]
  congr 1
  funext source
  exact (SignedCompletionSchedule.schedule_acceptance (hq δ) (large δ) hn hbranch hrows
    (sourceSigns clauses source) (fun outcome =>
      event ((completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ).symm
        ⟨source, outcome⟩))).symm

end
end PerfectCompleteness.CompletedSignedLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_CompletedVisitOrder
attribute [-instance] _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CompletedVisitOrder

open MetadataFreeSampler
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v) (rows repeats : Nat → Nat)
  [NeZero m] (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)

local notation "locationCount" => TreeCanonical.locationCount branch n t
local notation "hq" => CanonicalLocalCompletion.alphabet_positive locationCount δ
local notation "large" => CanonicalLocalCompletion.partitionWidth_le_alphabet locationCount δ
local notation "D" => SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows
  (FinitePreliminaryCompletion.alphabet branch n t δ)
local notation "F" => FinitePreliminaryCompletion.blockFamily clauses branch n t rows repeats

local instance leftVertex_fintype : Fintype (CanonicalGame.LeftVertex F) := Fintype.ofFinite _
local instance rightVertex_fintype : Fintype (CanonicalGame.RightVertex F) := Fintype.ofFinite _

local notation "C" =>
  FinitePreliminaryCompletion.actualFamily (t := t) clauses rows repeats hn hbranch hrows δ
local notation "Completed" => CompletedSignedLaw.Completed (t := t) clauses rows repeats hn hbranch hrows δ
local notation "transport" =>
  Equiv.symm (CompletedSignedLaw.completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ)

local instance leftLabel_fintype_re23f58_2 (x : CanonicalGame.LeftVertex F) :
    Fintype (CanonicalGame.LeftLabel F x) := Fintype.ofFinite _
local instance rightLabel_fintype_re23f58_2 (y : CanonicalGame.RightVertex F) :
    Fintype (CanonicalGame.RightLabel F y) := Fintype.ofFinite _
def localOrder (source : PreliminarySampler.Questions branch n t m) : List Completed :=
  (SignedCompletionSchedule.schedule (branch := branch) (n := n) (t := t)
      (rows := rows) (repeats := repeats) hq large hn hbranch hrows
    (sourceSigns clauses source)).map (fun outcome => transport ⟨source, outcome⟩)

def completedOrder : List Completed :=
  (SourceVisitOrder.visitOrder branch n t m).flatMap
    (localOrder (t := t) clauses rows repeats hn hbranch hrows δ)

theorem localOrder_length (source : PreliminarySampler.Questions branch n t m) :
    (localOrder (t := t) clauses rows repeats hn hbranch hrows δ source).length = D := by
  rw [localOrder, List.length_map, SignedCompletionSchedule.schedule_length]

theorem completedOrder_length :
    (completedOrder (t := t) clauses rows repeats hn hbranch hrows δ).length =
      D * m ^ locationCount := by
  change (ExactConditionalOutput.output
    (SignedCompletionSchedule.count (branch := branch) (n := n) (t := t)
      (rows := rows) (repeats := repeats) hq large hn hbranch hrows) (sourceSigns clauses)
    (fun source outcome => transport ⟨source, outcome⟩)
    (SourceVisitOrder.visitOrder branch n t m)).length = _
  rw [ExactConditionalOutput.output_length _ _ _ D
    (SignedCompletionSchedule.count_total (branch := branch) (n := n) (t := t)
      (rows := rows) (repeats := repeats) hq large hn hbranch hrows),
    SourceVisitOrder.visitOrder_length]

theorem completedOrder_nonempty :
    completedOrder (t := t) clauses rows repeats hn hbranch hrows δ ≠ [] := by
  intro hempty
  have h := completedOrder_length (t := t) clauses rows repeats hn hbranch hrows δ
  rw [hempty, List.length_nil] at h
  exact (Nat.ne_of_gt (Nat.mul_pos
    (SignedMultiplicity.denominator_positive branch n t rows repeats hn hbranch hrows _)
    (Nat.pow_pos (NeZero.pos m)))) h.symm

theorem mem_completedOrder (e : Completed) :
    e ∈ completedOrder (t := t) clauses rows repeats hn hbranch hrows δ := by
  let descriptor := CompletedSignedLaw.completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ e
  apply List.mem_flatMap.mpr
  refine ⟨descriptor.1, SourceVisitOrder.mem_visitOrder descriptor.1, ?_⟩
  apply List.mem_map.mpr
  refine ⟨descriptor.2, ?_, ?_⟩
  · exact mem_copies (SignedCompletionSchedule.count (branch := branch) (n := n) (t := t)
      (rows := rows) (repeats := repeats) hq large hn hbranch hrows)
      (sourceSigns clauses descriptor.1) descriptor.2
      (SignedCompletionSchedule.count_positive (branch := branch) (n := n) (t := t)
        (rows := rows) (repeats := repeats) hq large hn hbranch hrows _ _)
  · exact (CompletedSignedLaw.completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ).symm_apply_apply e

def rawOrder : List (PreliminarySampler.Raw clauses branch n t rows repeats) :=
  (completedOrder (t := t) clauses rows repeats hn hbranch hrows δ).map Sigma.fst

theorem mem_rawOrder (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    e ∈ rawOrder (t := t) clauses rows repeats hn hbranch hrows δ := by
  apply List.mem_map.mpr
  refine ⟨⟨e, ⟨0, (C).positive e⟩⟩,
    mem_completedOrder (t := t) clauses rows repeats hn hbranch hrows δ _, rfl⟩

theorem rawOrder_length :
    (rawOrder (t := t) clauses rows repeats hn hbranch hrows δ).length = D * m ^ locationCount := by
  rw [rawOrder, List.length_map,
    completedOrder_length (t := t) clauses rows repeats hn hbranch hrows δ]

theorem completedOrder_filter_length (event : Completed → Bool) :
    ((completedOrder (t := t) clauses rows repeats hn hbranch hrows δ).filter event).length =
      ∑ source : PreliminarySampler.Questions branch n t m,
        ((SignedCompletionSchedule.schedule (branch := branch) (n := n) (t := t)
          (rows := rows) (repeats := repeats) hq large hn hbranch hrows
          (sourceSigns clauses source)).filter
            (fun outcome => event (transport ⟨source, outcome⟩))).length := by
  rw [completedOrder, List.filter_flatMap, List.length_flatMap]
  simp only [localOrder, List.filter_map, List.length_map, Function.comp_def]
  exact SourceVisitOrder.sum_map_visitOrder _

theorem completedOrder_probability (event : Completed → Bool) :
    (((completedOrder (t := t) clauses rows repeats hn hbranch hrows δ).filter event).length : ℝ) /
        (completedOrder (t := t) clauses rows repeats hn hbranch hrows δ).length =
      (C).game.occurrences.probability event := by
  have hcard : Fintype.card (PreliminarySampler.Questions branch n t m) =
      m ^ locationCount := by
    rw [Fintype.card_congr (SourceQuestionOrder.questionTupleEquiv branch n t m)]
    simp only [Fintype.card_fun, Fintype.card_fin]
  rw [completedOrder_filter_length (t := t) clauses rows repeats hn hbranch hrows δ event,
    Nat.cast_sum, completedOrder_length (t := t) clauses rows repeats hn hbranch hrows δ,
    Nat.cast_mul,
    CompletedSignedLaw.probability_schedule (t := t) clauses rows repeats hn hbranch hrows δ event]
  simp only [FiniteDistribution.expectation, PreliminarySampler.questionsLaw,
    FiniteDistribution.uniform, SignedCompletionSchedule.schedule_length]
  rw [← Finset.mul_sum, ← Finset.sum_div, hcard]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end
end PerfectCompleteness.CompletedVisitOrder

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_ExactPreliminaryTarget
attribute [-instance] _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ExactPreliminaryTarget

open UniqueGamesTheorem.Foundations.Games
open CompletionSoundness CompletionSoundness.LegalProjectionGame
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat} [NeZero m]
    (clauses : Fin m → SourceClause.NormalizedClause v) (rows repeats : Nat → Nat)
    (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)

local notation "F" => FinitePreliminaryCompletion.blockFamily clauses branch n t rows repeats
local notation "q" => FinitePreliminaryCompletion.alphabet branch n t δ
local notation "family" => FinitePreliminaryCompletion.actualFamily
  (t := t) clauses rows repeats hn hbranch hrows δ
local notation "order" => CompletedVisitOrder.completedOrder
  (t := t) clauses rows repeats hn hbranch hrows δ
local notation "rawOrder" => CompletedVisitOrder.rawOrder
  (t := t) clauses rows repeats hn hbranch hrows δ
local notation "coverage" => CompletedVisitOrder.mem_rawOrder
  (t := t) clauses rows repeats hn hbranch hrows δ

local instance leftVertex_fintype : Fintype (CanonicalGame.LeftVertex F) := Fintype.ofFinite _
local instance rightVertex_fintype : Fintype (CanonicalGame.RightVertex F) := Fintype.ofFinite _
local instance leftLabel_fintype (x : CanonicalGame.LeftVertex F) :
    Fintype (CanonicalGame.LeftLabel F x) := Fintype.ofFinite _
local instance rightLabel_fintype (y : CanonicalGame.RightVertex F) :
    Fintype (CanonicalGame.RightLabel F y) := Fintype.ofFinite _
local instance rightAlphabet_nonempty : Nonempty (Fin q) :=
  ⟨⟨0, CanonicalLocalCompletion.alphabet_positive (TreeCanonical.locationCount branch n t) δ⟩⟩
local instance leftAlphabet_nonempty : Nonempty (Fin (2 * q)) :=
  ⟨⟨0, Nat.mul_pos (by decide)
    (CanonicalLocalCompletion.alphabet_positive (TreeCanonical.locationCount branch n t) δ)⟩⟩

def namedGame := CanonicalNamedGame.rename F rawOrder coverage (family).game

def entry (e : CompletedSignedLaw.Completed (t := t) clauses rows repeats hn hbranch hrows δ) :
    Edge (rawOrder).length (rawOrder).length q where
  left := (namedGame (t := t) clauses rows repeats hn hbranch hrows δ).left e
  right := (namedGame (t := t) clauses rows repeats hn hbranch hrows δ).right e
  projection := ProjectionTable.ofMap ((family).map e.1 e.2) (by
    intro b
    rw [Fintype.card_eq_nat_card]
    have h := (family).exact_two e.1 e.2 b
    rw [Fintype.card_eq_nat_card] at h
    exact h)

theorem entry_satisfied (e : CompletedSignedLaw.Completed (t := t) clauses rows repeats hn hbranch hrows δ)
    (a : Fin (rawOrder).length → Fin (2 * q)) (b : Fin (rawOrder).length → Fin q) :
    (entry (t := t) clauses rows repeats hn hbranch hrows δ e).satisfied a b =
      (namedGame (t := t) clauses rows repeats hn hbranch hrows δ).wins (a, b) e := by
  simp only [Edge.satisfied, entry, ProjectionTable.ofMap_apply]
  exact decide_eq_decide.mpr Iff.rfl

def construct : Instance q where
  leftVertices := (rawOrder).length
  rightVertices := (rawOrder).length
  edges := (order).map (entry (t := t) clauses rows repeats hn hbranch hrows δ)
  nonempty := by
    intro hempty
    have h := List.map_eq_nil_iff.mp hempty
    exact CompletedVisitOrder.completedOrder_nonempty
      (t := t) clauses rows repeats hn hbranch hrows δ h

theorem edge_count :
    (construct (t := t) clauses rows repeats hn hbranch hrows δ).edges.length =
      SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q *
        m ^ TreeCanonical.locationCount branch n t := by
  change ((order).map (entry (t := t) clauses rows repeats hn hbranch hrows δ)).length = _
  rw [List.length_map]
  exact CompletedVisitOrder.completedOrder_length
    (t := t) clauses rows repeats hn hbranch hrows δ

theorem leftVertices_eq_edges :
    (construct (t := t) clauses rows repeats hn hbranch hrows δ).leftVertices =
      (construct (t := t) clauses rows repeats hn hbranch hrows δ).edges.length := by
  exact (CompletedVisitOrder.rawOrder_length
    (t := t) clauses rows repeats hn hbranch hrows δ).trans
    (edge_count (t := t) clauses rows repeats hn hbranch hrows δ).symm

theorem rightVertices_eq_edges :
    (construct (t := t) clauses rows repeats hn hbranch hrows δ).rightVertices =
      (construct (t := t) clauses rows repeats hn hbranch hrows δ).edges.length :=
  leftVertices_eq_edges (t := t) clauses rows repeats hn hbranch hrows δ

theorem rate_eq (a : Fin (rawOrder).length → Fin (2 * q)) (b : Fin (rawOrder).length → Fin q) :
    (countSatisfied a b (construct (t := t) clauses rows repeats hn hbranch hrows δ).edges : ℝ) /
        (construct (t := t) clauses rows repeats hn hbranch hrows δ).edges.length =
      (namedGame (t := t) clauses rows repeats hn hbranch hrows δ).success (a, b) := by
  change (countSatisfied a b
      ((order).map (entry (t := t) clauses rows repeats hn hbranch hrows δ)) : ℝ) /
    ((order).map (entry (t := t) clauses rows repeats hn hbranch hrows δ)).length = _
  rw [RoundedTarget.countSatisfied_eq_filter]
  simp only [List.filter_map, List.length_map, Function.comp_def]
  have h := CompletedVisitOrder.completedOrder_probability
    (t := t) clauses rows repeats hn hbranch hrows δ
    (fun e => (entry (t := t) clauses rows repeats hn hbranch hrows δ e).satisfied a b)
  simpa only [Function.comp_def, entry_satisfied, OccurrenceGame.success,
    namedGame, CanonicalNamedGame.rename_occurrences] using h

theorem value_eq :
    (construct (t := t) clauses rows repeats hn hbranch hrows δ).value =
      FinitePreliminaryCompletion.actualValue
        (t := t) clauses rows repeats hn hbranch hrows δ := by
  have hq : 0 < q :=
    CanonicalLocalCompletion.alphabet_positive (TreeCanonical.locationCount branch n t) δ
  have hnamed : (construct (t := t) clauses rows repeats hn hbranch hrows δ).value =
      (namedGame (t := t) clauses rows repeats hn hbranch hrows δ).value := by
    apply le_antisymm
    · obtain ⟨s, hs⟩ :=
        (construct (t := t) clauses rows repeats hn hbranch hrows δ).maxSatisfied_attained hq
      unfold Instance.value
      rw [← hs]
      exact (rate_eq (t := t) clauses rows repeats hn hbranch hrows δ s.1 s.2).le.trans
        ((namedGame (t := t) clauses rows repeats hn hbranch hrows δ).success_le_value s)
    · obtain ⟨s, hs⟩ :=
        (namedGame (t := t) clauses rows repeats hn hbranch hrows δ).exists_optimal_strategy
      calc
        (namedGame (t := t) clauses rows repeats hn hbranch hrows δ).value =
            (namedGame (t := t) clauses rows repeats hn hbranch hrows δ).success s := hs.symm
        _ = (countSatisfied s.1 s.2
            (construct (t := t) clauses rows repeats hn hbranch hrows δ).edges : ℝ) /
              (construct (t := t) clauses rows repeats hn hbranch hrows δ).edges.length :=
          (rate_eq (t := t) clauses rows repeats hn hbranch hrows δ s.1 s.2).symm
        _ ≤ (construct (t := t) clauses rows repeats hn hbranch hrows δ).value :=
          (construct (t := t) clauses rows repeats hn hbranch hrows δ).rate_le_value s
  exact hnamed.trans (CanonicalNamedGame.rename_value_eq F rawOrder coverage (family).game)

theorem value_le (hδ : 0 < δ) :
    (construct (t := t) clauses rows repeats hn hbranch hrows δ).value ≤
      (PreliminarySampler.game clauses branch n t rows repeats hn hbranch hrows).value +
        (δ : ℝ) / 3 := by
  rw [value_eq]
  exact FinitePreliminaryCompletion.actualValue_le
    (t := t) clauses rows repeats hn hbranch hrows δ hδ

theorem perfectlyComplete (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true) :
    PerfectlyComplete (construct (t := t) clauses rows repeats hn hbranch hrows δ) := by
  apply ((construct (t := t) clauses rows repeats hn hbranch hrows δ).perfectlyComplete_iff_value_eq_one
    (CanonicalLocalCompletion.alphabet_positive (TreeCanonical.locationCount branch n t) δ)).2
  rw [value_eq]
  exact FinitePreliminaryCompletion.actualValue_of_satisfying
    (t := t) clauses rows repeats hn hbranch hrows δ assignment hsat

theorem encoding_length_le :
    let target := construct (t := t) clauses rows repeats hn hbranch hrows δ
    let N := target.edges.length
    (Encoding.gameBits target).length ≤
      2 * N + q + N + 4 + N * (2 * N + 2 * q * q + 2 * q + 2) := by
  dsimp only
  have h := Encoding.gameBits_length_le_of_edge_count
    (construct (t := t) clauses rows repeats hn hbranch hrows δ)
    (construct (t := t) clauses rows repeats hn hbranch hrows δ).edges.length le_rfl
  have arithmetic (l r N : Nat) (hl : l = N) (hr : r = N) :
      l + r + q + N + 4 + N * (l + r + 2 * q * q + 2 * q + 2) =
        2 * N + q + N + 4 + N * (2 * N + 2 * q * q + 2 * q + 2) := by
    simp only [hl, hr, two_mul]
  exact h.trans_eq (arithmetic _ _ _
    (leftVertices_eq_edges (t := t) clauses rows repeats hn hbranch hrows δ)
    (rightVertices_eq_edges (t := t) clauses rows repeats hn hbranch hrows δ))

end
end PerfectCompleteness.ExactPreliminaryTarget

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_ExactTargetOnlineEncoding
attribute [-instance] _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeBEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
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

variable {branch : Nat → Nat} {n t v m : Nat} [NeZero m]
    (clauses : Fin m → SourceClause.NormalizedClause v) (rows repeats : Nat → Nat)
    (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
    (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)

local notation "F" => FinitePreliminaryCompletion.blockFamily clauses branch n t rows repeats
local notation "C" => CompletedSignedLaw.Completed (t := t) clauses rows repeats hn hbranch hrows δ
local notation "order" => CompletedVisitOrder.completedOrder
  (t := t) clauses rows repeats hn hbranch hrows δ
local notation "edge" => ExactPreliminaryTarget.entry
  (t := t) clauses rows repeats hn hbranch hrows δ

def leftKeys (occurrences : List C) := occurrences.map (fun e => CanonicalGame.leftKey F e.1)

def rightKeys (occurrences : List C) := occurrences.map (fun e => CanonicalGame.rightKey F e.1)

theorem left_online (earlier suffix : List C) (e : C) (split : order = earlier ++ e :: suffix) :
    CanonicalOnlineNames.onlineID (leftKeys (t := t) clauses rows repeats hn hbranch hrows δ earlier)
        (CanonicalGame.leftKey F e.1) = (edge e).left.val := by
  change _ = (BinaryNameSearch.payloads (CanonicalVertexNames.tokens
    (((order).map Sigma.fst).map (CanonicalGame.leftKey F)))).idxOf
      (CanonicalVertexNames.payload (CanonicalGame.leftKey F e.1))
  rw [List.map_map, split, List.map_append, List.map_cons]
  exact CanonicalOnlineNames.onlineID_eq_global _ _ _

theorem right_online (earlier suffix : List C) (e : C) (split : order = earlier ++ e :: suffix) :
    CanonicalOnlineNames.onlineID (rightKeys (t := t) clauses rows repeats hn hbranch hrows δ earlier)
        (CanonicalGame.rightKey F e.1) = (edge e).right.val := by
  change _ = (BinaryNameSearch.payloads (CanonicalVertexNames.tokens
    (((order).map Sigma.fst).map (CanonicalGame.rightKey F)))).idxOf
      (CanonicalVertexNames.payload (CanonicalGame.rightKey F e.1))
  rw [List.map_map, split, List.map_append, List.map_cons]
  exact CanonicalOnlineNames.onlineID_eq_global _ _ _

end
end PerfectCompleteness.ExactTargetOnlineEncoding

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SignedDescriptorStageMachine
attribute [-instance] _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SignedDescriptorStageMachine


open Turing UniqueGamesTheorem.Foundations.Complexity
open CanonicalKeys MetadataFreeSampler
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t q : Nat} {rows repeats : Nat → Nat}
  (hq : 0 < q)
  (large : CanonicalKeyEncoding.partitionWidth (TreeCanonical.locationCount branch n t) ≤ q)

local notation "width" => TreeCanonical.locationCount branch n t

abbrev Descriptor := SignedCompletionSchedule.Descriptor (rows := rows) (repeats := repeats) hq large

abbrev Context (A : Type) := A × Option (Descriptor (rows := rows) (repeats := repeats) hq large)

abbrev State (A : Type) :=
  CompletedEdgeMachine.State (Context (rows := rows) (repeats := repeats) hq large A)

def clean {A : Type} (ambient : A) : State (rows := rows) (repeats := repeats) hq large A :=
  CompletedEdgeMachine.clean (ambient, none)

def loaded {A : Type} (ambient : A)
    (descriptor : Descriptor (rows := rows) (repeats := repeats) hq large) :
    State (rows := rows) (repeats := repeats) hq large A :=
  CompletedEdgeMachine.clean (ambient, some descriptor)

def save {A : Type} (state : State (rows := rows) (repeats := repeats) hq large A)
    (descriptor : Descriptor (rows := rows) (repeats := repeats) hq large) :
    State (rows := rows) (repeats := repeats) hq large A := loaded hq large state.1.1.1 descriptor

inductive Label (α : Type) (locations : Nat)
  | load
  | dispatch
  | edge (descriptor : α) (localLabel : CompletedEdgeMachine.Label locations)
  | finish
  deriving DecidableEq, Fintype

variable (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1))

local notation "D" => SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q
local notation "StageLabel" => Label (Descriptor (rows := rows) (repeats := repeats) hq large) width

variable {K Λ A : Type} [DecidableEq K]

def selected (selectSigns : A → SignTuple branch n t) (i : Fin D)
    (state : State (rows := rows) (repeats := repeats) hq large A) :
    Descriptor (rows := rows) (repeats := repeats) hq large :=
  state.1.1.2.getD
    (SignedScheduleIndex.atIndex (branch := branch) (n := n) (t := t)
      (rows := rows) (repeats := repeats) hq large hn hbranch hrows (selectSigns state.1.1.1) i)

def finish (count : K) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State (rows := rows) (repeats := repeats) hq large A) :=
  .push count (fun _ => true)
    (.load (fun state => clean hq large state.1.1.1)
      (match exit with | none => .halt | some label => .goto (fun _ => label)))

theorem finish_trace (count : K) (exit : Option Λ)
    (state : State (rows := rows) (repeats := repeats) hq large A)
    (base : K → List Bool) :
    TM2.stepAux (finish hq large count exit) state base =
      ⟨exit, clean hq large state.1.1.1, Function.update base count (true :: base count)⟩ := by
  cases exit <;> rfl

variable [Fintype A] [DecidableEq A]

def instruction (selectSigns : A → SignTuple branch n t) (i : Fin D)
    (source : Fin width → Fin 6 → K) (work : Fin 10 → K) (count : K)
    (labels : StageLabel → Λ) (exit rejected : Option Λ) :
    StageLabel → TM2.Stmt (Alphabet (K := K)) Λ (State (rows := rows) (repeats := repeats) hq large A)
  | .load => SignedScheduleIndex.instruction hq large hn hbranch hrows
      (fun state : State (rows := rows) (repeats := repeats) hq large A => selectSigns state.1.1.1)
      (save hq large) i (labels .dispatch)
  | .dispatch => .goto (fun state =>
      labels (.edge (selected hq large hn hbranch hrows selectSigns i state)
        (CompletedEdgeMachine.main width)))
  | .edge descriptor localLabel => CompletedEdgeMachine.instruction hq large descriptor
      source work (fun l => labels (.edge descriptor l)) (labels .finish) rejected localLabel
  | .finish => finish hq large count exit

def finalTapes (descriptor : Descriptor (rows := rows) (repeats := repeats) hq large)
    (work : Fin 10 → K) (count : K)
    (base : K → List Bool) (leftPrefix rightPrefix : List (Key width))
    (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat) : K → List Bool :=
  let edgeTapes : K → List Bool := CompletedEdgeMachine.finalTapes hq large descriptor work base
    leftPrefix rightPrefix ids vars
  Function.update edgeTapes count (true :: edgeTapes count)

end
end PerfectCompleteness.SignedDescriptorStageMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SignedTupleCleanupMachineLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_variable_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_variables _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_current _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_remaining _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.nBits_eq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.rawSourceList_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceSoundness.leftTable_answer _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SignedTupleCleanupMachine


open Turing UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition
open scoped Classical

noncomputable section

abbrev Tape (width : Nat) (Extra : Type) := SignedTupleLayout.Tape width Extra
abbrev State (width : Nat) (U Desc : Type) := SignedTupleLayout.State width U Desc
abbrev Alphabet {width : Nat} {Extra : Type} (_ : Tape width Extra) := Bool

variable {width : Nat} {Extra U Desc Λ : Type}

def localTapes (position : Fin width) : List (Tape width Extra) :=
  [.source (.digit position),
   .source (.variableName position 0), .source (.variableName position 1),
   .source (.variableName position 2),
   .encodedVariable position 0, .encodedVariable position 1, .encodedVariable position 2]

def chosen (width : Nat) (Extra : Type) : List (Tape width Extra) :=
  (List.finRange width).flatMap localTapes

def selected : Tape width Extra → Bool
  | .source (.digit _) => true
  | .source (.variableName _ _) => true
  | .encodedVariable _ _ => true
  | _ => false

@[simp] theorem chosen_length (width : Nat) (Extra : Type) :
    (chosen width Extra).length = 7 * width := by
  have lengthFor (positions : List (Fin width)) :
      (positions.flatMap (localTapes (Extra := Extra))).length = 7 * positions.length := by
    induction positions with
    | nil => rfl
    | cons position positions ih =>
        simp only [List.flatMap_cons, List.length_append, localTapes, List.length_cons,
          List.length_nil, ih]
        omega
  simpa only [chosen, List.length_finRange] using lengthFor (List.finRange width)

@[simp] theorem mem_chosen (tape : Tape width Extra) :
    tape ∈ chosen width Extra ↔ selected tape = true := by
  cases tape with
  | source source =>
      cases source with
      | table => simp [chosen, localTapes, selected]
      | digit position => simp [chosen, localTapes, selected]
      | work slot => simp [chosen, localTapes, selected]
      | variableName position slot =>
          fin_cases slot <;> simp [chosen, localTapes, selected]
  | encodedVariable position slot =>
      fin_cases slot <;> simp [chosen, localTapes, selected]
  | current position => simp [chosen, localTapes, selected]
  | remaining position => simp [chosen, localTapes, selected]
  | adapterScratch => simp [chosen, localTapes, selected]
  | edgeWork slot => simp [chosen, localTapes, selected]
  | edgeCount => simp [chosen, localTapes, selected]
  | extra value => simp [chosen, localTapes, selected]

theorem finalTapes_eq (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (base : Tape width Extra → List Bool)
    (clear : SignedTupleLayout.Clear base) :
    MachineDrainMany.finalTapes (chosen width Extra)
      (SignedTupleLayout.preparedTapes formula indices base) = base := by
  funext tape
  simp only [MachineDrainMany.finalTapes_apply, mem_chosen]
  cases tape with
  | source source =>
      cases source with
      | table => simp [selected, SignedTupleLayout.preparedTapes]
      | digit position => simp [selected, clear.rawDigits]
      | work slot => simp [selected, SignedTupleLayout.preparedTapes]
      | variableName position slot => simp [selected, clear.rawVariables]
  | encodedVariable position slot => simp [selected, clear.encodedVariables]
  | current position => simp [selected, SignedTupleLayout.preparedTapes]
  | remaining position => simp [selected, SignedTupleLayout.preparedTapes]
  | adapterScratch => simp [selected, SignedTupleLayout.preparedTapes]
  | edgeWork slot => simp [selected, SignedTupleLayout.preparedTapes]
  | edgeCount => simp [selected, SignedTupleLayout.preparedTapes]
  | extra value => simp [selected, SignedTupleLayout.preparedTapes]

def steps (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (base : Tape width Extra → List Bool) : Nat :=
  MachineDrainMany.steps (chosen width Extra) (SignedTupleLayout.preparedTapes formula indices base)

abbrev Label (width : Nat) (Extra : Type) := MachineDrainMany.Label (chosen width Extra)

def instruction (labels : Label width Extra → Λ) (exit : Option Λ) :
    Label width Extra → TM2.Stmt (Alphabet (width := width) (Extra := Extra)) Λ
      (State width U Desc) :=
  MachineDrainMany.instruction (chosen width Extra) labels exit

def entry (labels : Label width Extra → Λ) (exit : Option Λ) : Option Λ :=
  MachineDrainMany.entry (chosen width Extra) labels exit

end
end PerfectCompleteness.SignedTupleCleanupMachine


namespace PerfectCompleteness.SignedTuplePreparationMachine


open Turing UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition MachineCloudPadding
open SignedTupleLayout
open scoped Classical

noncomputable section

abbrev Tape (width : Nat) (Extra : Type) := SignedTupleLayout.Tape width Extra
abbrev State (width : Nat) (U Desc : Type) := SignedTupleLayout.State width U Desc
abbrev Alphabet {width : Nat} {Extra : Type} (_ : Tape width Extra) := Bool

variable {width : Nat} {Extra U Desc Λ : Type}

def digitTape : FixedUnaryRepresentationPlacement.Tape width → Tape width Extra
  | .source i => .current i
  | .destination i => .source (.digit i)
  | .scratch => .adapterScratch

def variableTape : FixedUnaryRepresentationPlacement.Tape (width * 3) → Tape width Extra
  | .source i => .source (.variableName ((variableEquiv width) i).1 ((variableEquiv width) i).2)
  | .destination i => .encodedVariable ((variableEquiv width) i).1 ((variableEquiv width) i).2
  | .scratch => .adapterScratch

def instruction (labels : Label width → Λ) (exit : Option Λ) :
    Label width → TM2.Stmt (Alphabet (width := width) (Extra := Extra)) Λ (State width U Desc)
  | .digits label => FixedUnaryRepresentationPlacement.instruction .encodedToRaw digitTape
      (fun l => labels (.digits l)) (sourceEntry labels exit) label
  | .extract label => SourceTupleBodyPlacement.instruction SignedTupleLayout.Tape.source
      (fun l => labels (.extract l)) (variableEntry labels exit) label
  | .variableCopies label => FixedUnaryRepresentationPlacement.instruction .rawToEncoded variableTape
      (fun l => labels (.variableCopies l)) exit label

end
end PerfectCompleteness.SignedTuplePreparationMachine


namespace PerfectCompleteness.SourceTupleScheduleMachine


open Turing UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition MetadataFreeSampler
open scoped Classical

noncomputable section

def shapeSigns : CanonicalKeyShape.Shape → SourceClause.Triple
  | .clause signs => signs
  | .bit => (false, false, false)

def signTuple {branch : Nat → Nat} {n t : Nat}
    (shapes : Fin (TreeCanonical.locationCount branch n t) → CanonicalKeyShape.Shape) :
    SignTuple branch n t :=
  fun leaf slot => shapeSigns (shapes (TreeCanonical.numbering branch n t (leaf, slot)))

def sourceSigns {branch : Nat → Nat} {n t : Nat} (formula : Formula)
    (indices : Fin (TreeCanonical.locationCount branch n t) → Fin formula.clauses.length) :
    SignTuple branch n t :=
  fun leaf slot =>
    let clause := SourceTupleData.selectedClause formula indices
      (TreeCanonical.numbering branch n t (leaf, slot))
    (clause[0].positive, clause[1].positive, clause[2].positive)

end
end PerfectCompleteness.SourceTupleScheduleMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SignedTupleBodyMachine
attribute [-instance] _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_variable_count _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftKeys_length _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightKeys_length _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_variables _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_power _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_remainingLevel _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.handoffTapes_level _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.initialTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.finalTapes_prefix _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_current _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_remaining _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.nBits_eq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.rawSourceList_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceSoundness.leftTable_answer _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SignedTupleBodyMachine


open Turing UniqueGamesTheorem.Foundations.Complexity
open MachineComposition CanonicalKeys MetadataFreeSampler
open scoped Classical

noncomputable section

abbrev Tape (width : Nat) (Extra : Type) := SignedTupleLayout.Tape width Extra

inductive BodyLabel (locations steps : Nat) (Descriptor Extra : Type) where
  | start
  | prepare (label : SignedTuplePreparationMachine.Label locations)
  | edges (label : MachineFiniteSequence.Label
      (fun _ : Fin steps => SignedDescriptorStageMachine.Label Descriptor locations) (List.ofFn id))
  | cleanup (label : SignedTupleCleanupMachine.Label locations Extra)
  | reset
  deriving DecidableEq, Fintype

structure Data (width : Nat) where
  leftKeys : List (Key width)
  rightKeys : List (Key width)
  reversedOutput : List Bool
  count : Nat

variable {branch : Nat → Nat} {n t q : Nat} {rows repeats : Nat → Nat}
  (hq : 0 < q)
  (large : CanonicalKeyEncoding.partitionWidth (TreeCanonical.locationCount branch n t) ≤ q)
  (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1))

local notation "width" => TreeCanonical.locationCount branch n t
local notation "D" => SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q
local notation "Desc" => SignedDescriptorStageMachine.Descriptor
  (rows := rows) (repeats := repeats) hq large

variable {K Λ A : Type} [DecidableEq K]

def tapes (work : Fin 10 → K) (countTape : K) (base : K → List Bool)
    (data : Data width) : K → List Bool :=
  Function.update
    (Function.update
      (Function.update
        (Function.update base (work 1)
          (BinaryNameSearch.stream (CanonicalVertexNames.tokens data.leftKeys)))
        (work 8) (BinaryNameSearch.stream (CanonicalVertexNames.tokens data.rightKeys)))
      (work 7) data.reversedOutput)
    countTape (encodeWord data.count)

def next (descriptor : Desc) (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat)
    (data : Data width) : Data width where
  leftKeys := data.leftKeys ++ [CompletedEdgeMachine.key hq large descriptor .left ids vars]
  rightKeys := data.rightKeys ++ [CompletedEdgeMachine.key hq large descriptor .right ids vars]
  reversedOutput :=
    (CompletedEdgeMachine.edgeBits hq large descriptor data.leftKeys data.rightKeys ids vars).reverse ++
      data.reversedOutput
  count := data.count + 1

theorem finalTapes_eq (descriptor : Desc) (ids : Fin width → Nat)
    (vars : Fin width → Fin 3 → Nat) (work : Fin 10 → K)
    (distinct : Function.Injective work) (countTape : K)
    (countAvoid : ∀ j, countTape ≠ work j) (base : K → List Bool) (data : Data width) :
    SignedDescriptorStageMachine.finalTapes hq large descriptor work countTape
        (tapes work countTape base data) data.leftKeys data.rightKeys ids vars =
      tapes work countTape base (next hq large descriptor ids vars data) := by
  have hd (i j : Fin 10) (hne : i ≠ j) : work i ≠ work j :=
    fun h => hne (distinct h)
  funext k
  by_cases hc : k = countTape
  · subst k
    simp [SignedDescriptorStageMachine.finalTapes, CompletedEdgeMachine.finalTapes,
      tapes, next, countAvoid, encodeWord, List.replicate_succ]
  · by_cases hl : k = work 1
    · subst k
      simp [SignedDescriptorStageMachine.finalTapes, CompletedEdgeMachine.finalTapes,
        tapes, next, hc, hd 1 8 (by decide), hd 1 7 (by decide)]
    · by_cases hr : k = work 8
      · subst k
        simp [SignedDescriptorStageMachine.finalTapes, CompletedEdgeMachine.finalTapes,
          tapes, next, hc, hd 8 7 (by decide)]
      · by_cases ho : k = work 7
        · subst k
          simp [SignedDescriptorStageMachine.finalTapes, CompletedEdgeMachine.finalTapes,
            tapes, next, hc]
        · simp only [SignedDescriptorStageMachine.finalTapes, CompletedEdgeMachine.finalTapes,
            tapes, Function.update_of_ne hc, Function.update_of_ne hl,
            Function.update_of_ne hr, Function.update_of_ne ho]

theorem tapes_frame (work : Fin 10 → K) (countTape : K) (base : K → List Bool)
    (data : Data width) (k : K) (hc : k ≠ countTape)
    (hl : k ≠ work 1) (hr : k ≠ work 8) (ho : k ≠ work 7) :
    tapes work countTape base data k = base k := by
  simp only [tapes, Function.update_of_ne hc, Function.update_of_ne hl,
    Function.update_of_ne hr, Function.update_of_ne ho]

variable [Fintype A] [DecidableEq A]

abbrev StageLabel := SignedDescriptorStageMachine.Label Desc width
abbrev LocalLabel (_ : Fin D) := StageLabel (rows := rows) (repeats := repeats) hq large
abbrev Label (indices : List (Fin D)) :=
  MachineFiniteSequence.Label (LocalLabel (repeats := repeats) hq large hn hbranch hrows) indices
abbrev State := SignedDescriptorStageMachine.State (rows := rows) (repeats := repeats) hq large A

abbrev BodyState (U : Type) :=
  SignedDescriptorStageMachine.State (rows := rows) (repeats := repeats) hq large
    (SourceTupleMachine.State width U)

def localMain (_ : Fin D) : StageLabel (rows := rows) (repeats := repeats) hq large := .load

def localInstruction (selectSigns : A → SignTuple branch n t)
    (source : Fin width → Fin 6 → K) (work : Fin 10 → K) (countTape : K)
    (rejected : Option Λ) (i : Fin D)
    (labels : StageLabel (rows := rows) (repeats := repeats) hq large → Λ) (exit : Option Λ) :
    StageLabel (rows := rows) (repeats := repeats) hq large →
      TM2.Stmt (fun _ : K => Bool) Λ (State (rows := rows) (repeats := repeats) (A := A) hq large) :=
  SignedDescriptorStageMachine.instruction (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows selectSigns i
    source work countTape labels exit rejected

def instruction (selectSigns : A → SignTuple branch n t)
    (source : Fin width → Fin 6 → K) (work : Fin 10 → K) (countTape : K)
    (indices : List (Fin D))
    (labels : Label (repeats := repeats) hq large hn hbranch hrows indices → Λ)
    (exit rejected : Option Λ) :
    Label (repeats := repeats) hq large hn hbranch hrows indices →
      TM2.Stmt (fun _ : K => Bool) Λ (State (rows := rows) (repeats := repeats) (A := A) hq large) :=
  MachineFiniteSequence.instruction _ (localMain (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows)
    (localInstruction (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows selectSigns source work countTape rejected)
    indices labels exit

def entry (indices : List (Fin D))
    (labels : Label (repeats := repeats) hq large hn hbranch hrows indices → Λ)
    (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry _ (localMain (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows) indices labels exit

def result (signs : SignTuple branch n t) (ids : Fin width → Nat)
    (vars : Fin width → Fin 3 → Nat) : List (Fin D) → Data width → Data width
  | [], data => data
  | i :: indices, data => result signs ids vars indices
      (next hq large (SignedScheduleIndex.atIndex (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs i) ids vars data)

def budget (signs : SignTuple branch n t) (ids : Fin width → Nat)
    (vars : Fin width → Fin 3 → Nat) (source : Fin width → Fin 6 → K)
    (work : Fin 10 → K) (countTape : K) (base : K → List Bool) :
    List (Fin D) → Data width → Nat
  | [], _ => 0
  | i :: indices, data =>
      let descriptor := SignedScheduleIndex.atIndex (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs i
      CompletedEdgeMachine.budget hq large descriptor source (tapes work countTape base data)
        data.leftKeys data.rightKeys ids vars + 3 +
      budget signs ids vars source work countTape base indices (next hq large descriptor ids vars data)

def allStages : List (Fin D) := List.ofFn id

def tupleResult (formula : UniqueGamesTheorem.Foundations.Target.Formula)
    (indices : Fin width → Fin formula.clauses.length) (data : Data width) : Data width :=
  result (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows (SourceTupleScheduleMachine.sourceSigns formula indices)
    (SignedTupleLayout.ids formula indices) (SignedTupleLayout.vars formula indices)
    (allStages (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hn hbranch hrows) data

section WholeBody

variable {Extra U : Type} [DecidableEq Extra] [Fintype U] [DecidableEq U]

local notation "Arena" => Tape width Extra
local notation "Control" => BodyState (rows := rows) (repeats := repeats) hq large U
local notation "WholeLabel" => BodyLabel width D Desc Extra

def bodyMain : WholeLabel := .start

def bodySigns (control : SourceTupleMachine.State width U) : SignTuple branch n t :=
  SourceTupleScheduleMachine.signTuple control.1.1.2

omit [Fintype U] [DecidableEq U] in
@[simp] theorem bodySigns_prepared
    (formula : UniqueGamesTheorem.Foundations.Target.Formula)
    (indices : Fin width → Fin formula.clauses.length) (ambient : U) :
    bodySigns (SignedTupleLayout.preparedSource formula indices ambient) =
      SourceTupleScheduleMachine.sourceSigns formula indices := rfl

def bodyExit (exit : Option Λ) : TM2.Stmt (fun _ : Arena => Bool) Λ Control :=
  match exit with
  | none => .halt
  | some label => .goto (fun _ => label)

def cleanupEntry (labels : WholeLabel → Λ) : Option Λ :=
  SignedTupleCleanupMachine.entry (fun l => labels (.cleanup l)) (some (labels .reset))

def edgesEntry (labels : WholeLabel → Λ) : Option Λ :=
  entry (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows (allStages (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hn hbranch hrows)
    (fun l => labels (.edges l)) (cleanupEntry (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows labels)

def bodyInstruction (labels : WholeLabel → Λ) (exit : Option Λ) :
    WholeLabel → TM2.Stmt (fun _ : Arena => Bool) Λ Control
  | .start => bodyExit hq large
      (SignedTuplePreparationMachine.entry (fun l => labels (.prepare l))
        (edgesEntry (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows labels))
  | .prepare label => SignedTuplePreparationMachine.instruction
      (fun l => labels (.prepare l)) (edgesEntry (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows labels) label
  | .edges label => instruction (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows bodySigns
      SignedTupleLayout.metadata SignedTupleLayout.Tape.edgeWork SignedTupleLayout.Tape.edgeCount (allStages (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hn hbranch hrows)
      (fun l => labels (.edges l)) (cleanupEntry (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows labels) none label
  | .cleanup label => SignedTupleCleanupMachine.instruction
      (fun l => labels (.cleanup l)) (some (labels .reset)) label
  | .reset => .load (fun control => SignedTupleLayout.clean control.1.1.1.1.1.1)
      (bodyExit hq large exit)

theorem tapes_input (formula : UniqueGamesTheorem.Foundations.Target.Formula)
    (indices : Fin width → Fin formula.clauses.length) (base : Arena → List Bool)
    (input : SignedTupleLayout.Input formula indices base) (data : Data width) :
    SignedTupleLayout.Input formula indices (tapes SignedTupleLayout.Tape.edgeWork SignedTupleLayout.Tape.edgeCount base data) := by
  refine {
    toClear := {
      rawDigits := ?_
      rawVariables := ?_
      sourceWork := ?_
      encodedVariables := ?_
      scratch := ?_
    }
    table := ?_
    current := ?_
  }
  · intro i
    simpa [tapes] using input.rawDigits i
  · intro i j
    simpa [tapes] using input.rawVariables i j
  · intro j
    simpa [tapes] using input.sourceWork j
  · intro i j
    simpa [tapes] using input.encodedVariables i j
  · simpa [tapes] using input.scratch
  · simpa [tapes] using input.table
  · intro i
    simpa [tapes] using input.current i

theorem prepared_tapes_commute (formula : UniqueGamesTheorem.Foundations.Target.Formula)
    (indices : Fin width → Fin formula.clauses.length) (base : Arena → List Bool)
    (data : Data width) :
    SignedTupleLayout.preparedTapes formula indices (tapes SignedTupleLayout.Tape.edgeWork SignedTupleLayout.Tape.edgeCount base data) =
      tapes SignedTupleLayout.Tape.edgeWork SignedTupleLayout.Tape.edgeCount (SignedTupleLayout.preparedTapes formula indices base) data := by
  funext tape
  cases tape with
  | source source => cases source <;> simp [SignedTupleLayout.preparedTapes, tapes]
  | current i => simp [SignedTupleLayout.preparedTapes, tapes]
  | remaining i => simp [SignedTupleLayout.preparedTapes, tapes]
  | encodedVariable i j => simp [SignedTupleLayout.preparedTapes, tapes]
  | adapterScratch => simp [SignedTupleLayout.preparedTapes, tapes]
  | edgeWork j => simp [SignedTupleLayout.preparedTapes, tapes, Function.update_apply]
  | edgeCount => simp [SignedTupleLayout.preparedTapes, tapes]
  | extra value => simp [SignedTupleLayout.preparedTapes, tapes]

def bodyBudget (formula : UniqueGamesTheorem.Foundations.Target.Formula)
    (indices : Fin width → Fin formula.clauses.length) (base : Arena → List Bool)
    (data : Data width) : Nat :=
  1 + SignedTuplePreparationMachine.budget width (SourceOccurrenceEncoding.bits formula).length +
    budget (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows (SourceTupleScheduleMachine.sourceSigns formula indices)
      (SignedTupleLayout.ids formula indices) (SignedTupleLayout.vars formula indices)
      SignedTupleLayout.metadata SignedTupleLayout.Tape.edgeWork SignedTupleLayout.Tape.edgeCount
      (SignedTupleLayout.preparedTapes formula indices base) (allStages (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hn hbranch hrows) data +
    7 * width * ((SourceOccurrenceEncoding.bits formula).length + 2) + 1

end WholeBody

end
end PerfectCompleteness.SignedTupleBodyMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SignedTupleSemantics
attribute [-instance] _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.actualProjection_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SignedTupleSemantics


open MetadataFreeSampler
open UniqueGamesTheorem.Foundations.Complexity
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat} [NeZero m]
  (clauses : Fin m → SourceClause.NormalizedClause v) (rows repeats : Nat → Nat)
  (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)

local notation "width" => TreeCanonical.locationCount branch n t
local notation "q" => FinitePreliminaryCompletion.alphabet branch n t δ
local notation "hq" => CanonicalLocalCompletion.alphabet_positive width δ
local notation "large" => CanonicalLocalCompletion.partitionWidth_le_alphabet width δ
local notation "D" => SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q
local notation "C" => CompletedSignedLaw.Completed (t := t) clauses rows repeats hn hbranch hrows δ
local notation "F" => FinitePreliminaryCompletion.blockFamily clauses branch n t rows repeats
local notation "equiv" => CompletedSignedLaw.completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ
local notation "order" => CompletedVisitOrder.completedOrder
  (t := t) clauses rows repeats hn hbranch hrows δ
local notation "localOrder" => CompletedVisitOrder.localOrder
  (t := t) clauses rows repeats hn hbranch hrows δ
local notation "targetEntry" => ExactPreliminaryTarget.entry
  (t := t) clauses rows repeats hn hbranch hrows δ

def sourceIDs (source : PreliminarySampler.Questions branch n t m) : Fin width → Nat :=
  fun i => (SourceQuestionOrder.questionToTuple source i).val

def sourceVariables (source : PreliminarySampler.Questions branch n t m) :
    Fin width → Fin 3 → Nat :=
  fun i j => ((clauses (SourceQuestionOrder.questionToTuple source i)).variable j).val

omit [NeZero m] in
@[simp] theorem sourceIDs_tuple (indices : Fin width → Fin m) :
    sourceIDs (SourceQuestionOrder.tupleToQuestion (branch := branch) (n := n) (t := t) indices) =
      fun i => (indices i).val := by
  exact congrArg (fun tuple : Fin width → Fin m => fun i => (tuple i).val)
    (SourceQuestionOrder.questionToTuple_tupleToQuestion
      (branch := branch) (n := n) (t := t) indices)

omit [NeZero m] in
@[simp] theorem sourceVariables_tuple (indices : Fin width → Fin m) :
    sourceVariables clauses
        (SourceQuestionOrder.tupleToQuestion (branch := branch) (n := n) (t := t) indices) =
      fun i j => ((clauses (indices i)).variable j).val := by
  exact congrArg
    (fun tuple : Fin width → Fin m => fun i j => ((clauses (tuple i)).variable j).val)
    (SourceQuestionOrder.questionToTuple_tupleToQuestion
      (branch := branch) (n := n) (t := t) indices)

def descriptorOf (e : C) : SignedCompletionSchedule.Descriptor
    (rows := rows) (repeats := repeats) hq large :=
  ⟨sourceSigns clauses (equiv e).1, (equiv e).2⟩

theorem left_key (e : C) :
    CompletedEdgeMachine.key hq large (descriptorOf clauses rows repeats hn hbranch hrows δ e)
        .left (sourceIDs e.1.1.1) (sourceVariables clauses e.1.1.1) =
      CanonicalGame.leftKey F e.1 := by
  rcases e with ⟨raw, seed⟩
  exact (DescriptorKeyTemplate.recover_left clauses raw).trans
    (HierarchicalGame.leftKey_eq
      (PreliminarySampler.family clauses branch n t rows repeats) raw).symm

theorem right_key (e : C) :
    CompletedEdgeMachine.key hq large (descriptorOf clauses rows repeats hn hbranch hrows δ e)
        .right (sourceIDs e.1.1.1) (sourceVariables clauses e.1.1.1) =
      CanonicalGame.rightKey F e.1 := by
  rcases e with ⟨raw, seed⟩
  exact (DescriptorKeyTemplate.recover_right clauses raw).trans
    (HierarchicalGame.rightKey_eq
      (PreliminarySampler.family clauses branch n t rows repeats) raw).symm

theorem projection_eq (e : C) :
    DescriptorProjectionMachine.projection hq large
        (descriptorOf clauses rows repeats hn hbranch hrows δ e) =
      (targetEntry e).projection  := by
  apply projection_ext (n := n) (alphabet := q)
  intro a
  have hp := DescriptorProjectionMachine.projection_apply
    (branch := branch) (n := n) (t := t) («q» := q) (rows := rows) (repeats := repeats)
    hq large (descriptorOf (branch := branch) (n := n) (t := t) (v := v) (m := m)
      clauses rows repeats hn hbranch hrows δ e) a
  apply hp.trans
  delta ExactPreliminaryTarget.entry
  rw [ProjectionTable.ofMap_apply]
  exact CompletedSignedLaw.descriptorTable_eq_map
    (branch := branch) (n := n) (t := t) (v := v) (m := m)
    clauses rows repeats hn hbranch hrows δ e a

def occurrenceAt (source : PreliminarySampler.Questions branch n t m) (i : Fin D) : C :=
  (equiv).symm ⟨source,
    (SignedScheduleIndex.atIndex hq large hn hbranch hrows (sourceSigns clauses source) i).2⟩

theorem occurrenceAt_source (source : PreliminarySampler.Questions branch n t m) (i : Fin D) :
    (occurrenceAt clauses rows repeats hn hbranch hrows δ source i).1.1.1 = source :=
  CompletedSignedLaw.completedEquiv_symm_source (t := t) clauses rows repeats hn hbranch hrows δ _

theorem descriptorOf_occurrenceAt (source : PreliminarySampler.Questions branch n t m) (i : Fin D) :
    descriptorOf clauses rows repeats hn hbranch hrows δ
        (occurrenceAt clauses rows repeats hn hbranch hrows δ source i) =
      SignedScheduleIndex.atIndex hq large hn hbranch hrows (sourceSigns clauses source) i := by
  have roundtrip := congrArg
    (fun x : CompletedSignedLaw.SignedCompleted (branch := branch) (n := n) (t := t)
        clauses rows repeats δ =>
      (⟨sourceSigns clauses x.1, x.2⟩ :
        SignedCompletionSchedule.Descriptor (rows := rows) (repeats := repeats) hq large))
    ((equiv).apply_symm_apply ⟨source,
      (SignedScheduleIndex.atIndex hq large hn hbranch hrows (sourceSigns clauses source) i).2⟩)
  exact roundtrip.trans (by rfl)

theorem ofFn_occurrenceAt (source : PreliminarySampler.Questions branch n t m) :
    List.ofFn (occurrenceAt clauses rows repeats hn hbranch hrows δ source) = localOrder source := by
  have localSchedule :
      List.ofFn (fun i : Fin D =>
        (SignedScheduleIndex.atIndex hq large hn hbranch hrows (sourceSigns clauses source) i).2) =
        SignedCompletionSchedule.schedule hq large hn hbranch hrows (sourceSigns clauses source) := by
    let xs := SignedCompletionSchedule.schedule
      (branch := branch) (n := n) (t := t) («q» := q) (rows := rows) (repeats := repeats)
      hq large hn hbranch hrows (sourceSigns clauses source)
    have hlen : xs.length = D :=
      SignedCompletionSchedule.schedule_length
        (branch := branch) (n := n) (t := t) («q» := q) (rows := rows) (repeats := repeats)
        hq large hn hbranch hrows (sourceSigns clauses source)
    change List.ofFn (fun i : Fin D => xs.get (Fin.cast hlen.symm i)) = xs
    have roundtrip := (List.ofFn_congr hlen xs.get).symm
    rw [List.ofFn_get] at roundtrip
    exact roundtrip
  calc
    _ = (List.ofFn (fun i : Fin D =>
        (SignedScheduleIndex.atIndex hq large hn hbranch hrows (sourceSigns clauses source) i).2)).map
          (fun outcome => (equiv).symm ⟨source, outcome⟩) := List.ofFn_comp' _ _
    _ = localOrder source := by rw [localSchedule]; rfl

theorem map_finRange_occurrenceAt (source : PreliminarySampler.Questions branch n t m) :
    (List.finRange D).map (occurrenceAt clauses rows repeats hn hbranch hrows δ source) =
      localOrder source := by
  rw [← List.ofFn_eq_map]
  exact ofFn_occurrenceAt clauses rows repeats hn hbranch hrows δ source

def dataOfPrefix (earlier : List C) (tail : List Bool) : SignedTupleBodyMachine.Data width where
  leftKeys := ExactTargetOnlineEncoding.leftKeys (t := t) clauses rows repeats hn hbranch hrows δ earlier
  rightKeys := ExactTargetOnlineEncoding.rightKeys (t := t) clauses rows repeats hn hbranch hrows δ earlier
  reversedOutput := (earlier.flatMap (fun e => encodeWords (Encoding.edgeWords (targetEntry e)))).reverse ++ tail
  count := earlier.length

theorem edgeBits_eq_entry (earlier suffix : List C) (e : C)
    (split : order = earlier ++ e :: suffix) :
    CompletedEdgeMachine.edgeBits hq large (descriptorOf clauses rows repeats hn hbranch hrows δ e)
        (ExactTargetOnlineEncoding.leftKeys (t := t) clauses rows repeats hn hbranch hrows δ earlier)
        (ExactTargetOnlineEncoding.rightKeys (t := t) clauses rows repeats hn hbranch hrows δ earlier)
        (sourceIDs e.1.1.1) (sourceVariables clauses e.1.1.1) =
      encodeWords (Encoding.edgeWords (targetEntry e)) := by
  rw [CompletedEdgeMachine.edgeBits_eq, left_key, right_key,
    DescriptorProjectionMachine.outputBits, DescriptorProjectionMachine.outputWords, projection_eq,
    ExactTargetOnlineEncoding.left_online (t := t) clauses rows repeats hn hbranch hrows δ
      earlier suffix e split,
    ExactTargetOnlineEncoding.right_online (t := t) clauses rows repeats hn hbranch hrows δ
      earlier suffix e split]
  simp only [Encoding.edgeWords, encodeWords_append, encodeWords, List.append_nil, List.append_assoc]

theorem next_eq_append (earlier suffix : List C) (e : C) (tail : List Bool)
    (split : order = earlier ++ e :: suffix) :
    SignedTupleBodyMachine.next hq large (descriptorOf clauses rows repeats hn hbranch hrows δ e)
        (sourceIDs e.1.1.1) (sourceVariables clauses e.1.1.1)
        (dataOfPrefix clauses rows repeats hn hbranch hrows δ earlier tail) =
      dataOfPrefix clauses rows repeats hn hbranch hrows δ (earlier ++ [e]) tail := by
  have hbits := edgeBits_eq_entry clauses rows repeats hn hbranch hrows δ earlier suffix e split
  simp only [ExactTargetOnlineEncoding.leftKeys, ExactTargetOnlineEncoding.rightKeys] at hbits
  simp only [SignedTupleBodyMachine.next, dataOfPrefix, left_key, right_key,
    hbits,
    ExactTargetOnlineEncoding.leftKeys, ExactTargetOnlineEncoding.rightKeys,
    List.map_append, List.map_cons, List.map_nil, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.reverse_append,
    List.length_append, List.length_cons, List.length_nil, Nat.zero_add, List.append_assoc]

theorem next_atIndex_eq (source : PreliminarySampler.Questions branch n t m) (i : Fin D)
    (earlier suffix : List C) (tail : List Bool)
    (split : order = earlier ++ occurrenceAt clauses rows repeats hn hbranch hrows δ source i :: suffix) :
    SignedTupleBodyMachine.next hq large
        (SignedScheduleIndex.atIndex hq large hn hbranch hrows (sourceSigns clauses source) i)
        (sourceIDs source) (sourceVariables clauses source)
        (dataOfPrefix clauses rows repeats hn hbranch hrows δ earlier tail) =
      dataOfPrefix clauses rows repeats hn hbranch hrows δ
        (earlier ++ [occurrenceAt clauses rows repeats hn hbranch hrows δ source i]) tail := by
  simpa only [descriptorOf_occurrenceAt, occurrenceAt_source] using
    next_eq_append clauses rows repeats hn hbranch hrows δ earlier suffix
      (occurrenceAt clauses rows repeats hn hbranch hrows δ source i) tail split

theorem result_eq_append (source : PreliminarySampler.Questions branch n t m)
    (indices : List (Fin D)) (earlier suffix : List C) (tail : List Bool)
    (split : order = earlier ++
      indices.map (occurrenceAt clauses rows repeats hn hbranch hrows δ source) ++ suffix) :
    SignedTupleBodyMachine.result hq large hn hbranch hrows (sourceSigns clauses source)
        (sourceIDs source) (sourceVariables clauses source) indices
        (dataOfPrefix clauses rows repeats hn hbranch hrows δ earlier tail) =
      dataOfPrefix clauses rows repeats hn hbranch hrows δ
        (earlier ++ indices.map (occurrenceAt clauses rows repeats hn hbranch hrows δ source)) tail := by
  induction indices generalizing earlier with
  | nil => simp only [SignedTupleBodyMachine.result, List.map_nil, List.append_nil]
  | cons i indices ih =>
    let e := occurrenceAt clauses rows repeats hn hbranch hrows δ source i
    have currentSplit : order = earlier ++ e ::
        (indices.map (occurrenceAt clauses rows repeats hn hbranch hrows δ source) ++ suffix) := by
      simpa only [e, List.map_cons, List.append_assoc, List.cons_append] using split
    rw [SignedTupleBodyMachine.result,
      next_atIndex_eq clauses rows repeats hn hbranch hrows δ source i earlier
        (indices.map (occurrenceAt clauses rows repeats hn hbranch hrows δ source) ++ suffix) tail currentSplit]
    have restSplit : order = (earlier ++ [e]) ++
        indices.map (occurrenceAt clauses rows repeats hn hbranch hrows δ source) ++ suffix := by
      simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
        using currentSplit
    simpa only [e, List.map_cons, List.append_assoc, List.singleton_append, List.cons_append,
      List.nil_append] using
      ih (earlier ++ [e]) restSplit

theorem full_result_eq (source : PreliminarySampler.Questions branch n t m)
    (earlier suffix : List C) (tail : List Bool)
    (split : order = earlier ++ localOrder source ++ suffix) :
    SignedTupleBodyMachine.result hq large hn hbranch hrows (sourceSigns clauses source)
        (sourceIDs source) (sourceVariables clauses source) (List.finRange D)
        (dataOfPrefix clauses rows repeats hn hbranch hrows δ earlier tail) =
      dataOfPrefix clauses rows repeats hn hbranch hrows δ (earlier ++ localOrder source) tail := by
  have indexedSplit : order = earlier ++
      (List.finRange D).map (occurrenceAt clauses rows repeats hn hbranch hrows δ source) ++ suffix := by
    rwa [map_finRange_occurrenceAt]
  simpa only [map_finRange_occurrenceAt] using
    result_eq_append clauses rows repeats hn hbranch hrows δ source (List.finRange D)
      earlier suffix tail indexedSplit

end
end PerfectCompleteness.SignedTupleSemantics

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

inductive Label (locations stages : Nat) (Descriptor Extra : Type)
  | body (label : SignedTupleBodyMachine.BodyLabel locations stages Descriptor Extra)
  | check (coordinate : Fin locations)
  | reset (coordinate : Fin locations)
  | exit
  deriving DecidableEq, Fintype

end PerfectCompleteness.ExactTargetOdometer

end OAI
end


