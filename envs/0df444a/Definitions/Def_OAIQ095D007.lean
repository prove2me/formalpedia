-- Prove2me | Definitions.Def_OAIQ095D007
-- name    : OAIQ095D007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:06:29.038403+00:00
-- url     : https://prove2.me/theorems/f03661ee-eca8-41c8-abe9-d9df08dba33f
-- title:
--   Definitions bundle OAIQ095D007 of the split of OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 166 declarations of OpenAI's Lean: 133 definitions, 2 instances and 31 theorems. The definitions and types are `OAI.Ostmann.movingOriginalPatternWeight`, `OAI.Ostmann.movingOuterKernel`, `OAI.Ostmann.movingPairCompensatedMass`, `OAI.Ostmann.movingPatternBulkLeaves`, `OAI.Ostmann.movingPatternBulkMean`, `OAI.Ostmann.movingPatternExternalMultiplier`, `OAI.Ostmann.movingPatternFinBulkData`, `OAI.Ostmann.movingPatternFinData`, `OAI.Ostmann.movingPatternFinRepresentative`, `OAI.Ostmann.movingPatternFiniteSamples`, `OAI.Ostmann.movingPatternRegularSlots`, `OAI.Ostmann.movingPatternRepresentative`, `OAI.Ostmann.movingPatternSamples`, `OAI.Ostmann.movingPatternSlotData`, `OAI.Ostmann.movingPatternTemplateEquiv`, `OAI.Ostmann.movingPrimeLineSupport`, `OAI.Ostmann.movingRealFourierWeight`, `OAI.Ostmann.movingRealGateWeight`, `OAI.Ostmann.movingRealKernel`, `OAI.Ostmann.movingRealKernelPair`, `OAI.Ostmann.movingRealRootCuts`, `OAI.Ostmann.movingRealSmoothWeight`, `OAI.Ostmann.movingReducedPairModulus`, `OAI.Ostmann.movingReducedPairModulusBase`, `OAI.Ostmann.movingReducedPairResidueCoefficient`, `OAI.Ostmann.movingReducedResidueSupport`, `OAI.Ostmann.movingReducedResidueWeight`, `OAI.Ostmann.movingRepresentativeLine`, `OAI.Ostmann.movingResidueCoefficient`, `OAI.Ostmann.movingRestoredPrimeSets`, `OAI.Ostmann.movingRestoredTiers`, `OAI.Ostmann.movingSampleRootFactor`, `OAI.Ostmann.movingSeparatedPairResidueCoefficient`, `OAI.Ostmann.movingSeparatedResidueCoefficient`, `OAI.Ostmann.movingSeparatedSupport`, `OAI.Ostmann.movingSignedAuxiliaryUnits`, `OAI.Ostmann.movingSignedFrequencyUnits`, `OAI.Ostmann.movingSlotLineProbability`, `OAI.Ostmann.movingSmallSlotEquiv`, `OAI.Ostmann.movingSpectatorHaarAverage` and 93 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `Ostmann_Arithmetic_CommonRootMesh`, `Ostmann_Arithmetic_FrequencyTreeNodes`, `Ostmann_Arithmetic_MovingAuxiliaryPeriod`, `Ostmann_Arithmetic_MovingCanonicalWeights`, `Ostmann_Arithmetic_MovingFullResidues`, `Ostmann_Arithmetic_MovingIntegralFrequencySplit`, `Ostmann_Arithmetic_MovingKernelPair`, `Ostmann_Arithmetic_MovingLineIntegration`, `Ostmann_Arithmetic_MovingNormalizedSymmetrizedEnergy`, `Ostmann_Arithmetic_MovingOriginalDiagonalPatterns`, `Ostmann_Arithmetic_MovingOuterKernel`, `Ostmann_Arithmetic_MovingPatternArithmeticComparison`, `Ostmann_Arithmetic_MovingPatternBulkBudgets`, `Ostmann_Arithmetic_MovingPatternBulkData`, `Ostmann_Arithmetic_MovingPatternBulkLog`, `Ostmann_Arithmetic_MovingPatternBulkMean`, `Ostmann_Arithmetic_MovingPatternFinite`, `Ostmann_Arithmetic_MovingPatternRegularSupport`, `Ostmann_Arithmetic_MovingPatternTemplateEnumeration`, `Ostmann_Arithmetic_MovingPatternTree`, `Ostmann_Arithmetic_MovingPrimeLineGate`, `Ostmann_Arithmetic_MovingRealCells`, `Ostmann_Arithmetic_MovingRealKernel`, `Ostmann_Arithmetic_MovingRealSmooth`, `Ostmann_Arithmetic_MovingReducedModulus`, `Ostmann_Arithmetic_MovingReducedOuterFactor`, `Ostmann_Arithmetic_MovingReducedSupport`, `Ostmann_Arithmetic_MovingRepresentativeLineSystem`, `Ostmann_Arithmetic_MovingRestoredPrimeLaws`, `Ostmann_Arithmetic_MovingRestoredTierSeparation`, `Ostmann_Arithmetic_MovingSampleCoordinateLevels`, `Ostmann_Arithmetic_MovingSampleMap`, `Ostmann_Arithmetic_MovingSampleOccurrence`, `Ostmann_Arithmetic_MovingSamplePatternBudget`, `Ostmann_Arithmetic_MovingSampledRecursion`, `Ostmann_Arithmetic_MovingSeparatedAverages`, `Ostmann_Arithmetic_MovingSeparatedCoefficient`, `Ostmann_Arithmetic_MovingSeparatedPair`, `Ostmann_Arithmetic_MovingSpectatorModulus`, `Ostmann_Arithmetic_MovingSymmetrizedMaskedEnergy`, `Ostmann_Arithmetic_MovingSymmetrizedMaskedKernel`, `Ostmann_Arithmetic_MovingTemplateAmplitude`, `Ostmann_Arithmetic_MovingTemplateExternalMultiplier`, `Ostmann_Arithmetic_MovingTemplatePrimeStatistic`, `Ostmann_Arithmetic_MovingTopCells`, `Ostmann_Arithmetic_MovingWeightedDiagonalRelabel`, `Ostmann_Arithmetic_MovingWindowCells`, `Ostmann_Arithmetic_RangedExpandedWordPairBound`, `Ostmann_Characters_AllCharacterDecorrelation`, `Ostmann_Characters_CharacterNonbulkBudget`, `Ostmann_Characters_NormalizedResidueFamily`, `Ostmann_Characters_PolynomialIntegerCharacterSum`, `Ostmann_Characters_QuartetHorizontalMean`, `Ostmann_Characters_QuartetIndexCoordinates`, `Ostmann_Characters_QuartetLocalBounds`, `Ostmann_Characters_QuartetProductFibers`, `Ostmann_Characters_QuartetProductProjection`, `Ostmann_Characters_SparseCoefficientMajorant`, `Ostmann_Characters_SparseExpandedMean`, `Ostmann_Characters_SparsePolydiscBlocks`, `Ostmann_Characters_SparsePrimeMean`, `Ostmann_Characters_SparsePrimitiveExpansion`, `Ostmann_Characters_SparseTensorKernel`, `Ostmann_Characters_SparseTensorModes`, `Ostmann_Characters_SparseTensorPolynomial`, `Ostmann_Characters_SparseWeightPairAverage`, `Ostmann_Characters_TensorUnitPolynomial`, `Ostmann_Characters_TreeLeafProducts`, `Ostmann_Construction_CompleteTailGiantMean`, `Ostmann_Construction_CopiedPriorFubini`, `Ostmann_Construction_FinalParityPaths`, `Ostmann_Construction_HalfPrimeInitialAmplitude`, `Ostmann_Construction_InitialCellSchedule`, `Ostmann_Construction_InitialMovingSmallPermutation`, `Ostmann_Construction_InitialScheduledPrior`, `Ostmann_Construction_MaskedPhaseGiantMean`, `Ostmann_Construction_OriginalAveragedTransfer`, `Ostmann_Construction_OriginalFourierCoefficients`, `Ostmann_Construction_OriginalKernelDecomposition`, `Ostmann_Construction_OriginalOffWitnessMoment`, `Ostmann_Construction_OriginalPositiveFirstMoment`, `Ostmann_Construction_OriginalSignedFourier`, `Ostmann_Construction_PairedScheduledHistory`, `Ostmann_Construction_PhaseGiantTest`, `Ostmann_Construction_PhysicalAmplification`, `Ostmann_Construction_PrimeGuardedAmplitude`, `Ostmann_Construction_PrimePhysicalTest`, `Ostmann_Construction_RegularInitialAmplitude`, `Ostmann_Construction_RetainedCharacterPrimeBound`, `Ostmann_Construction_ScheduledAmplitude`, `Ostmann_Construction_ScheduledArithmeticIteration`, `Ostmann_Construction_ScheduledCellGap`, `Ostmann_Construction_ScheduledCellIteration`, `Ostmann_Construction_ScheduledCopiedAmplitude`, `Ostmann_Construction_ScheduledCurrentAmplitude`, `Ostmann_Construction_ScheduledFrequencyHistory`, `Ostmann_Construction_ScheduledHistoryEmbedding`, `Ostmann_Construction_ScheduledLeafProducts`, `Ostmann_Construction_ScheduledMatchedEdges`, `Ostmann_Construction_ScheduledNodeSources`, `Ostmann_Construction_ScheduledRootIndex`, `Ostmann_Construction_ScheduledSampleQuotient`, `Ostmann_Construction_ScheduledSourceScheme`, `Ostmann_Construction_ScheduledTransferGraph`, `Ostmann_Construction_TailFourierMass`, `Ostmann_Construction_TwoCoordinatePrior`, `Ostmann_Construction_WordTransferFullPeriod`, `Ostmann_QuadraticCenter_AmplificationWeight`, `Ostmann_QuadraticCenter_DivisorFrequencyExpansion`, `Ostmann_QuadraticCenter_OffWitnessFamily`, `Ostmann_QuadraticCenter_PrimeDivisorEnergy`, `Ostmann_QuadraticCenter_PrimeSetQuadratic`, `Ostmann_QuadraticCenter_SplitPrimeAfterExclusion`, `Ostmann_Supply_NonnegativeSparseWeight`.
--
--   **Imports.** It imports the bundles `OAIQ095D003`, `OAIQ095D004` and `OAIQ095D005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ095D008` and `OAIQ095D009`; the statements `OAI.Ostmann.EventuallyPrimeSumset.constructed_initial_amplitude`, `OAI.Ostmann.EventuallyPrimeSumset.constructed_initial_nongiant_priors`, `OAI_Ostmann_EventuallyPrimeSumset_eventual_giant_from_favorable_blocks`, `OAI.Ostmann.EventuallyPrimeSumset.favorable_tail_prime_mass`, `OAI.Ostmann.EventuallyPrimeSumset.initial_broad_prior_centers`, `OAI_Ostmann_EventuallyPrimeSumset_selected_endpoint_giant`, `OAI.Ostmann.EventuallyPrimeSumset.sparse_tail_coverage`, `OAI_Ostmann_EventuallyPrimeSumset_sparse_tail_mass_bound`, `OAI_Ostmann_EventuallyPrimeSumset_tail_spectator_pool`, `OAI.Ostmann.PublishedProgressionInput.all_character_decorrelation`, `OAI_Ostmann_PublishedProgressionInput_concrete_character_band_contradiction`, `OAI_Ostmann_PublishedProgressionInput_constructed_binned_character_priors`, `OAI.Ostmann.PublishedProgressionInput.moving_outer_coprime_mixed_haar_rate`, `OAI_Ostmann_PublishedProgressionInput_moving_selected_initial_amplitude_energy`, `OAI_Ostmann_PublishedProgressionInput_moving_selected_initial_early_log_diagonal`, `OAI_Ostmann_PublishedProgressionInput_moving_selected_initial_full_energy`, `OAI.Ostmann.constituent_final_pair_bound`, `OAI.Ostmann.constituent_signed_supported_pair_bound`, `OAI.Ostmann.eventual_character_atom_iteration`, `OAI.Ostmann.eventual_character_final_contradiction`, `OAI.Ostmann.eventual_constituent_final_pair_decay`, `OAI_Ostmann_eventual_dyadic_two_tail_contradiction`, `OAI.Ostmann.eventual_original_small_second_moment`, `OAI.Ostmann.eventual_original_tuple_witness_lift`, `OAI.Ostmann.eventual_original_witness_probability`, `OAI.Ostmann.eventual_selected_final_natural_energy_comparison`, `OAI.Ostmann.eventual_selected_initial_amplitude`, `OAI.Ostmann.exists_movingPatternPrimeGain_window`, `OAI_Ostmann_few_kernel_populations_impossible`, `OAI.Ostmann.fixed_pivot_full_original_pair_bound`, `OAI_Ostmann_sparseWeightedPrimeSum_decay`, `OAI_Ostmann_sparseWeightedPrimeSum_lower` and `OAI.Ostmann.sparse_finite_contraction`; the proofs of `OAI.Ostmann.EventuallyPrimeSumset.constructed_initial_amplitude`, `OAI.Ostmann.EventuallyPrimeSumset.constructed_initial_nongiant_priors`, `OAI.Ostmann.EventuallyPrimeSumset.favorable_tail_prime_mass`, `OAI.Ostmann.EventuallyPrimeSumset.initial_broad_prior_centers`, `OAI_Ostmann_EventuallyPrimeSumset_selected_endpoint_giant`, `OAI.Ostmann.EventuallyPrimeSumset.sparse_tail_coverage`, `OAI_Ostmann_EventuallyPrimeSumset_sparse_tail_mass_bound`, `OAI_Ostmann_EventuallyPrimeSumset_tail_spectator_pool`, `OAI.Ostmann.PublishedProgressionInput.all_character_decorrelation`, `OAI_Ostmann_PublishedProgressionInput_concrete_character_band_contradiction`, `OAI_Ostmann_PublishedProgressionInput_constructed_binned_character_priors`, `OAI_Ostmann_PublishedProgressionInput_moving_selected_initial_amplitude_energy`, `OAI_Ostmann_PublishedProgressionInput_moving_selected_initial_early_log_diagonal`, `OAI_Ostmann_PublishedProgressionInput_moving_selected_initial_full_energy`, `OAI.Ostmann.constituent_final_pair_bound`, `OAI.Ostmann.constituent_signed_supported_pair_bound`, `OAI.Ostmann.eventual_character_anchor_decay`, `OAI.Ostmann.eventual_character_atom_iteration`, `OAI.Ostmann.eventual_character_final_contradiction`, `OAI.Ostmann.eventual_constituent_final_pair_decay`, `OAI_Ostmann_eventual_dyadic_two_tail_contradiction`, `OAI.Ostmann.eventual_large_kernel_prime_moment`, `OAI.Ostmann.eventual_original_small_second_moment`, `OAI.Ostmann.eventual_original_tail_commonCenter`, `OAI.Ostmann.eventual_original_tuple_witness_lift`, `OAI.Ostmann.eventual_original_witness_probability`, `OAI.Ostmann.eventual_selected_final_natural_energy_comparison`, `OAI.Ostmann.eventual_selected_initial_amplitude`, `OAI.Ostmann.eventual_selected_nonanchor_product_decay`, `OAI.Ostmann.eventual_uniform_character_endpoint_contradiction`, `OAI.Ostmann.exists_movingPatternPrimeGain_window`, `OAI.Ostmann.fixed_pivot_full_original_pair_bound`, `OAI.Ostmann.projectedTree_mean_le`, `OAI_Ostmann_sparseWeightedPrimeSum_decay`, `OAI_Ostmann_sparseWeightedPrimeSum_lower`, `OAI.Ostmann.sparse_finite_contraction`, `OAI_Ostmann_uniform_constituent_natural_history_energy` and `OAI_Ostmann_uniform_constituent_natural_square_rate`.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ095D003
import Definitions.Def_OAIQ095D004
import Definitions.Def_OAIQ095D005

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_CommonRootMesh
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One explicit root mesh for all residue classes -/

namespace Ostmann
open scoped BigOperators Classical
open MeasureTheory

noncomputable def rootMeshWeight {k : ℕ} (F : Fin k → ClippedPolynomialFactor)
    (w : ℝ → ℂ) (s : ℕ → ℝ) (j : ℕ) (y : ℝ) : ℂ :=
  w (Real.exp ((s j + s (j + 1)) / 2)) * smoothPolynomialWeight F (Real.exp y)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TreeLeafProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Leaf-product fibers in a full binary tree -/

namespace Ostmann

open scoped BigOperators

noncomputable instance treeLeafFiberFintype (U : Type*) [CommGroup U] [Fintype U]
    (n : ℕ) (P : U) : Fintype (TreeLeafFiber U n P) := by
  classical
  unfold TreeLeafFiber
  infer_instance

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrequencyTreeNodes
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preorder frequency data and its exact product of split costs -/

namespace Ostmann

open scoped BigOperators Classical

def treeNodeFrequencies (S : Finset ℤ) (n : ℕ) (x : FrequencyTree (S × S) n)
    (j : ℕ) : NodeFrequencies × NodeFrequencies :=
  (frequencySplitList S n x).getD j (emptyNodeFrequencies, emptyNodeFrequencies)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialIntegerCharacterSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the residue classes of the long-integer interval -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

noncomputable def supportedPolynomialWeight {n t : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) (keep : (Fin t → Bool) → Bool) (x : ℝ) : ℂ :=
  (if keep (polynomialSupportCode H x) = true then 1 else 0) *
    (Complex.ofReal (x⁻¹) * smoothPolynomialWeight F x)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetProductFibers
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent product fibers at the bottom quartet level -/

namespace Ostmann

open scoped BigOperators

noncomputable instance quartetProductFiberFintype (U : Type*) [CommGroup U] [Fintype U]
    (n : ℕ) (P : TreeLeafIndex n → U) : Fintype (QuartetProductFiber U n P) := by
  classical
  unfold QuartetProductFiber
  infer_instance

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetIndexCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Leaf coordinates within a labeled bottom quartet -/

namespace Ostmann

open scoped BigOperators

theorem quartetLeafIndex_coordinates (n : ℕ) (j : TreeLeafIndex (n + 2)) :
    quartetLeafIndex n (quartetLeafCoordinates n j).1 (quartetLeafCoordinates n j).2 = j := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases j with
    | inl j => exact congrArg Sum.inl (ih j)
    | inr j => exact congrArg Sum.inr (ih j)

def quartetIndexFiberEquiv (n : ℕ) (q : TreeLeafIndex n) :
    {j : TreeLeafIndex (n + 2) // bottomQuartet n j = q} ≃ TreeLeafIndex 2 where
  toFun j := (quartetLeafCoordinates n j.1).2
  invFun j := ⟨quartetLeafIndex n q j, bottomQuartet_leafIndex n q j⟩
  left_inv j := by
    apply Subtype.ext
    have h := quartetLeafIndex_coordinates n j.1
    rw [quartetLeafCoordinates_fst, j.property] at h
    exact h
  right_inv j := congrArg Prod.snd (quartetLeafCoordinates_index n q j)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferFullPeriod
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full small-frequency modulus, including every node's unit tests -/

namespace Ostmann

open scoped Classical

def wordTransferFullPeriod (n : ℕ) (t : FrequencyTree ℤ n) (B : ℕ) : ℕ :=
  historyFrequencyPeriod (internalFrequencyList n t) (B ^ (n + 1) + 1) *
    historyFrequencyBase (allFrequencyList n t)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_PrimeSetQuadratic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual quadratic density sums indexed by prime divisors -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap

noncomputable def primeSetQuadraticSum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : ∀ p : ℕ, Finset (ZMod p)) (W : Finset ℕ)
    (a : ZMod P.toList.prod) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v : ℝ) (s : ℕ) : ℂ :=
  let : NeZero P.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime P hP)).ne'⟩
  quadraticDensitySum
    (densityFourier (densityCRTList _ (primeSet_list_prime P hP) (primeSet_list_coprime P hP) S).value)
    W a θ Φ R v s

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_AmplificationWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original positive periodic amplification weight -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def primeDivisorDensity (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (U : Finset ℕ) : ZMod U.toList.prod → ℂ :=
  if hU : U ⊆ Q then
    let : NeZero U.toList.prod :=
      ⟨(prime_list_prod_pos U.toList (primeSet_list_prime U (fun p hp => hQ p (hU hp)))).ne'⟩
    (densityCRTList U.toList
      (primeSet_list_prime U (fun p hp => hQ p (hU hp)))
      (primeSet_list_coprime U (fun p hp => hQ p (hU hp))) D).value
  else fun _ => 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PhysicalAmplification
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original physical-space amplified moment -/

namespace Ostmann

open scoped BigOperators SchwartzMap

noncomputable def physicalWeight (Q : Finset ℕ) (D : ∀ p : ℕ, Finset (ZMod p))
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (n : ℤ) : ℝ :=
  (ψ ((n : ℝ) / X)).re * amplificationWeight Q D n

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FinalParityPaths
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two equally sized final-parity classes of actual copy paths -/

namespace Ostmann

open scoped Classical

noncomputable def parityPathsEquiv (n : ℕ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    ParityPaths n ε ≃ (Fin n → Bool) := by
  let f : ParityPaths n ε → (Fin n → Bool) := fun t => Fin.init t.val
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    have ha := finalCopyParity_snoc (Fin.init a.val) (a.val (Fin.last n))
    have hb := finalCopyParity_snoc (Fin.init b.val) (b.val (Fin.last n))
    rw [Fin.snoc_init_self, a.property] at ha
    rw [Fin.snoc_init_self, b.property] at hb
    change Fin.init a.val = Fin.init b.val at hab
    have hn : finalCopyParity (Fin.init a.val) ≠ 0 := by
      change copyPathParity (finiteCopyPath (Fin.init a.val)) n ≠ 0
      rcases copyPathParity_sign (finiteCopyPath (Fin.init a.val)) n with h | h <;> omega
    have hl : a.val (Fin.last n) = b.val (Fin.last n) := by
      apply transferCopySign_injective
      apply mul_right_cancel₀ hn
      rw [hab]
      simpa only [hab] using ha.symm.trans hb
    apply Subtype.ext
    calc
      a.val = Fin.snoc (Fin.init a.val) (a.val (Fin.last n)) := (Fin.snoc_init_self _).symm
      _ = Fin.snoc (Fin.init b.val) (b.val (Fin.last n)) := by rw [hab, hl]
      _ = b.val := Fin.snoc_init_self _
  · intro t
    let b : Bool := decide (ε * finalCopyParity t = 1)
    have hp := copyPathParity_sign (finiteCopyPath t) n
    change finalCopyParity t = 1 ∨ finalCopyParity t = -1 at hp
    have he : finalCopyParity (Fin.snoc t b) = ε := by
      rw [finalCopyParity_snoc]
      rcases hε with hε | hε <;> rcases hp with hp | hp <;>
        simp only [b, hε, hp, mul_one, mul_neg_one, neg_neg, decide_true, decide_false,
          show ¬(-1 : ℤ) = 1 by omega, transferCopySign] <;> norm_num
    exact ⟨⟨Fin.snoc t b, he⟩, @Fin.init_snoc n (fun _ => Bool) b t⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TwoCoordinatePrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating the selected pair inside the unchanged original product prior -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def twoCoordinateEquiv {V A : Type*} (a b : V) (hab : a ≠ b) :
    ((OtherVertices a b → A) × (A × A)) ≃ (V → A) where
  toFun x := twoCoordinateAssignment a b hab x.1 x.2.1 x.2.2
  invFun x := (fun v => x v, x a, x b)
  left_inv x := by
    apply Prod.ext
    · funext v; exact twoCoordinateAssignment_other a b hab _ _ _ v
    · exact Prod.ext (twoCoordinateAssignment_short a b hab _ _ _)
        (twoCoordinateAssignment_long a b hab _ _ _)
  right_inv x := by
    funext v
    obtain ⟨w, rfl⟩ := (twoVertexEquiv a b hab).surjective v
    cases w with
    | inl t => cases t <;> simp
    | inr v => simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RangedExpandedWordPairBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-prior correlation with every intermediate range test -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

noncomputable def rangedWordTransferPairBound {σ : Type*} {n : ℕ}
    (template template' : WordTransferTemplate σ n)
    (D D' : WordRangeDecoration σ n) (t t' : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (hn' : NonzeroInternalFrequencies n t')
    (B : ℕ) (f f' : WordFourierParameters n) (A E : ℕ)
    (P Q : Finset ℕ) (b : ℝ) (Bq : ℕ) : ℝ :=
  let M := wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B
  let R := (3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1)
  let C := f.budget template t hn * f'.budget template' t' hn'
  ((Nat.log 2 E + 1 : ℕ) : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ *
    (((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * b⁻¹) * (2 * C ^ 2) +
      (M : ℝ) * ((3 ^ (2 * (R + R)) : ℕ) * (2 * (A : ℝ)⁻¹ * C ^ 2)) * (Bq : ℝ) ^ 2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTopCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual top-giant residue cells for the moving arithmetic support -/

namespace Ostmann
open scoped Classical

/-- The period depends only on the fixed small data and frequencies. -/
noncomputable def movingTopPeriod {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) : ℕ :=
  movingArithmeticPeriod (T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFullResidues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full moving support as one explicit residue mask -/

namespace Ostmann
open scoped Classical

noncomputable def movingSquareLineSupport {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℤ) : Prop :=
  ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots,
    let φ := MovingSlotReversal.naturalReduction (value i ^ 2) value
    φ (movingSlotLine o.path o.current).a * (XL : ZMod (value i ^ 2)) +
      φ (movingSlotLine o.path o.current).b * (XR : ZMod (value i ^ 2)) ≠ 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingWindowCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sharp terminal windows have explicit polynomial root cells -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingWindowPolynomials {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (L R : Polynomial ℝ) (X lo hi : ℝ)
    (i : TreeLeafIndex n × Bool) : Polynomial ℝ :=
  if i.2 then Polynomial.C hi - movingLeafNormalizedPolynomial value T L R X i.1
  else movingLeafNormalizedPolynomial value T L R X i.1 - Polynomial.C lo

noncomputable def movingWindowRootCuts {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (L R : Polynomial ℝ) (X lo hi : ℝ) : Finset ℝ :=
  polynomialRootCuts (movingWindowPolynomials value T L R X lo hi)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRealCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Residue-independent cells for either real giant coordinate -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingRealGateWeight {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (X lo hi : ℝ)
    (x : Bool → ℝ) : ℂ :=
  movingArchimedeanFlag nodes x * movingRealWindowFlag value T X lo hi (x false) (x true)

noncomputable def movingRealRootCuts {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (X lo hi : ℝ)
    (coord : Bool) (fixed : ℝ) : Finset ℝ :=
  movingArchimedeanRootCuts nodes (topGiantReal fixed fixed) coord ∪
    movingWindowRootCuts value T (movingCoordinateLeft coord fixed)
      (movingCoordinateRight coord fixed) X lo hi

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCanonicalWeights
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical residue coefficients of the original moving weight -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingResidueCoefficient {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (a b : ℕ) : ℂ :=
  (movingResidueFlag nodes (topGiantInput a b) * movingSpectatorResidue q value g D S T a b) *
    movingDataWeight F E T

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRealSmooth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single real smooth kernel for the two original giant coordinates -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate SchwartzMap

noncomputable def movingRealFourierWeight {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (L R : ℝ) : ℂ :=
  ∏ i : TreeLeafIndex n,
    let v := (fourierPolynomialFactor Polynomial.X ψ (T.leafFrequencies i) lo hi hlo hhi).value
      (T.realLeafModuli value L R i / X)
    if treeLeafTupleEquiv Bool n (transferConjugations n false) i then conj v else v

noncomputable def movingRealSmoothWeight {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) : ℂ :=
  movingRealFourierWeight value T ψ X lo hi hlo hhi L R * movingRealNodeCutoff value φ G T L R

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRealKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurability and uniform bounds for the original two-giant kernel -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate SchwartzMap
open MeasureTheory

noncomputable def movingRealKernel {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) : ℂ :=
  movingRealGateWeight value T nodes X lo hi (topGiantReal L R) *
    movingRealSmoothWeight value T ψ X lo hi hlo hhi φ G L R

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingAuxiliaryPeriod
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A residue period that omits inherited regular-slot unit tests -/

namespace Ostmann
open scoped Classical

noncomputable def movingSignedAuxiliaryUnits {σ : Type*} (value : σ → ℕ) (outside : List ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → Prop
  | _, T@(.leaf _ _), XL, XR => movingAuxiliaryLocalUnits outside T XL XR
  | _, T@(.node s CL CR U left right), XL, XR =>
      let p := (MovingSlotData.step s CL CR U left right false).signedPivot value XL XR
      movingAuxiliaryLocalUnits outside T XL XR ∧
        movingSignedAuxiliaryUnits value outside left p XL ∧ movingSignedAuxiliaryUnits value outside right p XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPrimeLineGate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The internal-prime gate on the original top giant pair -/

namespace Ostmann
open scoped Classical

noncomputable def movingPrimeLineSupport {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (x y : ℤ) : Prop :=
  ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots,
    let φ := MovingSlotReversal.naturalReduction (value i) value
    φ (movingSlotLine o.path o.current).a * (x : ZMod (value i)) +
      φ (movingSlotLine o.path o.current).b * (y : ZMod (value i)) = 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingIntegralFrequencySplit
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact frequency and internal-prime splitting before real restrictions

All divisions here are integer divisions. Positivity is deliberately left to
the existing real gate. The equivalence recovers integer divisibility from
the two disjoint residue blocks, including at every descendant node.
-/

namespace Ostmann
open scoped Classical

def movingSignedFrequencyUnits {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → Prop
  | _, T@(.leaf _ _), x, y => movingFrequencyLocalUnits T x y
  | _, T@(.node s CL CR U left right), x, y =>
      let p := (MovingSlotData.step s CL CR U left right false).signedPivot value x y
      movingFrequencyLocalUnits T x y ∧
        movingSignedFrequencyUnits value left p x ∧ movingSignedFrequencyUnits value right p y

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingKernelPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal product of the two histories in a diagonal comparison -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators Classical ComplexConjugate SchwartzMap

noncomputable def movingRealKernelPair {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) : ℂ :=
  movingRealKernel value (T false) (nodes false) ψ X lo hi hlo hhi φ G L R *
    conj (movingRealKernel value (T true) (nodes true) ψ X lo hi hlo hhi φ G L R)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingLineIntegration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating the actual moving-giant line systems on their full support -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def movingSlotLineProbability {A J : Type*} {n : ℕ}
    (value : A → ℤ) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (path : J → List (MovingSlotReversal (Fin n)))
    (current : J → MovingSlotReversal (Fin n)) (external : Bool)
    (x : Fin n → A) (a : A) : ℝ :=
  let _ : Fact (prime a).Prime := ⟨hprime a⟩
  let φ := integerLineReduction value x (prime a)
  internalLineProbability external
    (fun j => ((movingSlotLine (path j) (current j)).normalized φ).1)
    (fun j => ((movingSlotLine (path j) (current j)).normalized φ).2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingReducedSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The recursive residue support after extracting the regular-prime units -/

namespace Ostmann
open scoped Classical

noncomputable def movingReducedResidueSupport {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℤ) : Prop :=
  movingRegularOutsidePairwise value outside T ∧ movingSquareLineSupport value T XL XR ∧
    movingSignedAuxiliaryUnits value outside T XL XR

noncomputable def movingReducedResidueWeight {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (a b : ℤ) (z : ℂ) : ℂ :=
  if movingReducedResidueSupport value outside T a b then z else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSpectatorModulus
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A concrete modulus for arithmetic support and all spectator trees -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingSpectatorModulus {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (q : I → ℕ) (S : Finset I) : ℕ :=
  movingTopPeriod value hvalue childBound pivotBound T hf *
    (movingSpectatorDenominator value T).natAbs * ∏ i ∈ S, q i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingReducedModulus
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The common residue modulus after extracting the regular primes -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def movingReducedPairModulusBase {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (q : I → ℕ) (S : Finset I) : ℕ :=
  ∏ b : Bool, movingSpectatorModulus value hvalue childBound pivotBound (T b) (hf b) q S *
    (movingAuxiliaryUnitPeriod value outside (T b)).natAbs

noncomputable def movingReducedPairModulus {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (q : I → ℕ) (S : Finset I) : ℕ :=
  (movingReducedPairModulusBase value hvalue outside childBound pivotBound T hf q S) ^ 2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOuterKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two-history kernel with its original outer priors and diagonal ratio -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators Classical ComplexConjugate SchwartzMap

noncomputable def movingOuterKernel {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Jleft Jright : ℝ) (diagonal : Bool) (L R : ℝ) : ℂ :=
  movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G L R *
    giantOuterWeight φ Jleft Jright diagonal L R

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingReducedOuterFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original outer priors with the regular block removed from the residue coefficient -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate SchwartzMap

noncomputable def movingReducedPairResidueCoefficient {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : Bool → ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (a b : ℕ) : ℂ :=
  movingReducedResidueWeight value outside (T false) a b
      (movingResidueCoefficient q value (F false) (E false) g (Dq false) S (T false) (nodes false) a b) *
    conj (movingReducedResidueWeight value outside (T true) a b
      (movingResidueCoefficient q value (F true) (E true) g (Dq true) S (T true) (nodes true) a b))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSeparatedCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original remainder coefficient in separated arithmetic coordinates -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingSeparatedSupport {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n) (nodes : List MovingFormulaNode)
    (R : ℤ) (x y : ℤ) : Prop :=
  movingRegularOutsidePairwise value outside T ∧ movingSquareLineSupport value T x y ∧
    (∀ f ∈ nodes, f.guard.frequencyBounds) ∧
      movingFrequencyGate value R T x y ∧ movingPrimeLineSupport value T x y

noncomputable def movingSeparatedResidueCoefficient {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (R : ℤ) (x y : ℤ) : ℂ :=
  if movingSeparatedSupport value outside T nodes R x y then
    (∏ i ∈ S, movingModularSpectator value (q i) (g i) (D i) T x y) * movingDataWeight F E T
  else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSeparatedPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The separated two-history coefficient -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def movingSeparatedPairResidueCoefficient {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : Bool → ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (a b : ℕ) : ℂ :=
  movingSeparatedResidueCoefficient q value outside (F false) (E false) g (Dq false) S
      (T false) (nodes false) R a b *
    conj (movingSeparatedResidueCoefficient q value outside (F true) (E true) g (Dq true) S
      (T true) (nodes true) R a b)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSamplePatternBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Applying representative-prior domination to the literal sampled pair -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingPairCompensatedMass {A : Type*} (μ : ℕ → A → ℝ)
    (prime : A → ℕ) {n : ℕ} (a : MovingSampleSlots A n × MovingSampleSlots A n) : ℝ :=
  ((movingSampleProduct prime a.1 : ℝ) * movingSamplesPrior μ a.1) *
    ((movingSampleProduct prime a.2 : ℝ) * movingSamplesPrior μ a.2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleCoordinateLevels
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Tier separation for the original indexed sample tree -/

namespace Ostmann
open scoped Classical

/-- The sample constructor itself enforces the required tier of every
compensation occurrence. No assumption about an independently chosen tree
is needed when the labels are the actual sample coordinates. -/
theorem movingSampleCoordinates_levels {A : Type*} (tier : A → ℕ)
    (n : ℕ) (x : MovingSampleIndex n → A)
    (hx : ∀ i, tier (x i) = movingSampleTier i) :
    ((movingSampleCoordinates A n).symm x).Levels tier := by
  induction n with
  | zero => trivial
  | succ n ih =>
      let u := (treeLeafTupleEquiv (Fin 4 → A) n).symm (fun t j => x (.inl (t, j)))
      change (∀ i ∈ flattenMovingSlots n (movingCompensationSlots n u), tier i = n) ∧ _ ∧ _
      refine ⟨movingCompensationSlots_forall n u _ ?_, ?_, ?_⟩
      · intro t j
        have hu := congrFun (congrFun
          ((treeLeafTupleEquiv (Fin 4 → A) n).apply_symm_apply
            (fun t j => x (.inl (t, j)))) t) j
        change tier (treeLeafTupleEquiv (Fin 4 → A) n u t j) = n
        rw [hu]
        exact hx (.inl (t, j))
      · exact ih (fun i => x (.inr (true, i))) (fun i => hx (.inr (true, i)))
      · exact ih (fun i => x (.inr (false, i))) (fun i => hx (.inr (false, i)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleMap
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Evaluating the fixed indexed sample tree

This identifies the original sampled prime tree with evaluation of fixed
slot data. Thus equality-pattern and polynomial arguments use the same
literal constructor as the sampled coefficient.
-/

namespace Ostmann
open scoped Classical

theorem movingSampleCoordinates_map {A B : Type*} (f : A → B) {n : ℕ}
    (a : MovingSampleSlots A n) (i : MovingSampleIndex n) :
    movingSampleCoordinates B n (a.map f) i = f (movingSampleCoordinates A n a i) := by
  induction a with
  | leaf => exact Empty.elim i
  | @node n u l r hl hr =>
      rcases i with ⟨t, j⟩ | ⟨b, i⟩
      · exact congrFun (treeLeafTupleEquiv_map (fun a : Fin 4 → A => f ∘ a) n u t) j
      · cases b
        · exact hr i
        · exact hl i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternTree
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual pair of sampled trees after fixing an internal pattern -/

namespace Ostmann
open scoped Classical

/-- Fixed external labels and internal equality classes are kept separate.
The latter number depends only on depth, not on the bulk length. -/
def movingPatternSamples (C : Type*) (n : ℕ)
    (pattern : Bool × MovingSampleIndex n → C) (side : Bool) : MovingSampleSlots C n :=
  (movingSampleCoordinates C n).symm (fun i => pattern (side, i))

theorem movingPatternSamples_map {C A : Type*} (f : C → A) (n : ℕ)
    (pattern : Bool × MovingSampleIndex n → C) (side : Bool) :
    (movingPatternSamples C n pattern side).map f =
      movingPatternSamples A n (f ∘ pattern) side := by
  apply (movingSampleCoordinates A n).injective
  funext i
  rw [movingSampleCoordinates_map]
  simp only [movingPatternSamples, Equiv.apply_symm_apply, Function.comp_apply]

def movingPatternSlotData {B C : Type*} (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List B) n) (pattern : Bool × MovingSampleIndex n → C)
    (side : Bool) : MovingSlotData (B ⊕ C) n :=
  buildMovingSlotData n t (treeLeafMap (List.map Sum.inl) n small)
    (treeLeafMap (List.map Sum.inl) n bulk)
    (movingPatternSamples (B ⊕ C) n (Sum.inr ∘ pattern) side)

theorem movingPatternSlotData_levels {B C : Type*} (tierB : B → ℕ) (tierC : C → ℕ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, n ≤ tierB i)
    (hbulk : ∀ i ∈ flattenMovingSlots n bulk, n ≤ tierB i)
    (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2) (side : Bool) :
    (movingPatternSlotData n t small bulk pattern side).Levels (Sum.elim tierB tierC) := by
  apply buildMovingSlotData_levels
  · intro i hi
    rw [flattenMovingSlots_map] at hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    exact hsmall j hj
  · intro i hi
    rw [flattenMovingSlots_map] at hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    exact hbulk j hj
  · apply movingSampleCoordinates_levels
    intro i
    exact htier (side, i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRepresentativeLineSystem
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed occurrence systems for a representative sampled prime -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingRepresentativeLine {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) (rep : σ)
    (j : MovingPairRepresentativeOccurrences T rep) : PolynomialGiantLine σ :=
  let o := (T j.1).occurrences.get j.2.val
  movingSlotLine o.path o.current

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleOccurrence
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An actual occurrence for every internal sample class -/

namespace Ostmann
open scoped Classical

/-- Each independent draw has a genuine node occurrence in the constructed
history; subsequent copies in regular lists are irrelevant to this witness. -/
theorem movingSample_occurs {A : Type*} (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List A) n) (a : MovingSampleSlots A n)
    (i : MovingSampleIndex n) :
    ∃ o ∈ (buildMovingSlotData n t small bulk a).occurrences,
      movingSampleCoordinates A n a i ∈ o.current.compensationSlots := by
  induction a with
  | leaf => exact Empty.elim i
  | @node n a l r hl hr =>
    let U := flattenMovingSlots n (movingCompensationSlots n a)
    let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
    let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
    let L := buildMovingSlotData n t.2.1
      (appendMovingSlotLeaves n (movingCompensationSlots n a) small.1) bulk.1 l
    let R := buildMovingSlotData n t.2.2
      (appendMovingSlotLeaves n (movingCompensationSlots n a) small.2) bulk.2 r
    change ∃ o ∈ (MovingSlotData.node t.1 CL CR U L R).occurrences,
      movingSampleCoordinates A (n + 1) (.node a l r) i ∈ o.current.compensationSlots
    rcases i with ⟨ti, j⟩ | ⟨b, i⟩
    · refine ⟨⟨n + 1, MovingSlotData.step t.1 CL CR U L R false, []⟩, List.mem_cons_self, ?_⟩
      exact movingCompensationSlots_mem n a ti j
    · cases b with
      | false =>
        obtain ⟨o, ho, hi⟩ := hr t.2.2
          (appendMovingSlotLeaves n (movingCompensationSlots n a) small.2) bulk.2 i
        refine ⟨o.extend (MovingSlotData.step t.1 CL CR U L R false), ?_, hi⟩
        exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr ⟨o, ho, rfl⟩))
      | true =>
        obtain ⟨o, ho, hi⟩ := hl t.2.1
          (appendMovingSlotLeaves n (movingCompensationSlots n a) small.1) bulk.1 i
        refine ⟨o.extend (MovingSlotData.step t.1 CL CR U L R true), ?_, hi⟩
        exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨o, ho, rfl⟩))

/-- A representative occurrence exists for every nonempty internal class of
the actual paired pattern, without an extra arithmetic assumption. -/
theorem movingPattern_representative_nonempty {B C : Type*}
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (c : C) :
    Nonempty (MovingPairRepresentativeOccurrences
      (fun side => movingPatternSlotData n (t side) (small side) (bulk side) pattern side) (.inr c)) := by
  let i := rep c
  have h := movingSample_occurs n (t i.val.1)
    (treeLeafMap (List.map Sum.inl) n (small i.val.1)) (treeLeafMap (List.map Sum.inl) n (bulk i.val.1))
    (movingPatternSamples (B ⊕ C) n (Sum.inr ∘ pattern) i.val.1) i.val.2
  simp only [movingPatternSamples, Equiv.apply_symm_apply, Function.comp_apply, i.property] at h
  obtain ⟨o, ho, hi⟩ := h
  change o ∈ (movingPatternSlotData n (t i.val.1) (small i.val.1) (bulk i.val.1) pattern i.val.1).occurrences at ho
  obtain ⟨k, hk, hko⟩ := List.mem_iff_getElem.mp ho
  refine ⟨⟨i.val.1, ⟨⟨k, hk⟩, ?_⟩⟩⟩
  simpa only [List.get_eq_getElem, hko] using hi

noncomputable def movingPatternRepresentative {B C : Type*}
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (c : C) :
    MovingPairRepresentativeOccurrences
      (fun side => movingPatternSlotData n (t side) (small side) (bulk side) pattern side) (.inr c) :=
  Classical.choice (movingPattern_representative_nonempty n t small bulk pattern rep c)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternFinite
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite coordinates for the actual internal-pattern tree pair -/

namespace Ostmann
open scoped Classical

def movingPatternFinData {B C : Type*} {N : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C) (side : Bool) : MovingSlotData (Fin (N + 1)) n :=
  (movingPatternSlotData n (t side) (small side) (bulk side) pattern side).map e.symm

theorem movingPatternFinData_levels {B C : Type*} {N : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (tierB : B → ℕ) (tierC : C → ℕ) (n : ℕ) (t : Bool → FrequencyTree ℤ n)
    (small bulk : Bool → TreeLeafTuple (List B) n) (pattern : Bool × MovingSampleIndex n → C)
    (hsmall : ∀ b, ∀ i ∈ flattenMovingSlots n (small b), n ≤ tierB i)
    (hbulk : ∀ b, ∀ i ∈ flattenMovingSlots n (bulk b), n ≤ tierB i)
    (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2) (side : Bool) :
    (movingPatternFinData e n t small bulk pattern side).Levels ((Sum.elim tierB tierC) ∘ e) := by
  apply (MovingSlotData.levels_map e.symm (Sum.elim tierB tierC) ((Sum.elim tierB tierC) ∘ e)
    (fun i => by simp only [Function.comp_apply, Equiv.apply_symm_apply]) _).mpr
  exact movingPatternSlotData_levels tierB tierC n (t side) (small side) (bulk side) pattern (hsmall side) (hbulk side) htier side

/-- The base row is selected from a proved original occurrence, then mapped
into the finite coordinate system used by polynomial comparison. -/
noncomputable def movingPatternFinRepresentative {B C : Type*} {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (n : ℕ) (t : Bool → FrequencyTree ℤ n)
    (small bulk : Bool → TreeLeafTuple (List B) n) (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (c : C) :
    MovingPairRepresentativeOccurrences (movingPatternFinData e n t small bulk pattern)
      (e.symm (.inr c)) :=
  Classical.choice (movingPairRepresentative_map_nonempty e.symm _ (.inr c)
    (movingPatternRepresentative n t small bulk pattern rep c))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternArithmeticComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original internal arithmetic coefficient versus symbolic flags -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingOriginalPatternWeight {A B C : Type*} [Fintype B] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ) (prime : A → ℕ)
    (n : ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (G : (Fin (N + 1) → A) → ℂ) (x : Fin (N + 1) → A) : ℂ :=
  ((∏ b, ν b (x (e.symm (.inl b))) : ℝ) : ℂ) *
    (movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
      (fun i => x (e.symm (.inr (pattern i))))) : ℂ) * movingPatternInjectionGuard e G x

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledTransferGraph
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricting the graph update to the actual H/Y partition -/

namespace Ostmann

/-- No unused copied or retained alternative occurs in this map. -/
def scheduledOutputVertex {I : Type*} (role : I → CopyScheduleRole) (n : ℕ) :
    (Bool × CopyScheduleH role n) ⊕ CopyScheduleY role n →
      {i : CopyScheduleVertex I (n + 1) // CopyScheduleSurvives role (n + 1) i} :=
  (copyScheduleSurvivorEquiv role n).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_CopiedPriorFubini
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The copied H priors and the single retained Y prior -/

namespace Ostmann

open scoped BigOperators Classical

theorem scheduledCopiedAssignment_left {I A : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (u : CopyScheduleY role n → A) (l r : CopyScheduleH role n → A) (h : CopyScheduleH role n) :
    scheduledCopiedAssignment role n u l r (scheduledOutputVertex role n (.inl (true, h))) = l h := by
  simp only [scheduledCopiedAssignment, scheduledOutputVertex, Equiv.apply_symm_apply]

theorem scheduledCopiedAssignment_right {I A : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (u : CopyScheduleY role n → A) (l r : CopyScheduleH role n → A) (h : CopyScheduleH role n) :
    scheduledCopiedAssignment role n u l r (scheduledOutputVertex role n (.inl (false, h))) = r h := by
  simp only [scheduledCopiedAssignment, scheduledOutputVertex, Equiv.apply_symm_apply]

theorem scheduledCopiedAssignment_outside {I A : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (u : CopyScheduleY role n → A) (l r : CopyScheduleH role n → A) (y : CopyScheduleY role n) :
    scheduledCopiedAssignment role n u l r (scheduledOutputVertex role n (.inr y)) = u y := by
  simp only [scheduledCopiedAssignment, scheduledOutputVertex, Equiv.apply_symm_apply]

noncomputable def scheduledCopiedAssignmentEquiv {I A : Type*}
    (role : I → CopyScheduleRole) (n : ℕ) :
    ((CopyScheduleY role n → A) × ((CopyScheduleH role n → A) × (CopyScheduleH role n → A))) ≃
      ({i : CopyScheduleVertex I (n + 1) // CopyScheduleSurvives role (n + 1) i} → A) where
  toFun a := scheduledCopiedAssignment role n a.1 a.2.1 a.2.2
  invFun a := ((fun y => a (scheduledOutputVertex role n (.inr y))),
    (fun h => a (scheduledOutputVertex role n (.inl (true, h)))),
    (fun h => a (scheduledOutputVertex role n (.inl (false, h)))))
  left_inv a := by
    apply Prod.ext
    · funext y
      exact scheduledCopiedAssignment_outside role n a.1 a.2.1 a.2.2 y
    · apply Prod.ext
      · funext h
        exact scheduledCopiedAssignment_left role n a.1 a.2.1 a.2.2 h
      · funext h
        exact scheduledCopiedAssignment_right role n a.1 a.2.1 a.2.2 h
  right_inv a := by
    funext j
    obtain ⟨i, rfl⟩ := (copyScheduleSurvivorEquiv role n).symm.surjective j
    dsimp only
    rcases i with ⟨b, h⟩ | y
    · cases b
      · exact scheduledCopiedAssignment_right role n _ _ _ h
      · exact scheduledCopiedAssignment_left role n _ _ _ h
    · exact scheduledCopiedAssignment_outside role n _ _ _ y

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalAveragedTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual averaged arithmetic step with its forced integer substitution -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

noncomputable def reconstructedOffDiagonal {A : Type*} [Fintype A]
    (T : Finset ℕ) (V : ℕ) (L : A → ℕ) (v : A → ℤ) (c : ℕ → A → ℂ) : ℂ :=
  ∑ s ∈ transferFrequencyRange V, ∑ a, ∑ b,
    if validTransferredPivot T (v a * L b - v b * L a) s then
      c (reconstructedPivot (v a * L b - v b * L a) s) a *
        conj (c (reconstructedPivot (v a * L b - v b * L a) s) b) else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledCurrentAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The current scheduled amplitude under its original prime priors -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def sampledScheduledPhase {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (n r : ℕ)
    (e : Fin r ≃ CurrentPivotConstituent role n) (t : FrequencyTree ℤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (x : Fin r → P)
    (L : CopyScheduleH role n → ℕ) (U : CopyScheduleY role n → ℕ)
    [∀ h, Fact (L h).Prime] [∀ y, Fact (U y).Prime]
    (center : ∀ p : ℕ, ZMod p) : ℂ := by
  letI : ∀ i, Fact (x i : ℕ).Prime := fun i => ⟨hP _ (x i).property⟩
  letI := scheduledInputPrimeFact role n r e (fun i => (x i : ℕ)) L U
  exact scheduledPrimePhase role χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t
    (scheduledInputLabels role n r e (fun i => (x i : ℕ)) L U) center

noncomputable def scheduledCurrentAmplitude {I A Z : Type*}
    [Fintype I] [Fintype A] [Fintype Z]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (n r : ℕ)
    (e : Fin r ≃ CurrentPivotConstituent role n) (hist : A → FrequencyTree ℤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : Fin r → Finset ℕ) (S : Finset (Fin r → P))
    (L : A → CopyScheduleH role n → ℕ) (U : Z → CopyScheduleY role n → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ z y, Fact (U z y).Prime]
    (center : ∀ p : ℕ, ZMod p) (W : Z → ℕ → A → ℂ) (μ : Z → ℝ) : ℂ :=
  ∑ z, (μ z : ℂ) * ∑ x ∈ S, (productPrior (fun i => primeSubsetPrior P (Q i)) x : ℂ) *
    ∑ a, W z (∏ i, (x i : ℕ)) a *
      sampledScheduledPhase role χ κ pivot n r e (hist a) P hP x (L a) (U z) center

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeGuardedAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full constituent-prime guard in arithmetic amplitude coordinates -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def primeGuardedCurrentAmplitude {I A Z : Type*}
    [Fintype I] [Fintype A] [Fintype Z]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (n r : ℕ)
    (e : Fin r ≃ CurrentPivotConstituent role n) (hist : A → FrequencyTree ℤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : Fin r → Finset ℕ)
    (L : A → CopyScheduleH role n → ℕ) (U : Z → CopyScheduleY role n → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ z y, Fact (U z y).Prime]
    (center : ∀ p : ℕ, ZMod p) (W : Z → ℕ → A → ℂ) (μ : Z → ℝ) : ℂ :=
  ∑ z, (μ z : ℂ) * ∑ x : Fin r → P,
    (productPrior (fun i => primeSubsetPrior P (Q i)) x : ℂ) *
    ∑ a, if Pairwise (fun i j =>
        (Sum.elim (fun k => (x k : ℕ)) (Sum.elim (L a) (U z)) i).Coprime
          (Sum.elim (fun k => (x k : ℕ)) (Sum.elim (L a) (U z)) j)) then
      W z (∏ i, (x i : ℕ)) a *
        sampledScheduledPhase role χ κ pivot n r e (hist a) P hP x (L a) (U z) center
    else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledCopiedAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The reconstructed off-diagonal on the actual next schedule -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

/-- The two old frequency histories become the two children of the new root.
Only the forced positive integer pivot is inserted into the inherited weights. -/
noncomputable def scheduledNextAmplitude {I A : Type*} [Fintype I] [Fintype A]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (g : I → I → ℤ) (pivot : ℕ → I) (initial : I → ℤ → ℕ → ℂ)
    (n : ℕ) (hist : A → FrequencyTree ℤ n)
    (L : A → CopyScheduleH role n → ℕ) (U : CopyScheduleY role n → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ y, Fact (U y).Prime]
    (center : ∀ p : ℕ, ZMod p) (W : ℕ → A → ℂ) (T : Finset ℕ) (V : ℕ) : ℂ :=
  ∑ s ∈ transferFrequencyRange V, ∑ a, ∑ a',
    let N := frequencyRoot n (hist a) * (∏ h, L a' h) -
      frequencyRoot n (hist a') * (∏ h, L a h)
    let M := reconstructedPivot N s
    if validTransferredPivot T N s then
      letI := transferredPrimeFact (L a) (L a') U
      W M a * conj (W M a') *
        scheduledPrimePhase role χ g pivot initial (n + 1) (s, hist a, hist a')
          (fun j => transferredLabels (L a) (L a') U (copyScheduleSurvivorEquiv role n j)) center
    else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledFrequencyHistory
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite frequency histories with the actual cutoff at every level -/

namespace Ostmann

open scoped Classical

theorem scheduledFrequencyHistory_root_bound (V : ℕ → ℕ) (n : ℕ)
    (a : ScheduledFrequencyIndex V n) :
    (frequencyRoot n (scheduledFrequencyHistory V n a)).natAbs ≤ V n := by
  cases n with
  | zero => exact (mem_transferFrequencyRange _ _).mp a.property
  | succ n => exact (mem_transferFrequencyRange _ _).mp a.1.property

/-- The largest level cutoff controls every actual child frequency. -/
theorem scheduledFrequencyHistory_all_bound (V : ℕ → ℕ) (hV : Monotone V) (n : ℕ)
    (a : ScheduledFrequencyIndex V n) (s : ℤ)
    (hs : s ∈ allFrequencyList n (scheduledFrequencyHistory V n a)) : s.natAbs ≤ V n := by
  induction n with
  | zero =>
    have he : s = a.val := by simpa only [allFrequencyList, scheduledFrequencyHistory, List.mem_singleton] using hs
    subst s
    exact scheduledFrequencyHistory_root_bound V 0 a
  | succ n ih =>
    rcases List.mem_cons.mp hs with he | hc
    · subst s
      exact scheduledFrequencyHistory_root_bound V (n + 1) a
    · rcases List.mem_append.mp hc with hL | hR
      · exact (ih a.2.1 hL).trans (hV (Nat.le_succ n))
      · exact (ih a.2.2 hR).trans (hV (Nat.le_succ n))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledHistoryEmbedding
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Embedding the actual varying-cutoff histories without adding bottom frequencies -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def scheduledHistoryEmbedding (V : ℕ → ℕ) (hV : Monotone V) (n : ℕ) :
    NonzeroScheduledHistory V n ↪ FrequencyTree ((transferFrequencyRange (V n)).erase 0) n where
  toFun a := frequencyTreeInFinset _ n (scheduledFrequencyHistory V n a.val) (by
    intro s hs
    exact Finset.mem_erase.mpr ⟨a.property s hs,
      (mem_transferFrequencyRange _ _).mpr (scheduledFrequencyHistory_all_bound V hV n a.val s hs)⟩)
  inj' := by
    intro a b h
    apply Subtype.ext
    apply scheduledFrequencyHistory_injective V n
    have hh := congrArg (frequencyTreeMap Subtype.val n) h
    simpa only [frequencyTreeInFinset_map] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PairedScheduledHistory
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two original scheduled histories as one paired frequency tree -/

namespace Ostmann
open scoped Classical BigOperators

theorem pairFrequencyTrees_projections (S : Finset ℤ) (n : ℕ)
    (t : FrequencyTree (S × S) n) :
    pairFrequencyTrees S n (frequencyPairProjection S n false t)
      (frequencyPairProjection S n true t) = t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (t.1,
      pairFrequencyTrees S n (frequencyPairProjection S n false t.2.1)
        (frequencyPairProjection S n true t.2.1),
      pairFrequencyTrees S n (frequencyPairProjection S n false t.2.2)
        (frequencyPairProjection S n true t.2.2)) = t
    rw [ih, ih]
    rcases t with ⟨a, b, c⟩
    rfl

/-- No multiplicity is lost when the two independent descendant histories
are placed in the paired tree used by the arithmetic norm estimate. -/
def pairedFrequencyEquiv (S : Finset ℤ) (n : ℕ) :
    (FrequencyTree S n × FrequencyTree S n) ≃ FrequencyTree (S × S) n where
  toFun t := pairFrequencyTrees S n t.1 t.2
  invFun t := (frequencyPairProjection S n false t, frequencyPairProjection S n true t)
  left_inv t := by simp only [frequencyPairProjection_pair, Bool.false_eq_true, ite_false, if_false, ite_true, if_true]
  right_inv := pairFrequencyTrees_projections S n

noncomputable def pairedScheduledHistoryEmbedding (V : ℕ → ℕ) (hV : Monotone V) (n : ℕ) :
    (NonzeroScheduledHistory V n × NonzeroScheduledHistory V n) ↪
      FrequencyTree (((transferFrequencyRange (V n)).erase 0) ×
        ((transferFrequencyRange (V n)).erase 0)) n :=
  (Function.Embedding.prodMap (scheduledHistoryEmbedding V hV n) (scheduledHistoryEmbedding V hV n)).trans
    (pairedFrequencyEquiv ((transferFrequencyRange (V n)).erase 0) n).toEmbedding

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledSourceScheme
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped BigOperators Classical

section
variable {I B : Type*} [Fintype I]
variable (role : I → CopyScheduleRole) (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
variable (left right : (j : Fin (2 ^ n - 1)) →
  CopyScheduleH role (n - ((preorderNodePath n j).length + 1)) →
    B ⊕ Fin (preorderNodePath n j).length)
variable (C : B → ℤ)

/-- Every ancestor is a genuine proper prefix of this node. The source
products are constructed from H slots, rather than assumed coefficients. -/
noncomputable def scheduledSourceScheme : PivotDependencyScheme (2 ^ n - 1) where
  frequencies j := singleTreeNodeFrequencies S n t j.val
  depth j := (preorderNodePath n j).length
  fixedLeft j := atomFixedProduct (left j) C
  fixedRight j := atomFixedProduct (right j) C
  ancestorsLeft j := (atomAncestorSet (left j)).image (ancestorNodeIndex n j)
  ancestorsRight j := (atomAncestorSet (right j)).image (ancestorNodeIndex n j)
  earlierLeft j i hi := by
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hi
    exact ancestorNodeIndex_earlier n j a
  earlierRight j i hi := by
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hi
    exact ancestorNodeIndex_earlier n j a

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledNodeSources
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete ancestor-source environments at every scheduled tree node -/

namespace Ostmann
open scoped Classical

theorem scheduledNodeLevel_add_depth (n : ℕ) (j : Fin (2 ^ n - 1)) :
    scheduledNodeLevel n j + 1 + (preorderNodePath n j).length = n := by
  have h := preorderNodePath_length n j
  dsimp only [scheduledNodeLevel]
  omega

noncomputable def scheduledNodeRootEquiv {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (j : Fin (2 ^ n - 1)) :
    CopyScheduleAtoms role (scheduledNodeLevel n j + 1 + (preorderNodePath n j).length) ≃
      CopyScheduleAtoms role n :=
  Equiv.cast (congrArg (CopyScheduleAtoms role) (scheduledNodeLevel_add_depth n j))

noncomputable def scheduledRawNodeSources {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (j : Fin (2 ^ n - 1)) :
    CopyScheduleAtoms role (scheduledNodeLevel n j + 1) → CopyScheduleAtoms role n ⊕ ℕ :=
  descendAtomSources role (preorderNodePath n j).length (scheduledNodeLevel n j + 1) 0
    (scheduledReversePath n j) (fun v => .inl (scheduledNodeRootEquiv role n j v))

theorem scheduledRawNodeSources_before {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (j : Fin (2 ^ n - 1)) :
    ∀ v, AtomSourceBefore (preorderNodePath n j).length (scheduledRawNodeSources role n j v) := by
  simpa only [Nat.zero_add, scheduledRawNodeSources] using descendAtomSources_before role (preorderNodePath n j).length
    (scheduledNodeLevel n j + 1) 0 (scheduledReversePath n j)
    (fun v => Sum.inl (scheduledNodeRootEquiv role n j v)) (fun _ => True.intro)

noncomputable def scheduledNodeSources {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (j : Fin (2 ^ n - 1)) :
    CopyScheduleAtoms role (scheduledNodeLevel n j + 1) →
      CopyScheduleAtoms role n ⊕ Fin (preorderNodePath n j).length :=
  boundAtomSources _ _ (scheduledRawNodeSources_before role n j)

noncomputable def scheduledNodeHSources {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (j : Fin (2 ^ n - 1)) :
    CopyScheduleH role (scheduledNodeLevel n j) →
      CopyScheduleAtoms role n ⊕ Fin (preorderNodePath n j).length :=
  fun h => scheduledNodeSources role n j ⟨.inl (b, h.val), h.property⟩

/-- In v H_R - w H_L, the left coefficient is the right H source product. -/
noncomputable def scheduledActualSourceScheme {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (C : CopyScheduleAtoms role n → ℤ) : PivotDependencyScheme (2 ^ n - 1) :=
  scheduledSourceScheme role S n t
    (scheduledNodeHSources role n false) (scheduledNodeHSources role n true) C

noncomputable def scheduledNodeValues {I A : Type*} [Zero A] (role : I → CopyScheduleRole)
    (n : ℕ) (j : Fin (2 ^ n - 1))
    (C : CopyScheduleAtoms role n → A) (p : Fin (2 ^ n - 1) → A) :
    CopyScheduleAtoms role (scheduledNodeLevel n j + 1) → A :=
  descendAtomValues role (preorderNodePath n j).length (scheduledNodeLevel n j + 1) 0
    (scheduledReversePath n j) (nodeAncestorValues n j p)
    (fun v => C (scheduledNodeRootEquiv role n j v))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampledRecursion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Expanding the sampled giant recursion into its literal histories

This is the recursion of Section 7.4 (7.10)--(7.11), rather than the
whole-atom recursion of Section 4. Each root sample is used by both children.
The child sample trees are independent under the original finite law.
-/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingSampleRootFactor {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ (n + 1)) (CL CR u : List σ) (XL XR : ℕ) : ℂ :=
  let x := movingRootState n t CL CR u XL XR
  let sys := movingSlotSystem value childBound pivotBound
  let v := frequencyRoot n t.2.1
  let w := frequencyRoot n t.2.2
  let P := historyPivot sys x t.1 v w
  if ValidTransferNode sys x t.1 v w P then
    (movingSlotCutoff value childBound pivotBound E x t.1 v w : ℂ) else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetHorizontalMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the surviving characters after horizontal density domination -/

namespace Ostmann

open scoped BigOperators

attribute [local instance] OAI.Ostmann.horizontalCharFintype
noncomputable def rationalCutCharacterSum {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool (n + 2))
    (B : TreeLeafIndex n → MulChar (ZMod p) ℂ → ZMod p → ℝ)
    (sign : TreeLeafIndex n → ℤ) (P : TreeLeafTuple (ZMod p)ˣ n) : ℝ := by
  classical
  exact ∑ ρ : TreeLeafIndex n → MulChar (ZMod p) ℂ,
    if (∏ i : TreeLeafIndex n, (ρ i) ^ sign i) = 1 then
      quartetCutValue (fun S (wp : (ZMod p → ℝ) × (ZMod p)ˣ) =>
        wp.1 (rationalQuartetStateArgument D S wp.2)) n
        (rationalQuartetStates n T XL XR c P)
        (treeLeafZip n ((treeLeafTupleEquiv _ n).symm (fun i => B i (ρ i))) P)
    else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetLocalBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The six possible moving-leaf pairs and their uniform local estimates -/

namespace Ostmann

open scoped BigOperators

noncomputable def quartetMovingLeaves {U : Type*} [CommGroup U]
    (choice : QuartetMovingCase) (P a b r : U) : TreeLeafTuple U 2 :=
  match choice with
  | .cross left right => crossQuartetLeaves left right P a b r
  | .leftPair => samePairLeftLeaves P a b r
  | .rightPair => samePairRightLeaves P a b r

noncomputable def quartetMovingMajorant {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (cL cR : Bool) (choice : QuartetMovingCase)
    (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) : ℝ :=
  match choice with
  | .cross left right =>
    8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 *
      crossPairMajorant (orientedPairBase (pairConjugate g cL) left)
        (orientedPairBase (pairConjugate g cR) right) left right ρ⁻¹ y
  | .leftPair => 8 * samePairMajorant (fieldPairCoefficientMoment (pairConjugate g cL))
      (fieldPairMoment (pairConjugate g cR)) ρ y
  | .rightPair => 8 * samePairMajorant (fieldPairCoefficientMoment (pairConjugate g cR))
      (fieldPairMoment (pairConjugate g cL)) ρ (-y)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetProductProjection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cycle projection of a product of actual quartet states -/

namespace Ostmann

open scoped BigOperators

attribute [local instance] OAI.Ostmann.quartetProjectionCharDecidableEq
noncomputable def quartetStateProduct {p : ℕ} [Fact p.Prime]
    {I : Type*} [Fintype I] (g : ZMod p → ℂ) (D : (ZMod p)ˣ)
    (S : I → RationalQuartetState p) (P : I → (ZMod p)ˣ) (choice : I → QuartetMovingCase)
    (h : I → (ZMod p)ˣ × (ZMod p)ˣ) (r : I → (ZMod p)ˣ) : ℂ :=
  ∏ i : I, rationalQuartetStateAmplitude g D (S i)
    (quartetMovingLeaves (choice i) (P i) (h i).1 (h i).2 (r i))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternBulkData
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original pattern pair in selected bulk coordinates -/

namespace Ostmann
open scoped Classical

def movingPatternFiniteSamples {B C : Type*} {N : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (n : ℕ) (pattern : Bool × MovingSampleIndex n → C) (side : Bool) :
    MovingSampleSlots (Fin (N + 1)) n :=
  movingPatternSamples (Fin (N + 1)) n ((fun c => e.symm (.inr c)) ∘ pattern) side

theorem movingPatternFinData_build {B C : Type*} {N : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C) (side : Bool) :
    movingPatternFinData e n t small bulk pattern side =
      buildMovingSlotData n (t side) (movingPatternFiniteSmall e n (small side))
        (movingPatternFiniteSmall e n (bulk side))
        (movingPatternFiniteSamples e n pattern side) := by
  unfold movingPatternFinData movingPatternSlotData
  rw [buildMovingSlotData_map, treeLeafMap_list_comp, treeLeafMap_list_comp,
    movingPatternSamples_map]
  rfl

noncomputable def movingPatternBulkLeaves {B : Type*} (n m : ℕ)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m)) (side : Bool) :
    TreeLeafTuple (List B) n :=
  if side then bulkSlotLeaves n m (slot ∘ perm.symm) else bulkSlotLeaves n m slot

noncomputable def movingPatternFinBulkData {B C : Type*} {N : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (n m : ℕ) (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C) (side : Bool) :
    MovingSlotData (Fin (N + 1)) n :=
  movingPatternFinData e n t small (movingPatternBulkLeaves n m slot perm) pattern side

theorem movingPatternFinBulkData_build {B C : Type*} {N : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (n m : ℕ) (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C) (side : Bool) :
    movingPatternFinBulkData e n m t small slot perm pattern side =
      buildMovingSlotData n (t side) (movingPatternFiniteSmall e n (small side))
        (if side then bulkSlotLeaves n m (movingPatternBulkEmbedding e slot ∘ perm.symm)
          else bulkSlotLeaves n m (movingPatternBulkEmbedding e slot))
        (movingPatternFiniteSamples e n pattern side) := by
  rw [movingPatternFinBulkData, movingPatternFinData_build]
  cases side <;>
    simp only [movingPatternFiniteSmall, movingPatternBulkLeaves, Bool.false_eq_true,
      ite_false, if_false, ite_true, if_true, bulkSlotLeaves_map]
  <;> rfl

theorem movingPatternFinBulkData_levels {B C : Type*} {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (n m : ℕ) (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (side : Bool) :
    (movingPatternFinBulkData e n m t small slot perm pattern side).Levels
      ((Sum.elim tierB tierC) ∘ e) :=
  movingPatternFinData_levels e tierB tierC n t small _ pattern
    (fun _ i _ => hB i) (fun _ i _ => hB i) htier side

theorem movingPatternFinBulkData_compensationAbsent {B C : Type*} {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (n m : ℕ) (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (side : Bool) (j : TreeLeafIndex n × Fin m) :
    (movingPatternFinBulkData e n m t small slot perm pattern side).CompensationAbsent
      (movingPatternBulkEmbedding e slot j) := by
  apply MovingSlotData.compensationAbsent_of_levels ((Sum.elim tierB tierC) ∘ e) _
    (movingPatternFinBulkData_levels e tierB tierC n m t small slot perm pattern hB htier side)
  change n ≤ Sum.elim tierB tierC (e (e.symm (.inl (slot j))))
  simpa only [Equiv.apply_symm_apply, Sum.elim_inl] using hB (slot j)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSeparatedAverages
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit three-factor form of the original Page-weighted average -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingSpectatorHaarAverage {σ : Type*} (value : σ → ℕ)
    (q : ℕ) [Fact q.Prime] (g : ZMod q → ℂ) (D : Bool → (ZMod q)ˣ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) : ℂ :=
  (Fintype.card (ZMod q × (ZMod q)ˣ) : ℂ)⁻¹ *
    ∑ z : ZMod q × (ZMod q)ˣ, movingSpectatorPairFactor value q g D T z.1 z.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternBulkMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lifting signed cancellation in the original bulk mean -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingPatternBulkMean {A B C : Type*} [Fintype A] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (ν : B → A → ℝ)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (G : (Fin (N + 1) → A) → ℂ)
    (x : Fin (N + 1) → A) : ℂ :=
  ∑ z : TreeLeafIndex n × Fin m → A, ((∏ j, ν (slot j) (z j) : ℝ) : ℂ) *
    G (joinBulkNonbulk (movingPatternBulkEmbedding e slot) z (fun i => x i))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternBulkBudgets
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete length and frequency budgets for the original pattern pair -/

namespace Ostmann
open scoped Classical

theorem movingPatternFinBulkData_follows {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C) (b : Bool) :
    (movingPatternFinBulkData e n m t small slot perm pattern b).Follows (t b) := by
  rw [movingPatternFinBulkData_build]
  exact buildMovingSlotData_follows _ _ _ _ _

/-- Frequency bounds are taken from the original histories, not from an
additional assumption on each pattern realization. -/
theorem movingPatternFinBulkData_frequencies {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C) (P : ℤ → Prop)
    (hP : ∀ b, ∀ s ∈ allFrequencyList n (t b), P s) (b : Bool) :
    (movingPatternFinBulkData e n m t small slot perm pattern b).Frequencies P :=
  ((movingPatternFinBulkData_follows e t small slot perm pattern b).frequencies_iff P).mpr (hP b)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternBulkLog
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The real bulk coordinates evaluate to the original pattern primes -/

namespace Ostmann
open scoped Classical

theorem movingPatternBulkSet_compensationAbsent {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2) :
    ∀ b i, i ∈ selectedBulkSet (movingPatternBulkEmbedding e slot) →
      (movingPatternFinBulkData e n m t small slot perm pattern b).CompensationAbsent i := by
  intro b i hi
  obtain ⟨j, rfl⟩ := (mem_selectedBulkSet _ _).mp hi
  exact movingPatternFinBulkData_compensationAbsent e tierB tierC n m t small slot perm pattern hB htier b j

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternRegularSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Support and arithmetic of the original regular-prime list -/

namespace Ostmann
open scoped Classical BigOperators

/-- The common top list, before its primes are drawn. -/
noncomputable def movingPatternRegularSlots {B C : Type*} {N : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (n m : ℕ) (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B) :
    List (Fin (N + 1)) :=
  flattenMovingSlots n (movingPatternFiniteSmall e n small) ++
    flattenMovingSlots n (bulkSlotLeaves n m (movingPatternBulkEmbedding e slot))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOriginalDiagonalPatterns
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original diagonal mean in the arithmetic pattern coordinates -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingPatternRegularSlots_eq_map {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (small : TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) :
    movingPatternRegularSlots e n m small slot =
      (flattenMovingSlots n small ++ flattenMovingSlots n (bulkSlotLeaves n m slot)).map
        (fun b => e.symm (.inl b)) := by
  unfold movingPatternRegularSlots movingPatternFiniteSmall
  change _ ++ flattenMovingSlots n
    (bulkSlotLeaves n m ((fun b => e.symm (.inl b)) ∘ slot)) = _
  rw [← bulkSlotLeaves_map, flattenMovingSlots_map, flattenMovingSlots_map, List.map_append]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PhaseGiantTest
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Fourier-phase giant and its real physical inverse -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def phaseGiantPhysical {p : ℕ} [NeZero p]
    (g : ZMod p → ℂ) : ZMod p → ℂ :=
  densityFourierInverse (fun b => complexUnitPhase (g b))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_PrimeDivisorEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The low-weight coefficient energy of the actual divisor sums -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap

noncomputable def primeDivisorQuadratic (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : ∀ p : ℕ, Finset (ZMod p)) (W : Finset ℕ → Finset ℕ)
    (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (R v : ℝ) (U : Finset ℕ) (s : ℕ) : ℂ := by
  classical
  exact if hU : U ⊆ P then
    primeSetQuadraticSum U (fun p hp => hP p (hU hp)) S (W U) (a U) (θ U) Φ R v s
  else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_NormalizedResidueFamily
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single family of normalized transforms for varying sampled primes -/

namespace Ostmann
open scoped Classical BigOperators

/-- The zero modulus is unused by prime samples. This total definition lets
both histories evaluate the same transform at their actual sampled prime. -/
noncomputable def normalizedResidueFamily (sets : ∀ q : ℕ, Finset (ZMod q))
    (q : ℕ) : ZMod q → ℂ :=
  if h : q = 0 then fun _ => 0 else
    letI : NeZero q := ⟨h⟩
    normalizedResidueTransform (sets q)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original prime amplitude on each restored regular template -/

namespace Ostmann
open scoped Classical BigOperators

/-- The finite prime amplitude, with both giants and every regular slot
sampled from their original laws. The root frequency is not renormalized. -/
noncomputable def movingTemplatePrimeAmplitude {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (Pg : Finset ℕ) (ρ : Pg → ℝ) (ν : MovingRegularSlot n r m → σ → ℝ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) : ℂ :=
  ∑ XL : Pg, (ρ XL : ℂ) * ∑ XR : Pg, (ρ XR : ℂ) *
    ∑ s : transferFrequencyRange (V n),
      ∑ y : MovingRegularSlot n r m → σ, ((∏ i, ν i (y i) : ℝ) : ℂ) *
        (movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n r m
          s.val y XL XR *
          movingTaggedTransform
            (Sum.elim (fun b : Bool => if b then (XL : ℕ) else (XR : ℕ)) (value ∘ y))
            (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod s.val)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimePhysicalTest
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact physical tests for the two kinds of prime position -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- A giant uses the Fourier phase on favorable primes and zero elsewhere;
every other prime position uses the exact normalized residue indicator. -/
noncomputable def primePhysicalTest {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (giant favorable : Bool) : ZMod p → ℂ :=
  if giant then
    if favorable then phaseGiantPhysical (normalizedResidueTransform S) else fun _ => 0
  else normalizedResidueIndicator S

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RegularInitialAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original initial Fourier amplitude and repeated-prime error -/

namespace Ostmann
open scoped Classical BigOperators FourierTransform SchwartzMap

noncomputable def regularInitialAmplitude {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (μ : Fin n → P → ℝ)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (N : ℕ) (w : (Fin n → P) → ℂ) : ℂ :=
  ∑ x : Fin n → P, (productPrior μ x : ℂ) * w x *
    if Function.Injective x then primeTupleFourierCoefficient P F ψ X N x else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSymmetrizedMaskedKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The restored multiplier of the actual bulk-averaged coefficient -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingSymmetrizedMaskedTemplateKernel
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ)
    (x : MovingRegularSlot n (4 + r) m → P) (p X : ℕ) (s : ℤ) : ℝ :=
  let q := fun i => (x i : ℕ)
  let _ : ∀ i, Fact (q i).Prime := fun i => ⟨hP _ (x i).property⟩
  ‖movingBulkAveragedTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
      n (4 + r) m s x p X‖ ^ 2 *
    naturalRegularMultiplier q (movingRestoredActive n r m) s
      (fun i => ((outside.prod * tupleCofactor q i : ℕ) : ZMod (q i)))
      (fun i => greg (q i)) p X

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSymmetrizedMaskedEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bulk-averaged masked energy under the original restored prior -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingSymmetrizedMaskedTemplateEnergy
    (P Pg I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (Q : MovingRegularSlot n r m → Finset ℕ) (greg : ∀ q : ℕ, ZMod q → ℂ)
    (weight : (MovingRegularSlot n (4 + r) m → P) → ℝ) : ℝ :=
  ∑ x : MovingRegularSlot n (4 + r) m → P,
    (∏ i, movingTemplateRestoredPrior n r m (μ n) (fun i => primeSubsetPrior P (Q i)) i (x i)) *
      (weight x * ∑ p ∈ I, φ (Real.log p - G (n + 1)) *
        ∑ X : Pg, smoothGiantPrior Pg φ (G (n + 1)) X *
          ∑ s : transferFrequencyRange (V n),
            movingSymmetrizedMaskedTemplateKernel P hP outside μ childBound pivotBound V F φ G n r m
              greg x p X s.val)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternTemplateEnumeration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying arithmetic pattern slots with the full regular template -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPatternTemplateSlots_eq {C : Type*} {N : ℕ} (n r m : ℕ)
    (e : Fin (N + 1) ≃ MovingRegularSlot n r m ⊕ C) :
    movingPatternRegularSlots e n m (movingTemplateSmall n r m) (movingTemplateBulk n r m) =
      (movingTemplateSlotList n r m).map (fun b => e.symm (.inl b)) := by
  exact movingPatternRegularSlots_eq_map e _ _

noncomputable def movingPatternTemplateEquiv {C : Type*} {N : ℕ} (n r m : ℕ)
    (e : Fin (N + 1) ≃ MovingRegularSlot n r m ⊕ C) :
    Fin (movingPatternRegularSlots e n m (movingTemplateSmall n r m)
      (movingTemplateBulk n r m)).length ≃ MovingRegularSlot n r m :=
  (finCongr (by rw [movingPatternTemplateSlots_eq, List.length_map])).trans
    (movingTemplateListEquiv n r m)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingWeightedDiagonalRelabel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relabeling the retained exterior multiplier into arithmetic coordinates -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def movingPatternExternalMultiplier {J : Type*} [Fintype J] {N : ℕ}
    (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
    (reg : J → Fin (N + 1)) (active : J → Bool)
    (other : (Fin (N + 1) → primes) → J → ℤ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (sreg : ℤ) (φ : ℝ → ℝ)
    (Jleft Jright : ℝ) (diagonal : Bool) (x : Fin (N + 1) → primes) (z y : ℝ) : ℂ :=
  let q := fun j => (x (reg j) : ℕ)
  let _ : ∀ j, Fact (q j).Prime := fun j => ⟨hprimes _ (x (reg j)).property⟩
  (giantOuterWeight φ Jleft Jright diagonal ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ : ℂ) *
    (naturalRegularMultiplier q active sreg (fun j => (other x j : ZMod (q j)))
      (fun j => greg (q j)) ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ : ℝ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateExternalMultiplier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original exterior multiplier in template and pattern coordinates -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def movingTemplateExternalMultiplier
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n r m : ℕ)
    (active : MovingRegularSlot n r m → Bool) (outside : List ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (s : ℤ) (φ : ℝ → ℝ)
    (Jleft Jright : ℝ) (diagonal : Bool)
    (x : MovingRegularSlot n r m → P) (z y : ℝ) : ℂ :=
  let q := fun i => (x i : ℕ)
  let _ : ∀ i, Fact (q i).Prime := fun i => ⟨hP _ (x i).property⟩
  (giantOuterWeight φ Jleft Jright diagonal ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ : ℂ) *
    (naturalRegularMultiplier q active s
      (fun i => ((outside.prod * tupleCofactor q i : ℕ) : ZMod (q i)))
      (fun i => greg (q i)) ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ : ℝ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingNormalizedSymmetrizedEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact normalization of the original bulk-averaged masked energy -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingTemplateMaskedSymmetrizedEnergy
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (ν : MovingRegularSlot n r m → P → ℝ) (active : MovingRegularSlot n r m → Bool)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (Jleft Jright : ℝ) (diagonal : Bool)
    (u v a b center : ℝ) : ℂ :=
  mixedExternalAverage ν (V n) u v a b center (fun s y x z =>
    (‖movingBulkAveragedTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
      n r m s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊‖ ^ 2 : ℂ) *
      movingTemplateExternalMultiplier P hP n r m active outside greg s φ Jleft Jright diagonal y x z)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRestoredPrimeLaws
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original prime sets and tiers in restored coordinates -/

namespace Ostmann
open scoped Classical

noncomputable def movingRestoredPrimeSets (n r m : ℕ) (Qμ : Finset ℕ)
    (Qν : MovingRegularSlot n r m → Finset ℕ) : MovingRegularSlot n (4 + r) m → Finset ℕ :=
  fun i => Sum.elim (fun _ => Qμ) Qν ((movingReverseTemplate n r m).symm i)

noncomputable def movingRestoredTiers (n r m : ℕ)
    (tier : MovingRegularSlot n r m → ℕ) : MovingRegularSlot n (4 + r) m → ℕ :=
  fun i => Sum.elim (fun _ => n) tier ((movingReverseTemplate n r m).symm i)

@[simp] theorem movingRestoredPrimeSets_compensation (n r m : ℕ) (Qμ : Finset ℕ)
    (Qν : MovingRegularSlot n r m → Finset ℕ) (i : TreeLeafIndex n × Fin 4) :
    movingRestoredPrimeSets n r m Qμ Qν (movingReverseTemplate n r m (.inl i)) = Qμ := by
  simp only [movingRestoredPrimeSets, Equiv.symm_apply_apply, Sum.elim_inl]

@[simp] theorem movingRestoredPrimeSets_surviving (n r m : ℕ) (Qμ : Finset ℕ)
    (Qν : MovingRegularSlot n r m → Finset ℕ) (i : MovingRegularSlot n r m) :
    movingRestoredPrimeSets n r m Qμ Qν (movingReverseTemplate n r m (.inr i)) = Qν i := by
  simp only [movingRestoredPrimeSets, Equiv.symm_apply_apply, Sum.elim_inr]

@[simp] theorem movingRestoredPrimeSets_bulk (n r m : ℕ) (Qμ : Finset ℕ)
    (Qν : MovingRegularSlot n r m → Finset ℕ) (i : TreeLeafIndex n × Fin m) :
    movingRestoredPrimeSets n r m Qμ Qν (movingTemplateBulk n (4 + r) m i) =
      Qν (movingTemplateBulk n r m i) := by
  rw [← movingReverseTemplate_bulk, movingRestoredPrimeSets_surviving]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRestoredTierSeparation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restoration preserves the terminal-tier separation -/

namespace Ostmann
open scoped Classical

@[simp] theorem movingRestoredTiers_compensation (n r m : ℕ)
    (tier : MovingRegularSlot n r m → ℕ) (i : TreeLeafIndex n × Fin 4) :
    movingRestoredTiers n r m tier (movingReverseTemplate n r m (.inl i)) = n := by
  simp only [movingRestoredTiers, Equiv.symm_apply_apply, Sum.elim_inl]

@[simp] theorem movingRestoredTiers_surviving (n r m : ℕ)
    (tier : MovingRegularSlot n r m → ℕ) (i : MovingRegularSlot n r m) :
    movingRestoredTiers n r m tier (movingReverseTemplate n r m (.inr i)) = tier i := by
  simp only [movingRestoredTiers, Equiv.symm_apply_apply, Sum.elim_inr]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplatePrimeStatistic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prime statistic for the actual data-dependent template leaf -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingTemplatePrimeStatistic
    (P : Finset ℕ) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (ν : MovingRegularSlot n r m → P → ℝ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (H : ℝ) (u v a b : ℝ) : ℂ :=
  primeExternalAverage ν (V n) u v a b (fun s y x z =>
    ((movingGiantPhase Subtype.val outside (movingTemplateSmall n r m)
        (bulkSlotLeaves n m (movingTemplateBulk n r m)) ggiant favorable s y x z *
      movingExternalRegularFactor Subtype.val outside (movingTemplateSmall n r m)
        (bulkSlotLeaves n m (movingTemplateBulk n r m)) greg s y x z) *
      movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
        n r m s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊) *
      giantOuterWeight φ H H false ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledArithmeticIteration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Iterating the literal original-prior arithmetic amplitudes -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def scheduledConstituentAmplitude {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (lo hi : I → ℕ) (V pivotBound : ℕ → ℕ)
    (leaf : ScheduleAtomState role → ℤ → ℂ) (center : ∀ p : ℕ, ZMod p) (j : ℕ) : ℂ :=
  constituentPrimeGuardedAmplitude role size χ κ pivot j P hP Q V pivotBound
    (atomIntervalRanges role lo hi) leaf (scheduledFrequencyHistory V j) center

noncomputable def scheduledConstituentDiagonal {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (lo hi : I → ℕ) (V pivotBound : ℕ → ℕ)
    (leaf : ScheduleAtomState role → ℤ → ℂ) (center : ∀ p : ℕ, ZMod p)
    (p : I) (j : ℕ) : ℝ :=
  ∑ u, (∏ y, primeSubsetPrior P (Q (copyScheduleOrigin j y.val)) (u y)) *
    ∑ M ∈ Finset.Icc (lo p) (hi p),
      (constituentPivotDiagonal role size χ κ pivot j P hP Q V pivotBound
        (atomIntervalRanges role lo hi) leaf (scheduledFrequencyHistory V j) center u M).re

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledMatchedEdges
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The anchor interaction in the literal retained matching graph -/

namespace Ostmann
open scoped Classical

noncomputable def scheduledMatchedGraph {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n : ℕ) (e : Equiv.Perm (CopyScheduleH role n)) :
    (CopyScheduleH role n ⊕ CopyScheduleY role n) →
      (CopyScheduleH role n ⊕ CopyScheduleY role n) → ℤ :=
  let g := retainedInternalGraph (scheduledRetainedGraph role initialCompleteGraph pivot n)
  graphDifference g (transportGraph (Equiv.sumCongr e (Equiv.refl _)) g)

noncomputable def scheduledPastAnchor {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (a : I) (j : Fin (n + 1)) (ha : role a = .anchor j) (b : Bool) :
    CopyScheduleY role (n + 1) :=
  ⟨copyScheduleAnchor (n + 1) j b a,
    copyScheduleSurvives_anchor role a j ha (n + 1) j.isLt b, by
      rw [copyScheduleRole_anchor role a j ha (n + 1) j.isLt b]
      exact ⟨rfl, rfl⟩⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledSampleQuotient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal full scheduled phase quotient at a common root -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate

noncomputable def scheduledSurvivorUnary {I : Type*}
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (n : ℕ) (t : FrequencyTree ℤ n)
    (i : CopyScheduleAtoms role n) (p : ℕ) : ℂ :=
  copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t i.val p

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterNonbulkBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual character top, pivot and anchor normalizers fit the cell budget -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def selectedNonbulkCost {I : Type*} [Fintype I]
    (ρ : I → CopyScheduleRole) (n m : ℕ) (bulk : Fin m ↪ I)
    (hbulk : ∀ i, ρ (bulk i) = .word) (mass : CopyScheduleH ρ n → ℝ) : ℝ :=
  (Fintype.card (SelectedNonbulkH ρ n m bulk hbulk)).factorial *
    ∏ h : SelectedNonbulkH ρ n m bulk hbulk, (mass h.val)⁻¹

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledLeafProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two sampled prime products at each actual scheduled node -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def scheduledNodeLeafValues {G : Type*} (n : ℕ) (j : Fin (2 ^ n - 1))
    (x : TreeLeafIndex n → G) : TreeLeafIndex (scheduledNodeLevel n j + 1) → G :=
  descendLeafValues (preorderNodePath n j).length (scheduledNodeLevel n j + 1)
    (scheduledReversePath n j)
    (fun v => x (Equiv.cast (congrArg TreeLeafIndex (scheduledNodeLevel_add_depth n j)) v))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledRootIndex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The root frequency as an element of its actual finite cutoff range -/

namespace Ostmann

noncomputable def scheduledRootIndex (V : ℕ → ℕ) (n : ℕ)
    (d : ScheduledFrequencyIndex V n) : transferFrequencyRange (V n) :=
  ⟨frequencyRoot n (scheduledFrequencyHistory V n d),
    (mem_transferFrequencyRange _ _).mpr (scheduledFrequencyHistory_root_bound V n d)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparsePolydiscBlocks
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform side and lower bounds on the complex parameter polydisc -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def polydiscSparseLower {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (c d : ℂ) (f : ZMod p → ℂ) (x : ZMod p) : ℂ :=
  c * residueKernelLower S T (localSparseKernel E) f x +
    d * residueKernelLower S T (localSparseSquare E) f x

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseTensorKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual sparse tensor kernel of Section 5.3 -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def sparseTensorKernel {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (u v : ℂ) :
    (∀ i, Option (ZMod (p i))) → (∀ i, Option (ZMod (p i))) → ℂ :=
  finiteTensorKernel (fun i => sparseResidueMatrix (S i)
    (largeTransformSpectrum (normalizedResidueTransform (S i))) u v)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseTensorPolynomial
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete coefficients of the sparse tensor polynomial -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def sparseTensorCoefficient {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (j k : ℕ) :
    (∀ i, Option (ZMod (p i))) → (∀ i, Option (ZMod (p i))) → ℂ :=
  cubeCoefficient (fun t => fun x y => ∏ i, localSparseCoefficient (S i)
    (largeTransformSpectrum (normalizedResidueTransform (S i))) (t i) (x i) (y i)) j k

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseTensorModes
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Only low centered modes survive the rectangular truncation -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def truncatedSparseTensorKernel {n : ℕ}
    (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ) :=
  rectangularPolynomialSum (sparseTensorCoefficient p S) (n + 1) K

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TensorUnitPolynomial
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Truncating the independent unit-residue mean -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def tensorUnitCoefficient {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (E : ∀ i, Finset (ZMod (p i))) (j k : ℕ) : ℂ :=
  tensorUnitMean p (fun x =>
    elementaryCoefficient (fun i => localSparseKernel (E i) (x i)) j *
      elementaryCoefficient (fun i => localSparseKernel (E i) (x i)) k)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_NonnegativeSparseWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The real nonnegative weight represented by the truncated tensor -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def sparseSubsetWeight {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ) (x : ∀ i, ZMod (p i)) : ℝ :=
  ‖elementaryTruncation (fun i => localSparseKernel
    (largeTransformSpectrum (normalizedResidueTransform (S i))) (x i)) K‖ ^ 2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseWeightPairAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sparse weight average over two actual finite summand sets -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def sparseWeightPairAverage {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ) {ι κ : Type*}
    (A : Finset ι) (B : Finset κ) (a : ι → ∀ i, ZMod (p i)) (b : κ → ∀ i, ZMod (p i)) : ℝ :=
  (A.card : ℝ)⁻¹ * (B.card : ℝ)⁻¹ * ∑ x ∈ A, ∑ y ∈ B,
    sparseSubsetWeight p S K (fun i => a x i - b y i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailFourierMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One total Fourier-mass function for the actual tail masks -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def tailFourierMass (A : Set ℕ) (N p : ℕ) : ℝ :=
  if h : p = 0 then 0 else
    letI : NeZero p := ⟨h⟩
    (p : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (tailDensityMask A N p) b‖

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_OffWitnessFamily
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed subfamily in which all small-kernel witnesses fail -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

noncomputable def offWitnessParameters (T : ℝ) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : ∀ p : ℕ, Finset (ZMod p))
    (Φ : 𝓢(ℝ, ℂ)) (S : Finset ℕ) : Finset QuadraticFamilyIndex := by
  classical
  exact (smallKernelParameters T Q.toList.prod).filter (fun i =>
    ∀ s ∈ S, ∀ V ∈ Q.powerset, ∀ U ∈ Q.powerset,
      ‖fixedPrimeDivisorTerm T Q hQ D Φ i V U s‖ ≤
        Real.exp (-9 * Q.card / 10) * (Real.sqrt 2) ^ U.card)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_DivisorFrequencyExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original density Fourier frequencies as divisor quadratic sums -/

namespace Ostmann

open scoped BigOperators SchwartzMap

noncomputable def primeDivisorFrequency (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (U : Finset ℕ) (M N h₀ : ℕ)
    (θ R : ℝ) (Φ : 𝓢(ℝ, ℂ)) : ℂ := by
  classical
  exact if hU : U ⊆ Q then
    let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _
      (primeSet_list_prime U (fun p hp => hQ p (hU hp)))).ne'⟩
    (Real.sqrt (R * U.toList.prod) : ℂ)⁻¹ *
      ∑ u ∈ Finset.Icc 1 N, (realJacobi u M : ℂ) *
        quadraticFrequencyTerm (densityFourier (densityCRTList U.toList
          (primeSet_list_prime U (fun p hp => hQ p (hU hp)))
          (primeSet_list_coprime U (fun p hp => hQ p (hU hp))) D).value)
          (quadraticInverseResidue M U) ((h₀ : ℝ) + θ) Φ R u
  else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalFourierCoefficients
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive Fourier expression is the actual arithmetic statistic -/

namespace Ostmann

open scoped BigOperators SchwartzMap

noncomputable def originalPositiveFourier (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M N h₀ : ℕ) (θ R : ℝ) (Φ : 𝓢(ℝ, ℂ)) : ℂ :=
  ∑ U ∈ Q.powerset, quadraticSymbolCoefficient M U *
    primeDivisorFrequency Q hQ D U M N h₀ θ R Φ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalKernelDecomposition
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the principal small kernels in the original Fourier statistic -/

namespace Ostmann

open scoped BigOperators SchwartzMap Classical

noncomputable def principalSmallFourier (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M N h₀ : ℕ) (θ R : ℝ) (Φ : 𝓢(ℝ, ℂ)) : ℂ :=
  quadraticArrayStatistic (smallSquarefreeKernels Q.toList.prod N) M
    (arithmeticQuadraticCoefficient Q hQ D Φ R 1 M h₀ θ)

noncomputable def principalLargeFourier (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M N h₀ : ℕ) (θ R : ℝ) (Φ : 𝓢(ℝ, ℂ)) : ℂ :=
  quadraticArrayStatistic (largeSquarefreeKernels Q.toList.prod N) M
    (arithmeticQuadraticCoefficient Q hQ D Φ R 1 M h₀ θ)

noncomputable def outerFourierRemainder (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M N h₀ : ℕ) (θ R : ℝ) (Φ : 𝓢(ℝ, ℂ)) : ℂ :=
  ∑ P ∈ M.divisors.erase 1, (ArithmeticFunction.moebius P : ℂ) *
    quadraticArrayStatistic (squarefreeKernelSupport Q.toList.prod N) M
      (arithmeticQuadraticCoefficient Q hQ D Φ R P M h₀ θ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalOffWitnessMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original small-kernel statistic on the event with no witness -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap Classical

noncomputable def principalSmallWitness (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M N h₀ : ℕ) (θ R : ℝ) (Φ : 𝓢(ℝ, ℂ)) : Prop :=
  ∃ s ∈ smallSquarefreeKernels Q.toList.prod N, ∃ V ∈ Q.powerset, ∃ U ∈ Q.powerset,
    Real.exp (-(Q.card : ℝ)) * (Real.sqrt 2) ^ U.card <
      ‖primeDivisorPositive Q hQ D (divisorQuadraticScalar (quadraticInverseResidue M) V)
        (fun _ => (h₀ : ℝ) + θ) Φ R V.toList.prod U s‖

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalSignedFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive half of the original signed Fourier expression -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap

noncomputable def primeDivisorSignedFrequency (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (U : Finset ℕ) (M h₀ : ℕ)
    (θ R : ℝ) (Φ : 𝓢(ℝ, ℂ)) : ℂ :=
  if hU : U ⊆ Q then
    let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _
      (primeSet_list_prime U (fun p hp => hQ p (hU hp)))).ne'⟩
    (Real.sqrt (R * U.toList.prod) : ℂ)⁻¹ * ∑' u : ℤ,
      integerQuadraticFrequency (densityFourier (primeDivisorDensity Q hQ D U))
        (quadraticInverseResidue M U) ((h₀ : ℝ) + θ) Φ R M u
  else 0

noncomputable def originalSignedFourier (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M h₀ : ℕ) (θ R : ℝ) (Φ : 𝓢(ℝ, ℂ)) : ℂ :=
  ∑ U ∈ Q.powerset, quadraticSymbolCoefficient M U *
    primeDivisorSignedFrequency Q hQ D U M h₀ θ R Φ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalPositiveFirstMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # First moment of the original positive-frequency statistic -/

namespace Ostmann

open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate
open Filter

noncomputable def originalPrimeProductStatistic (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (N : ℕ) (τ : ℕ → ℤ) (h₀ : ℕ → ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (M : ℕ) : ℝ :=
  ‖originalPositiveFourier Q hQ D M N (h₀ M) ((τ M : ℝ) / M) ((M : ℝ) / X) (𝓕 ψ)‖

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RetainedCharacterPrimeBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Signed prime mass for a retained primitive real character -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def zeroComparisonConstant (P : PublishedProgressionInput) : ℝ :=
  max 5 (1 + P.kappa⁻¹)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_SplitPrimeAfterExclusion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The split-prime bound after the explicit Page-family deletion -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def splitPrimeMassLower (P : PublishedProgressionInput)
    (H : PublishedRealZeroInput P) (A K C ε : ℝ) (Q₀ Q D Y : ℕ) (R s : ℝ) : ℝ :=
  (1 / (s - 1) - C -
    (2 * zeroComparisonConstant P * Real.log (4 * (Q₀ : ℝ)) +
      K * R ^ ε + H.errorConstant + A + 2)) / 2 -
    (Q : ℝ) ^ (-(s - 1) / 2) * (2 / (s - 1) + C) - (Y + Real.log D / Y)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AllCharacterDecorrelation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Combining quadratic and higher-order translated decorrelation -/
namespace Ostmann
open Filter
open scoped Classical BigOperators Topology

noncomputable def tailCharacterBias (A : Set ℕ) (N p : ℕ) : ℝ :=
  maximalQuadraticBias (tailSupport A N p) p + higherCharacterBias A N p

noncomputable def tailCharacterBandMass (A : Set ℕ) (N : ℕ) (α β L : ℝ) : ℝ :=
  ∑ p ∈ closedLogLogPrimeBand α β L, (p : ℝ)⁻¹ * tailCharacterBias A N p

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseCoefficientMajorant
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform coefficient bound for the truncated sparse weight -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def sparsePatternMellin {p : ℕ} [Fact p.Prime]
    (E : Finset (ZMod p)) (t : ℝ) (χ : MulChar (ZMod p) ℂ) : Bool × Bool → ℂ
  | (false, false) => if χ = 1 then 1 else 0
  | (true, false) => mellinCoefficient (fun x : (ZMod p)ˣ => sparseAdditiveKernel E t x) χ
  | (false, true) => mellinCoefficient (fun x : (ZMod p)ˣ => sparseAdditiveKernel E t x) χ
  | (true, true) => mellinCoefficient (fun x : (ZMod p)ˣ => sparseAdditiveKernel E t x ^ 2) χ

noncomputable def sparseTruncatedMellinCoefficient {n : ℕ}
    (p : Fin n → ℕ) [∀ i, Fact (p i).Prime] (E : ∀ i, Finset (ZMod (p i)))
    (t : ℝ) (K : ℕ) (χ : ∀ i, MulChar (ZMod (p i)) ℂ) : ℂ :=
  ∑ v ∈ (Finset.univ : Finset (BilinearCube n)).filter
    (fun v => cubeDegree v false ≤ K ∧ cubeDegree v true ≤ K),
      ∏ i, sparsePatternMellin (E i) t (χ i) (v i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparsePrimitiveExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sparse weight as a bounded sum of primitive characters -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def sparsePrimitiveLabel {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (χ : ∀ i, MulChar (ZMod (p i)) ℂ) : Option PrimitiveComplexCharacter :=
  primitiveCharacterReduction (sparseProductCharacter p χ)

noncomputable def sparsePrimitiveCoefficient {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (E : ∀ i, Finset (ZMod (p i))) (t : ℝ) (K : ℕ) :
    Option PrimitiveComplexCharacter → ℂ :=
  injectiveCoefficient (sparsePrimitiveLabel p) (sparseTruncatedMellinCoefficient p E t K)

attribute [local instance] OAI.Ostmann.instFintypeMulCharZModComplexOfFactPrime_solutions_5
noncomputable def sparsePrimitiveSupport {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (E : ∀ i, Finset (ZMod (p i))) (t : ℝ) (K : ℕ) : Finset (Option PrimitiveComplexCharacter) :=
  ((Finset.univ : Finset (∀ i, MulChar (ZMod (p i)) ℂ)).filter
    (fun χ => sparseTruncatedMellinCoefficient p E t K χ ≠ 0)).image (sparsePrimitiveLabel p)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseExpandedMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Applying the analytic estimate to the actual sparse coefficients -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def sparseExpandedMangoldtMean {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (E : ∀ i, Finset (ZMod (p i))) (t : ℝ) (K : ℕ) (X : ℝ) : ℂ :=
  sparsePrimitiveCoefficient p E t K none * smoothMangoldtMean 1 1 X +
    ∑ ρ ∈ (sparsePrimitiveSupport p E t K).eraseNone,
      sparsePrimitiveCoefficient p E t K (some ρ) * smoothMangoldtMean ρ.modulus ρ.character X

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparsePrimeMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prime-weighted mean of the actual sparse subset weight -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def sparseWeightedPrimeSum {n : ℕ} (p : Fin n → ℕ)
    [∀ i, NeZero (p i)] (S : ∀ i, Finset (ZMod (p i))) (K : ℕ) (X : ℝ) : ℝ :=
  ∑ q ∈ (Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime,
    Real.log q * sparseSubsetWeight p S K (fun i => (q : ZMod (p i))) * primeMeanTest (q / X)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_MaskedPhaseGiantMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The favorable-prime mask in the initial giant

Nonfavorable primes remain in the prior. Their physical test is exactly zero.
-/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

@[simp] theorem phaseGiantPhysical_zero {p : ℕ} [NeZero p] (x : ZMod p) :
    phaseGiantPhysical (fun _ : ZMod p => (0 : ℂ)) x = 0 := by
  simp [phaseGiantPhysical, densityFourierInverse, densityFourier, additiveFourier_apply]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_CompleteTailGiantMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original giant mean from favorable primes and tail collisions

All prime laws in the conclusion are the full smooth harmonic cell laws.
The favorable set is only a mask on the Fourier test, never on the prior.
-/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def tailGiantPhysical (A : Set ℕ) (N : ℕ) (F : Finset ℕ)
    (p : ℕ) [Fact p.Prime] : ZMod p → ℂ :=
  phaseGiantPhysical (if p ∈ F then normalizedResidueTransform (tailDensityMask A N p)
    else fun _ => 0)

noncomputable def tailGiantEndpointMean (A : Set ℕ) (N : ℕ) (F E : Finset ℕ)
    (p : ℕ) : ℝ :=
  if hp : p.Prime then
    let _ : Fact p.Prime := ⟨hp⟩
    (E.card : ℝ)⁻¹ * ∑ a ∈ E, (tailGiantPhysical A N F p (a : ZMod p)).re
  else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HalfPrimeInitialAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive statistic for the actual phase/residue half-list -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

noncomputable def primeHalfTests {n : ℕ} (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)]
    (S : (q : P) → Finset (ZMod (q : ℕ))) (favorable : P → Bool) :
    Fin (n + 1) → (q : P) → ZMod (q : ℕ) → ℂ :=
  Fin.cons (fun q => primePhysicalTest (S q) true (favorable q))
    (fun _ q => normalizedResidueIndicator (S q))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialCellSchedule
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual four-at-a-time compensation cell schedule -/
namespace Ostmann
open scoped Classical

noncomputable def scheduledRegularPrimeSets (cell : ℕ → Finset ℕ) (bulk : Finset ℕ)
    (top : ℕ) (cs : List ℕ) (n m : ℕ) :
    MovingRegularSlot n (scheduledSmallLength cs) m → Finset ℕ :=
  fun i => Sum.elim (fun j => cell (scheduledSmallCell top cs j)) (fun _ => bulk) i.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingSmallPermutation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Permuting small slots preserves the literal initial coefficient -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

def movingSmallSlotEquiv (n m : ℕ) {r r' : ℕ} (e : Fin r ≃ Fin r') :
    MovingRegularSlot n r m ≃ MovingRegularSlot n r' m :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.sumCongr e (Equiv.refl _))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialScheduledPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected original priors in compensation order -/
namespace Ostmann
open scoped Classical

noncomputable def scheduledRegularPrior {A : Type} (cell : ℕ → A → ℝ)
    (bulk : A → ℝ) (top : ℕ) (cs : List ℕ) (n m : ℕ) :
    MovingRegularSlot n (scheduledSmallLength cs) m → A → ℝ :=
  fun i => Sum.elim (fun j => cell (scheduledSmallCell top cs j)) (fun _ => bulk) i.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledCellGap
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The geometric gap on the actual compensation schedule -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def scheduledSmallLower (top : ℕ) (cs : List ℕ) (n : ℕ)
    (i : TreeLeafIndex n × Fin (scheduledSmallLength cs)) : ℝ :=
  (scheduledSmallCell top cs i.2 : ℝ) - 1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual amplitudes along the shrinking compensation list -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def scheduledCellAmplitude {A : Type} [Fintype A]
    (value : A → ℕ) (outside : List ℕ) (μ : ℕ → A → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState A → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Pg : Finset ℕ) (ρ : Pg → ℝ)
    (cell : ℕ → A → ℝ) (bulk : A → ℝ) (top : ℕ) (cs : List ℕ) (n m : ℕ)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) : ℂ :=
  movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G
    n (scheduledSmallLength (cs.drop n)) m Pg ρ
    (scheduledRegularPrior cell bulk top (cs.drop n) n m) greg ggiant favorable

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledCellIteration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite iteration on the literal shrinking cell schedule -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def scheduledCellDiagonal {A : Type} [Fintype A]
    (value : A → ℕ) (outside : List ℕ) (μ : ℕ → A → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState A → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Pg I : Finset ℕ) (ρ : Pg → ℝ)
    (cell : ℕ → A → ℝ) (bulk : A → ℝ) (top : ℕ) (cs : List ℕ) (n m : ℕ)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) : ℝ :=
  movingAmplitudeDiagonal value outside μ childBound pivotBound V F φ G n
    (scheduledSmallLength (cs.drop (n + 1))) m Pg I ρ
    (scheduledRegularPrior cell bulk top (cs.drop (n + 1)) n m) greg ggiant favorable

end Ostmann

end OAI
end


