-- Prove2me | Definitions.Def_OAIQ095D008
-- name    : OAIQ095D008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:12:46.576716+00:00
-- url     : https://prove2.me/theorems/ba5c3ee3-7209-4ceb-a36c-0a4a0b881298
-- title:
--   Definitions bundle OAIQ095D008 of the split of OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 32 declarations of OpenAI's Lean: 32 definitions. The definitions and types are `OAI.Ostmann.movingOriginalLeaf`, `OAI.Ostmann.movingOriginalPatternDiagonalObservable`, `OAI.Ostmann.movingOriginalPatternMatchedObservable`, `OAI.Ostmann.movingOriginalSampleAverage`, `OAI.Ostmann.movingOriginalSupportedOuterPair`, `OAI.Ostmann.movingOuterPolynomialFactors`, `OAI.Ostmann.movingPatternBulkIntegrand`, `OAI.Ostmann.movingPatternBulkMultiplier`, `OAI.Ostmann.movingPatternFeasible`, `OAI.Ostmann.movingPatternFlagProduct`, `OAI.Ostmann.movingPatternHaarProduct`, `OAI.Ostmann.movingPatternLineProduct`, `OAI.Ostmann.movingPatternLogIntegrand`, `OAI.Ostmann.movingPatternLogPrimeBulkHaar`, `OAI.Ostmann.movingPatternLogPrimeObservable`, `OAI.Ostmann.movingPatternPrimeBulkHaar`, `OAI.Ostmann.movingPatternPrimeObservable`, `OAI.Ostmann.movingPatternSquareDifference`, `OAI.Ostmann.movingSampledInternalProbability`, `OAI.Ostmann.movingSmoothPolynomialFactors`, `OAI.Ostmann.movingSupportedSampleTerm`, `OAI.Ostmann.movingSupportedWeight`, `OAI.Ostmann.movingWeightedDiagonalEnergy`, `OAI.Ostmann.movingWeightedDiagonalKernel`, `OAI.Ostmann.movingWeightedDiagonalMean`, `OAI.Ostmann.movingWeightedMatchedCorrelation`, `OAI.Ostmann.movingWeightedMatchedKernel`, `OAI.Ostmann.movingWeightedMatchedMean`, `OAI.Ostmann.movingWindowedSpectatorWeight`, `OAI.Ostmann.pageKernelExclusion`, `OAI.Ostmann.restrictedPrimeGiantDensity`, `OAI.Ostmann.scheduledPageDeletions`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `Ostmann_Arithmetic_MovingOriginalSampleExpansion`, `Ostmann_Arithmetic_MovingOuterSlices`, `Ostmann_Arithmetic_MovingPatternArithmeticComparison`, `Ostmann_Arithmetic_MovingPatternAveragedSquare`, `Ostmann_Arithmetic_MovingPatternBulkFubini`, `Ostmann_Arithmetic_MovingPatternDiagonalObservable`, `Ostmann_Arithmetic_MovingPatternFrozenMultiplier`, `Ostmann_Arithmetic_MovingPatternIntegrand`, `Ostmann_Arithmetic_MovingPatternLogIntegrand`, `Ostmann_Arithmetic_MovingPatternLogPrimeBulk`, `Ostmann_Arithmetic_MovingPatternLogPrimeObservable`, `Ostmann_Arithmetic_MovingPatternMatchedObservable`, `Ostmann_Arithmetic_MovingPatternPrimeBulk`, `Ostmann_Arithmetic_MovingPatternPrimeObservable`, `Ostmann_Arithmetic_MovingSamplePairExpansion`, `Ostmann_Arithmetic_MovingSampledIndexedProbability`, `Ostmann_Arithmetic_MovingSmoothPolynomials`, `Ostmann_Arithmetic_MovingSupportedOuterFactor`, `Ostmann_Arithmetic_MovingSupportedWeight`, `Ostmann_Arithmetic_MovingWeightedDiagonalEnergy`, `Ostmann_Arithmetic_MovingWeightedDiagonalMean`, `Ostmann_Arithmetic_MovingWeightedMatchedCorrelation`, `Ostmann_Arithmetic_MovingWeightedMatchedMean`, `Ostmann_Arithmetic_MovingWindowedSpectators`, `Ostmann_Construction_ScheduledPageDeletions`, `Ostmann_QuadraticCenter_PageKernelExclusion`, `Ostmann_ZeroDensity_RestrictedGiantDensity`.
--
--   **Imports.** It imports the bundles `OAIQ095D006` and `OAIQ095D007` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ095D009`; the statements `OAI_Ostmann_EventuallyPrimeSumset_eventual_giant_from_favorable_blocks`, `OAI_Ostmann_EventuallyPrimeSumset_selected_endpoint_giant`, `OAI_Ostmann_EventuallyPrimeSumset_tail_spectator_pool`, `OAI.Ostmann.PublishedProgressionInput.movingPattern_diagonal_ideal_integral_rate`, `OAI.Ostmann.PublishedProgressionInput.movingPattern_diagonal_whole_shell_masked_rate`, `OAI.Ostmann.PublishedProgressionInput.movingPattern_half_log_good_ideal_integral_rate_window`, `OAI.Ostmann.PublishedProgressionInput.movingPattern_half_log_good_masked_whole_shell_rate`, `OAI.Ostmann.PublishedProgressionInput.movingPattern_half_log_selected_prime_rate_window`, `OAI.Ostmann.PublishedProgressionInput.movingPattern_log_mixed_prime_signed_bound`, `OAI.Ostmann.PublishedProgressionInput.movingPattern_original_mixed_prime_norm_arithmetic_rate`, `OAI.Ostmann.PublishedProgressionInput.movingPattern_original_mixed_prime_norm_bound`, `OAI.Ostmann.PublishedProgressionInput.movingPattern_selected_mixed_prime_norm_rate`, `OAI.Ostmann.PublishedProgressionInput.moving_pattern_diagonal_haar_rate`, `OAI.Ostmann.PublishedProgressionInput.moving_pattern_matched_haar_rate`, `OAI.Ostmann.PublishedProgressionInput.moving_selected_amplitude_regular_energy`, `OAI.Ostmann.PublishedProgressionInput.moving_selected_initial_diagonal_uniform`, `OAI.Ostmann.PublishedProgressionInput.moving_selected_initial_symmetrized_energy`, `OAI.Ostmann.PublishedProgressionInput.selected_scheduled_diagonal`, `OAI.Ostmann.PublishedProgressionInput.selected_scheduled_final_contradiction`, `OAI.Ostmann.frozen_initial_small_amplitude`, `OAI.Ostmann.movingTemplatePrimeAmplitude_step_full_coefficients`, `OAI.Ostmann.selected_scheduled_iteration`, `OAI_Ostmann_sparseWeightedPrimeSum_decay` and `OAI_Ostmann_sparseWeightedPrimeSum_lower`; the proofs of `OAI_Ostmann_EventuallyPrimeSumset_selected_endpoint_giant`, `OAI_Ostmann_EventuallyPrimeSumset_sparse_tail_mass_bound`, `OAI_Ostmann_EventuallyPrimeSumset_tail_spectator_pool`, `OAI.Ostmann.PublishedProgressionInput.movingPattern_diagonal_ideal_integral_rate`, `OAI.Ostmann.PublishedProgressionInput.movingPattern_diagonal_whole_shell_masked_rate`, `OAI.Ostmann.PublishedProgressionInput.movingPattern_half_log_good_ideal_integral_rate_window`, `OAI.Ostmann.PublishedProgressionInput.movingPattern_half_log_good_masked_whole_shell_rate`, `OAI.Ostmann.PublishedProgressionInput.movingPattern_half_log_selected_prime_rate_window`, `OAI.Ostmann.PublishedProgressionInput.movingPattern_log_mixed_prime_signed_bound`, `OAI.Ostmann.PublishedProgressionInput.movingPattern_original_mixed_prime_norm_arithmetic_rate`, `OAI.Ostmann.PublishedProgressionInput.movingPattern_original_mixed_prime_norm_bound`, `OAI.Ostmann.PublishedProgressionInput.movingPattern_selected_mixed_prime_norm_rate`, `OAI.Ostmann.PublishedProgressionInput.moving_outer_coprime_mixed_haar_rate`, `OAI.Ostmann.PublishedProgressionInput.moving_pattern_diagonal_haar_rate`, `OAI.Ostmann.PublishedProgressionInput.moving_pattern_matched_haar_rate`, `OAI.Ostmann.PublishedProgressionInput.moving_selected_amplitude_regular_energy`, `OAI.Ostmann.PublishedProgressionInput.moving_selected_initial_diagonal_uniform`, `OAI.Ostmann.PublishedProgressionInput.moving_selected_initial_symmetrized_energy`, `OAI.Ostmann.PublishedProgressionInput.selected_scheduled_diagonal`, `OAI.Ostmann.PublishedProgressionInput.selected_scheduled_final_contradiction`, `OAI.Ostmann.common_center_biased_populations_impossible`, `OAI.Ostmann.frozen_initial_small_amplitude`, `OAI.Ostmann.movingTemplatePrimeAmplitude_step_full_coefficients`, `OAI_Ostmann_retained_graph_original_pair_ratio_bound`, `OAI_Ostmann_selected_natural_final_contradiction`, `OAI.Ostmann.selected_scheduled_iteration`, `OAI_Ostmann_sparseWeightedPrimeSum_decay`, `OAI_Ostmann_sparseWeightedPrimeSum_lower`, `OAI_Ostmann_sparse_pair_coverage_size_bound`, `OAI.Ostmann.twoInfiniteSummandsImpossible_of_published`, `OAI_Ostmann_uniform_constituent_natural_history_energy` and `OAI_Ostmann_uniform_constituent_natural_square_rate`.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ095D006
import Definitions.Def_OAIQ095D007

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSmoothPolynomials
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One polynomial family for all node cutoffs and Fourier leaves -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def movingSmoothPolynomialFactors {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) :
    Fin (2 ^ n + (T.nodeCutoffPolynomials value L R).length) → ClippedPolynomialFactor :=
  Fin.append (movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi)
    (movingNodeCutoffFactors value T L R φ G B D hB hD hφ hlip)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingWindowedSpectators
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete nonsmooth factor of the original moving coefficient -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def movingWindowedSpectatorWeight {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (X lo hi : ℝ) (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) : ℂ :=
  movingUnrestrictedWeight value (movingWindowLeaf value X lo hi (movingDataLeaf F))
    (movingDataExtra E) T XL XR * ∏ i ∈ S, movingSlotSpectator value (g i) (D i) T XL XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSupportedWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full manuscript support on the literal recursive giant weight -/

namespace Ostmann
open scoped Classical SchwartzMap

/-- Multiplying by this mask retains all current-state coprimality and all
subtree-frequency unit tests, including the fixed outside list. -/
noncomputable def movingSupportedWeight {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) (z : ℂ) : ℂ :=
  if movingFullSupport value outside T XL XR then z else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSamplePairExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact paired expansion of the fully supported sampled coefficient

The equality-pattern scalar is the literal original prior times all node
compensations. The remaining coefficient retains every support test.
-/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingSupportedSampleTerm {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ) (a : MovingSampleSlots σ n) : ℂ :=
  movingSupportedWeight value outside (buildMovingSlotData n t small bulk a) XL XR
    (recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound (movingLocalExtra E)) n
      ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOriginalSampleExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original Fourier coefficient under the exact internal sampling law -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def movingOriginalLeaf {σ I : Type*} (value : σ → ℕ) (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (x : MovingSlotState σ) (s : ℤ) : ℂ :=
  (movingWindowLeaf value X lo hi (movingDataLeaf F) x s * movingFourierLeaf value ψ X x s) *
    ∏ i ∈ S, spectatorHistoryLeaf (movingSlotModulus value) (g i) (Dq i) x s

/-- The sampled Fourier coefficient, with all original support and all
original internal probabilities. -/
noncomputable def movingOriginalSampleAverage {σ I : Type*} [Fintype σ]
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (μ : ℕ → σ → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ) : ℂ :=
  ∑ a : MovingSampleSlots σ n, (movingSamplesPrior μ a : ℂ) *
    movingSupportedWeight value outside (buildMovingSlotData n t small bulk a) XL XR
      (movingOriginalGiantWeight q value childBound pivotBound F (movingCompensationExtra value)
        g Dq S ψ X lo hi φ G (buildMovingSlotData n t small bulk a) t XL XR)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOuterSlices
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Root and variation bounds with the original outer giant priors -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate SchwartzMap

noncomputable def movingOuterPolynomialFactors {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (diagonal : Bool) :=
  Fin.append (pairedPolynomialFactors
    (movingSmoothPolynomialFactors value (T false) L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip)
    (movingSmoothPolynomialFactors value (T true) L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip))
    (giantOuterFactors L R φ Jleft Jright B D hB hD hφ hlip diagonal)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSupportedOuterFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal supported two-history weights with their original outer priors -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate SchwartzMap

noncomputable def movingOriginalSupportedOuterPair {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : Bool → ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Jleft Jright : ℝ) (diagonal : Bool) {n : ℕ} (T : Bool → MovingSlotData σ n)
    (t : Bool → FrequencyTree ℤ n) (XL XR : ℕ) : ℂ :=
  (movingSupportedWeight value outside (T false) XL XR
      (movingOriginalGiantWeight q value childBound pivotBound (F false) (E false) g (Dq false) S
        ψ X lo hi φ G (T false) (t false) XL XR) *
    conj (movingSupportedWeight value outside (T true) XL XR
      (movingOriginalGiantWeight q value childBound pivotBound (F true) (E true) g (Dq true) S
        ψ X lo hi φ G (T true) (t true) XL XR))) *
      giantOuterWeight φ Jleft Jright diagonal XL XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RestrictedGiantDensity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded densities on the common real giant rectangle -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

noncomputable def restrictedPrimeGiantDensity (P : PublishedProgressionInput) (Q q a : ℕ)
    (u v : ℝ) : ℝ → ℂ :=
  (Set.Ioc u v).indicator (fun x => (selectedPrimeLogDensity P Q q a x : ℂ))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampledIndexedProbability
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual prime samples in the fixed line-probability coordinates -/

namespace Ostmann
open scoped Classical

noncomputable def movingSampledInternalProbability {A : Type*} {N n : ℕ}
    (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (T : Bool → MovingSlotData (Fin N) n) (x : Fin N → A) (rep : Fin N) : ℝ :=
  letI : Fact (prime (x rep)).Prime := ⟨hprime (x rep)⟩
  internalLineProbability true
    (fun j => MovingSlotReversal.naturalReduction (prime (x rep)) (fun i => prime (x i))
      (movingPrimeOccurrenceLine (fun i => prime (x i)) T (prime (x rep)) j).a)
    (fun j => MovingSlotReversal.naturalReduction (prime (x rep)) (fun i => prime (x i))
      (movingPrimeOccurrenceLine (fun i => prime (x i)) T (prime (x rep)) j).b)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternAveragedSquare
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual square-exclusion error averaged under original pattern weights -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingPatternSquareDifference {A B C : Type*} [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n)
    (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C) (x : Fin (N + 1) → A) : ℂ :=
  let T := movingPatternFinData e n t small bulk pattern
  letI : ∀ c : C, Fact (prime (x (e.symm (.inr c)))).Prime := fun _ => ⟨hprime _⟩
  (∏ c, movingInternalHaarAverage (fun i => prime (x i)) T (prime (x (e.symm (.inr c))))) -
    ∏ c, (movingSampledInternalProbability prime hprime T x (e.symm (.inr c)) : ℂ)

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

noncomputable def movingPatternLineProduct {A B C : Type*} [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C) (x : Fin (N + 1) → A) : ℂ :=
  ∏ c, (movingSampledInternalProbability prime hprime
    (movingPatternFinData e n t small bulk pattern) x (e.symm (.inr c)) : ℂ)

noncomputable def movingPatternHaarProduct {A B C : Type*} [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C) (x : Fin (N + 1) → A) : ℂ :=
  let T := movingPatternFinData e n t small bulk pattern
  letI : ∀ c : C, Fact (prime (x (e.symm (.inr c)))).Prime := fun _ => ⟨hprime _⟩
  ∏ c, movingInternalHaarAverage (fun i => prime (x i)) T (prime (x (e.symm (.inr c))))

noncomputable def movingPatternFlagProduct {A B C : Type*} [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (x : Fin (N + 1) → A) : ℂ :=
  let T := movingPatternFinData e n t small bulk pattern
  let base := movingPatternFinRepresentative e n t small bulk pattern rep
  ∏ c, (internalLineFlagWeight true (prime (x (e.symm (.inr c))))
    (fun s => arithmeticTestFlag (lineTestPolynomials
      (movingIndexedLine T (e.symm (.inr c)) (base c))
      ⟨(base c).1, (base c).2.val⟩ s = 0)) : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternFrozenMultiplier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Symbolic internal factors are constant under selected bulk resampling -/

namespace Ostmann
open scoped Classical BigOperators

def movingPatternFeasible {B C : Type*} {N : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) : Prop :=
  let T := movingPatternFinData e n t small bulk pattern
  let base := movingPatternFinRepresentative e n t small bulk pattern rep
  ∀ c, lineFeasibleFlags true (fun s => arithmeticTestFlag (lineTestPolynomials
    (movingIndexedLine T (e.symm (.inr c)) (base c)) ⟨(base c).1, (base c).2.val⟩ s = 0))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternBulkFubini
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The signed bulk sum under the actual compensated pattern law -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingPatternBulkMultiplier {A B C : Type*} [Fintype A] [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (prime : A → ℕ)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (x : Fin (N + 1) → A) : ℂ :=
  (movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
    (fun i => x (e.symm (.inr (pattern i))))) : ℂ) *
    movingPatternFlagProduct e prime n t small bulk pattern rep x

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternDiagonalObservable
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original diagonal observable on the finite pattern sample space -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

noncomputable def movingOriginalPatternDiagonalObservable {B C J : Type*} [Fintype J]
    {N n m : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (t : Bool → FrequencyTree ℤ n) (small : TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (pattern : Bool × MovingSampleIndex n → C)
    (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
    (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
    (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
    (reg : J → Fin (N + 1)) (active : J → Bool) (sreg : ℤ)
    (other : (Fin (N + 1) → primes) → J → ℤ)
    (greg : ∀ q : ℕ, ZMod q → ℂ)
    (f : ℤ → ℂ) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v a b center : ℝ)
    (x : Fin (N + 1) → primes) : ℂ := by
  let value := fun i => (x i : ℕ)
  let : ∀ j, Fact (value (reg j)).Prime := fun j => ⟨hprimes _ (x (reg j)).property⟩
  exact complexPrimeInterval 1 0 a b (fun y => complexIntegerInterval 1 0 u v center (fun z =>
    movingOriginalSupportedOuterPair p value outside childBound pivotBound
      (fun _ {_} _ => f) (fun _ {_} _ _ _ _ => 1) g (fun _ => Dq) Finset.univ
      ψ X lo hi φ G Jleft Jright diagonal
      (movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern)
      t ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ *
    (naturalRegularMultiplier (fun j => value (reg j)) active sreg
      (fun j => (other x j : ZMod (value (reg j)))) (fun j => greg (value (reg j)))
      ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ : ℂ)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternIntegrand
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual pattern's bounded bulk integrand -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

section
variable {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (base : Fin (N + 1) → ℝ) (childBound pivotBound : ℕ → ℕ)
    (j₀ : TreeLeafIndex n × Fin m)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (L U : ℝ)

noncomputable def movingPatternBulkIntegrand : BulkIntegrand (TreeLeafIndex n × Fin m) :=
  (bulkLogKernelPairIntegrand base (selectedBulkSet (movingPatternBulkEmbedding e slot))
    childBound pivotBound (movingPatternFinBulkData e n m t small slot perm pattern)
    (movingPatternBulkSet_compensationAbsent e tierB tierC t small slot perm pattern hB htier)
    (movingPatternBulkEmbedding e slot j₀) ((mem_selectedBulkSet _ _).mpr ⟨j₀, rfl⟩)
    ψ X lo hi V hlo hhi
    (movingPatternFinBulkData_frequencies e t small slot perm pattern (fun s => |(s : ℝ)| ≤ V) hfreq)
    φ G Bφ Dφ hBφ hDφ hφ hlip hout L U).pullBulk base (movingPatternBulkEmbedding e slot)

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternLogIntegrand
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual pattern kernel with its retained bulk logarithmic weights -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

section
variable {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (base : Fin (N + 1) → ℝ) (childBound pivotBound : ℕ → ℕ)
    (j₀ : TreeLeafIndex n × Fin m)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (L U : ℝ)
    {tlog : ℕ} (logSlots : Fin tlog → List (Fin (N + 1))) (cb : ℝ)

noncomputable def movingPatternLogIntegrand : BulkIntegrand (TreeLeafIndex n × Fin m) :=
  (bulkLogKernelPairIntegrand base (selectedBulkSet (movingPatternBulkEmbedding e slot))
    childBound pivotBound (movingPatternFinBulkData e n m t small slot perm pattern)
    (movingPatternBulkSet_compensationAbsent e tierB tierC t small slot perm pattern hB htier)
    (movingPatternBulkEmbedding e slot j₀) ((mem_selectedBulkSet _ _).mpr ⟨j₀, rfl⟩)
    ψ X lo hi V hlo hhi
    (movingPatternFinBulkData_frequencies e t small slot perm pattern (fun s => |(s : ℝ)| ≤ V) hfreq)
    φ G Bφ Dφ hBφ hDφ hφ hlip hout L U).withLogCutoffs base
      (selectedBulkSet (movingPatternBulkEmbedding e slot)) cb logSlots |>.pullBulk base (movingPatternBulkEmbedding e slot)

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternPrimeBulk
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact selected-prime mean of the original pattern kernel -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

section
variable {B C Cell I : Type*} [Fintype Cell] [Fintype I] {N n m : ℕ}
  (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
  (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
  (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
  (pattern : Bool × MovingSampleIndex n → C)
  (hsmall : ∀ b, ∀ i ∈ flattenMovingSlots n (small b), i ∉ Set.range slot)
  (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
  (base : Fin (N + 1) → ℕ) (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
  (hbase : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), (base i).Prime)
  (childBound pivotBound : ℕ → ℕ)
  (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
  (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
  (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
  (hR : ∀ b, (movingPatternFinBulkData e n m t small slot perm pattern b).frequencyProduct ∣ R)
  (hr : R ^ (n + 1) ∣ (r : ℤ))
  (p : I → ℕ) [∀ i, Fact (p i).Prime]
  (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
  (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
  (twist : ∀ i, Bool → (ZMod (p i))ˣ)
  (P : PublishedProgressionInput) (Q : ℕ) (y : ℝ)
  (j₀ : TreeLeafIndex n × Fin m) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
  (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (hV : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
  (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
  (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
  (hφout : ∀ x, 1 ≤ |x| → φ x = 0) (L U : ℝ)

/-- This is the original real kernel and its original Page and spectator
averages, evaluated after inserting the selected prime draws. -/
noncomputable def movingPatternPrimeBulkHaar (x : (TreeLeafIndex n × Fin m) → primes) : ℂ :=
  let value := primeBulkValues base (movingPatternBulkEmbedding e slot) x
  let hp := primeBulkValues_prime base (movingPatternBulkEmbedding e slot) x hprimes hbase
  let data := movingPatternFinBulkData e n m t small slot perm pattern
  let nodes := fun b => (data b).formulaNodes value (fun i => (hp i).ne_zero)
    childBound pivotBound
    (movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq b)
    (.prime false) (.prime true)
  movingRealKernelPair value data nodes ψ X lo hi hlo hhi φ G L U *
    (movingFrequencyPageAverage value outside F E data nodes R r P Q y *
      ∏ i, movingSpectatorHaarAverage value (p i) (g i) (twist i) data)

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternLogPrimeBulk
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact selected-prime mean of the original pattern kernel -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

section
variable {B C Cell I : Type*} [Fintype Cell] [Fintype I] {N n m : ℕ}
  (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
  (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
  (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
  (pattern : Bool × MovingSampleIndex n → C)
  (hsmall : ∀ b, ∀ i ∈ flattenMovingSlots n (small b), i ∉ Set.range slot)
  (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
  (base : Fin (N + 1) → ℕ) (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
  (hbase : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), (base i).Prime)
  (childBound pivotBound : ℕ → ℕ)
  (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
  (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
  (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
  (hR : ∀ b, (movingPatternFinBulkData e n m t small slot perm pattern b).frequencyProduct ∣ R)
  (hr : R ^ (n + 1) ∣ (r : ℤ))
  (p : I → ℕ) [∀ i, Fact (p i).Prime]
  (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
  (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
  (twist : ∀ i, Bool → (ZMod (p i))ˣ)
  (P : PublishedProgressionInput) (Q : ℕ) (y : ℝ)
  (j₀ : TreeLeafIndex n × Fin m) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
  (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (hV : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
  (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
  (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
  (hφout : ∀ x, 1 ≤ |x| → φ x = 0) (L U : ℝ)
  {tlog : ℕ} (logSlots : Fin tlog → List (Fin (N + 1))) (cb : ℝ)

/-- This is the original real kernel and its original Page and spectator
averages, evaluated after inserting the selected prime draws. -/
noncomputable def movingPatternLogPrimeBulkHaar (x : (TreeLeafIndex n × Fin m) → primes) : ℂ :=
  let value := primeBulkValues base (movingPatternBulkEmbedding e slot) x
  let hp := primeBulkValues_prime base (movingPatternBulkEmbedding e slot) x hprimes hbase
  let data := movingPatternFinBulkData e n m t small slot perm pattern
  let nodes := fun b => (data b).formulaNodes value (fun i => (hp i).ne_zero)
    childBound pivotBound
    (movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq b)
    (.prime false) (.prime true)
  ((∏ j, bulkLogCutoffWeight (fun i => (value i : ℝ)) cb (logSlots j) : ℝ) : ℂ) *
    (movingRealKernelPair value data nodes ψ X lo hi hlo hhi φ G L U *
    (movingFrequencyPageAverage value outside F E data nodes R r P Q y *
      ∏ i, movingSpectatorHaarAverage value (p i) (g i) (twist i) data))

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternPrimeObservable
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal prime observable in the original nonbulk Fubini formula -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

section
variable {B C I : Type*} [Fintype I] {N n m : ℕ}
  (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
  (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
  (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
  (pattern : Bool × MovingSampleIndex n → C)
  (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
  (childBound pivotBound : ℕ → ℕ)
  (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
  (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
  (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
  (p : I → ℕ) [∀ i, Fact (p i).Prime] (g : ∀ i, ZMod (p i) → ℂ)
  (twist : ∀ i, Bool → (ZMod (p i))ˣ) (P : PublishedProgressionInput) (Q : ℕ) (y : ℝ)
  (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (φ : ℝ → ℝ) (G : ℕ → ℝ) (L U : ℝ)

/-- The coefficient before selecting or conditioning any of its bulk
coordinates. All original frequency and coprimality gates are retained. -/
noncomputable def movingPatternPrimeObservable (x : Fin (N + 1) → primes) : ℂ :=
  let value := fun i => (x i : ℕ)
  let data := movingPatternFinBulkData e n m t small slot perm pattern
  let nodes := fun b => (data b).formulaNodes value
    (fun i => (hprimes _ (x i).property).ne_zero) childBound pivotBound
    (movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq b)
    (.prime false) (.prime true)
  movingRealKernelPair value data nodes ψ X lo hi hlo hhi φ G L U *
    (movingFrequencyPageAverage value outside F E data nodes R r P Q y *
      ∏ i, movingSpectatorHaarAverage value (p i) (g i) (twist i) data)

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternLogPrimeObservable
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal prime observable in the original nonbulk Fubini formula -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

section
variable {B C I : Type*} [Fintype I] {N n m : ℕ}
  (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
  (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
  (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
  (pattern : Bool × MovingSampleIndex n → C)
  (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
  (childBound pivotBound : ℕ → ℕ)
  (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
  (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
  (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
  (p : I → ℕ) [∀ i, Fact (p i).Prime] (g : ∀ i, ZMod (p i) → ℂ)
  (twist : ∀ i, Bool → (ZMod (p i))ˣ) (P : PublishedProgressionInput) (Q : ℕ) (y : ℝ)
  (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (φ : ℝ → ℝ) (G : ℕ → ℝ) (L U : ℝ)
  {tlog : ℕ} (logSlots : Fin tlog → List (Fin (N + 1))) (cb : ℝ)

/-- The coefficient before selecting or conditioning any of its bulk
coordinates. All original frequency and coprimality gates are retained. -/
noncomputable def movingPatternLogPrimeObservable (x : Fin (N + 1) → primes) : ℂ :=
  let value := fun i => (x i : ℕ)
  let data := movingPatternFinBulkData e n m t small slot perm pattern
  let nodes := fun b => (data b).formulaNodes value
    (fun i => (hprimes _ (x i).property).ne_zero) childBound pivotBound
    (movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq b)
    (.prime false) (.prime true)
  ((∏ j, bulkLogCutoffWeight (fun i => (value i : ℝ)) cb (logSlots j) : ℝ) : ℂ) *
    (movingRealKernelPair value data nodes ψ X lo hi hlo hhi φ G L U *
    (movingFrequencyPageAverage value outside F E data nodes R r P Q y *
      ∏ i, movingSpectatorHaarAverage value (p i) (g i) (twist i) data))

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternMatchedObservable
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original matched-history observable on the finite pattern sample space -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

noncomputable def movingOriginalPatternMatchedObservable {B C J : Type*} [Fintype J]
    {N n m : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (t : Bool → FrequencyTree ℤ n) (small : TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m)) (pattern : Bool × MovingSampleIndex n → C)
    (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
    (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
    (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
    (reg : J → Fin (N + 1)) (active : J → Bool) (sreg : ℤ)
    (other : (Fin (N + 1) → primes) → J → ℤ)
    (greg : ∀ q : ℕ, ZMod q → ℂ)
    (f : ℤ → ℂ) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v a b center : ℝ)
    (x : Fin (N + 1) → primes) : ℂ := by
  let value := fun i => (x i : ℕ)
  let : ∀ j, Fact (value (reg j)).Prime := fun j => ⟨hprimes _ (x (reg j)).property⟩
  exact complexPrimeInterval 1 0 a b (fun y => complexIntegerInterval 1 0 u v center (fun z =>
    movingOriginalSupportedOuterPair p value outside childBound pivotBound
      (fun _ {_} _ => f) (fun _ {_} _ _ _ _ => 1) g (fun _ => Dq) Finset.univ
      ψ X lo hi φ G Jleft Jright diagonal
      (movingPatternFinBulkData e n m t (fun _ => small) slot perm pattern)
      t ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ *
    (naturalRegularMultiplier (fun j => value (reg j)) active sreg
      (fun j => (other x j : ZMod (value (reg j)))) (fun j => greg (value (reg j)))
      ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ : ℂ)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingWeightedDiagonalMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equality patterns with a retained external Fourier multiplier -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def movingWeightedDiagonalKernel {σ I B : Type*} {n : ℕ}
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (childBound pivotBound : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (t : Bool → FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List B) n)
    (W : (B → σ) → ℝ → ℝ → ℂ) (u v r w center : ℝ)
    (y : B → σ) (a : MovingSampleSlots σ n × MovingSampleSlots σ n) : ℂ :=
  let H := fun b XL XR =>
    let T := buildMovingSlotData n (t b) (treeLeafMap (List.map y) n small)
      (treeLeafMap (List.map y) n bulk) (if b then a.2 else a.1)
    movingSupportedWeight value outside T XL XR
      (movingOriginalGiantWeight q value childBound pivotBound (fun _ => f)
        (fun _ _ _ _ => 1) g Dq S ψ X lo hi φ G T (t b) XL XR)
  complexPrimeInterval 1 0 r w (fun z => complexIntegerInterval 1 0 u v center (fun x =>
    (H false ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊ *
      star (H true ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)) *
      W y x z))

/-- Both history averages and the external law are the original ones. -/
noncomputable def movingWeightedDiagonalMean {σ I B : Type*}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List B) n)
    (W : (B → σ) → ℝ → ℝ → ℂ) (u v r w center : ℝ) : ℂ :=
  ∑ y : B → σ, ((∏ b, ν b (y b) : ℝ) : ℂ) *
    complexPrimeInterval 1 0 r w (fun z => complexIntegerInterval 1 0 u v center (fun x =>
      (movingOriginalSampleAverage q value outside μ childBound pivotBound (fun _ => f)
        g Dq S ψ X lo hi φ G n (t false) (treeLeafMap (List.map y) n small)
        (treeLeafMap (List.map y) n bulk) ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊ *
      star (movingOriginalSampleAverage q value outside μ childBound pivotBound (fun _ => f)
        g Dq S ψ X lo hi φ G n (t true) (treeLeafMap (List.map y) n small)
        (treeLeafMap (List.map y) n bulk) ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)) *
      W y x z))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingWeightedDiagonalEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact expansion of the coefficient square with its exterior mask retained -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def movingWeightedDiagonalEnergy {σ I B : Type}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (small bulk : TreeLeafTuple (List B) n)
    (W : ℤ → (B → σ) → ℝ → ℝ → ℂ) (u v r w center : ℝ) : ℂ :=
  ∑ s : transferFrequencyRange (V n), ∑ y : B → σ, ((∏ b, ν b (y b) : ℝ) : ℂ) *
    complexPrimeInterval 1 0 r w (fun z => complexIntegerInterval 1 0 u v center (fun x =>
      (‖movingFrequencyCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G n s.val
        (treeLeafMap (List.map y) n small) (treeLeafMap (List.map y) n bulk)
        ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊‖ ^ 2 : ℂ) *
      W s.val y x z))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingWeightedMatchedMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original matched-history mean and its exact equality patterns -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def movingWeightedMatchedKernel {σ I B : Type*} {n : ℕ}
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (childBound pivotBound : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (t : Bool → FrequencyTree ℤ n) (small : TreeLeafTuple (List B) n) (bulk : Bool → TreeLeafTuple (List B) n)
    (W : (B → σ) → ℝ → ℝ → ℂ) (u v r w center : ℝ)
    (y : B → σ) (a : MovingSampleSlots σ n × MovingSampleSlots σ n) : ℂ :=
  let H := fun b XL XR =>
    let T := buildMovingSlotData n (t b) (treeLeafMap (List.map y) n small)
      (treeLeafMap (List.map y) n (bulk b)) (if b then a.2 else a.1)
    movingSupportedWeight value outside T XL XR
      (movingOriginalGiantWeight q value childBound pivotBound (fun _ => f)
        (fun _ _ _ _ => 1) g Dq S ψ X lo hi φ G T (t b) XL XR)
  complexPrimeInterval 1 0 r w (fun z => complexIntegerInterval 1 0 u v center (fun x =>
    (H false ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊ *
      star (H true ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)) *
      W y x z))

/-- Both history averages and the external law are the original ones. -/
noncomputable def movingWeightedMatchedMean {σ I B : Type*}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small : TreeLeafTuple (List B) n) (bulk : Bool → TreeLeafTuple (List B) n)
    (W : (B → σ) → ℝ → ℝ → ℂ) (u v r w center : ℝ) : ℂ :=
  ∑ y : B → σ, ((∏ b, ν b (y b) : ℝ) : ℂ) *
    complexPrimeInterval 1 0 r w (fun z => complexIntegerInterval 1 0 u v center (fun x =>
      (movingOriginalSampleAverage q value outside μ childBound pivotBound (fun _ => f)
        g Dq S ψ X lo hi φ G n (t false) (treeLeafMap (List.map y) n small)
        (treeLeafMap (List.map y) n (bulk false)) ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊ *
      star (movingOriginalSampleAverage q value outside μ childBound pivotBound (fun _ => f)
        g Dq S ψ X lo hi φ G n (t true) (treeLeafMap (List.map y) n small)
        (treeLeafMap (List.map y) n (bulk true)) ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)) *
      W y x z))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingWeightedMatchedCorrelation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full original correlation of two matched bulk assignments -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def movingWeightedMatchedCorrelation {σ I B : Type}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (small : TreeLeafTuple (List B) n) (bulk : Bool → TreeLeafTuple (List B) n)
    (W : ℤ → (B → σ) → ℝ → ℝ → ℂ) (u v r w center : ℝ) : ℂ :=
  ∑ s : transferFrequencyRange (V n), ∑ y : B → σ, ((∏ b, ν b (y b) : ℝ) : ℂ) *
    complexPrimeInterval 1 0 r w (fun z => complexIntegerInterval 1 0 u v center (fun x =>
      (movingFrequencyCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G n s.val
        (treeLeafMap (List.map y) n small) (treeLeafMap (List.map y) n (bulk false))
        ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊ *
        star (movingFrequencyCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G n s.val
        (treeLeafMap (List.map y) n small) (treeLeafMap (List.map y) n (bulk true))
        ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)) *
      W s.val y x z))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledPageDeletions
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two actual Page deletions fit the constructed initial prime pool -/
namespace Ostmann
open scoped Classical

noncomputable def scheduledPageDeletions (P : PublishedProgressionInput) (L : ℝ)
    (cutoff : ℕ) : Finset ℕ :=
  pageDeletionPrimes (selectedPageZero P (giantProgressionCutoff L)) cutoff ∪
    pageDeletionPrimes (selectedPageZero P (bulkProgressionCutoff L)) cutoff

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_PageKernelExclusion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the kernel family of a large Page character -/

namespace Ostmann

open scoped Classical

noncomputable def pageKernelExclusion (P : PublishedProgressionInput) (Q : ℕ) (R : ℝ) : Finset ℤ :=
  match selectedPageZero P Q with
  | none => ∅
  | some e => if R < (e.modulus : ℝ) then largeConductorKernelCandidates e.modulus else ∅

end Ostmann

end OAI
end


