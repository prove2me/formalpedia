-- Prove2me | Definitions.Def_OAIQ095D005
-- name    : OAIQ095D005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:00:16.85843+00:00
-- url     : https://prove2.me/theorems/793c6e39-61be-4924-b0cd-34b2ab7d7df5
-- title:
--   Definitions bundle OAIQ095D005 of the split of OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 231 declarations of OpenAI's Lean: 217 definitions, 3 instances and 11 theorems. The definitions and types are `OAI.Ostmann.frequencyTripleData`, `OAI.Ostmann.movingGiantFrequencyUnits`, `OAI.Ostmann.movingGiantPhase`, `OAI.Ostmann.movingIndexedOccurrence`, `OAI.Ostmann.movingModularGiantUnits`, `OAI.Ostmann.movingNaturalNodeCutoff`, `OAI.Ostmann.movingNodeCutoffFactors`, `OAI.Ostmann.movingPairedGiantEquiv`, `OAI.Ostmann.movingPatternBulkEmbedding`, `OAI.Ostmann.movingPatternFiniteSmall`, `OAI.Ostmann.movingPolynomialFourierTree`, `OAI.Ostmann.movingPrimeNodeFactor`, `OAI.Ostmann.movingRealNodeCutoff`, `OAI.Ostmann.movingRealWindowFlag`, `OAI.Ostmann.movingRepresentativeIndex`, `OAI.Ostmann.movingResidueFlag`, `OAI.Ostmann.movingResidueGate`, `OAI.Ostmann.movingRootState`, `OAI.Ostmann.movingSampleTier`, `OAI.Ostmann.movingSignedOutsideUnits`, `OAI.Ostmann.movingSignedSpectator`, `OAI.Ostmann.movingSlotSpectator`, `OAI.Ostmann.movingSpectatorDenominator`, `OAI.Ostmann.movingSpectatorResidue`, `OAI.Ostmann.movingTemplateCompensationEquiv`, `OAI.Ostmann.movingTemplateDoubledPrior`, `OAI.Ostmann.movingTemplateRestoredPrior`, `OAI.Ostmann.movingTemplateSidePrior`, `OAI.Ostmann.movingTopPivot`, `OAI.Ostmann.movingUnrestrictedWeight`, `OAI.Ostmann.nodeAncestorValues`, `OAI.Ostmann.originalProductRange`, `OAI.Ostmann.outerQuadraticParameters`, `OAI.Ostmann.pageDeletionPrimes`, `OAI.Ostmann.pairFrequencySupportBound`, `OAI.Ostmann.pairedFrequencyKernel`, `OAI.Ostmann.pairedPolynomialFactors`, `OAI.Ostmann.parityPathValue`, `OAI.Ostmann.paritySlotPerm`, `OAI.Ostmann.pivotConstituentEquiv` and 177 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `Ostmann_Arithmetic_ArithmeticFrequencyTree`, `Ostmann_Arithmetic_ArithmeticSplitTreeSupport`, `Ostmann_Arithmetic_BulkPrimeAtoms`, `Ostmann_Arithmetic_MovingAmplitudeNext`, `Ostmann_Arithmetic_MovingAveragedIntegerNode`, `Ostmann_Arithmetic_MovingCutoffPolynomials`, `Ostmann_Arithmetic_MovingFourierFactor`, `Ostmann_Arithmetic_MovingFrequencyCoefficient`, `Ostmann_Arithmetic_MovingFrequencyPrimeSquare`, `Ostmann_Arithmetic_MovingGiantPhase`, `Ostmann_Arithmetic_MovingGiantSamples`, `Ostmann_Arithmetic_MovingIndexedLineSystem`, `Ostmann_Arithmetic_MovingNodeCutoffFactor`, `Ostmann_Arithmetic_MovingOutsideResidues`, `Ostmann_Arithmetic_MovingPairedTransform`, `Ostmann_Arithmetic_MovingPatternBulkData`, `Ostmann_Arithmetic_MovingPatternBulkFrozen`, `Ostmann_Arithmetic_MovingPatternFinite`, `Ostmann_Arithmetic_MovingPatternTree`, `Ostmann_Arithmetic_MovingPrimeNodeFactor`, `Ostmann_Arithmetic_MovingRealResidues`, `Ostmann_Arithmetic_MovingRealWindows`, `Ostmann_Arithmetic_MovingResidueFactorization`, `Ostmann_Arithmetic_MovingSampleCoordinates`, `Ostmann_Arithmetic_MovingSampledRecursion`, `Ostmann_Arithmetic_MovingSignedSpectator`, `Ostmann_Arithmetic_MovingSlotSpectator`, `Ostmann_Arithmetic_MovingSpectatorCongruence`, `Ostmann_Arithmetic_MovingSupportWeight`, `Ostmann_Arithmetic_MovingTemplateAmplitudeRestore`, `Ostmann_Arithmetic_MovingTemplatePrior`, `Ostmann_Arithmetic_RecursiveLeafExpansion`, `Ostmann_Arithmetic_RecursiveNodeExpansion`, `Ostmann_Arithmetic_RecursiveSupportExpansion`, `Ostmann_Arithmetic_SampledHistoryEnergy`, `Ostmann_Arithmetic_SequentialSupport`, `Ostmann_Arithmetic_SingleFrequencyTree`, `Ostmann_Arithmetic_SplitSampleLists`, `Ostmann_Arithmetic_SquareLiftExclusions`, `Ostmann_Characters_AnchorPairCode`, `Ostmann_Characters_CharacterPrimeMean`, `Ostmann_Characters_PolynomialWeightPair`, `Ostmann_Characters_QuartetBadCoordinates`, `Ostmann_Characters_QuartetConjugation`, `Ostmann_Characters_QuartetFriendlyCoordinates`, `Ostmann_Characters_QuartetOrientedValue`, `Ostmann_Characters_QuartetSamePairBound`, `Ostmann_Characters_QuartetSymmetry`, `Ostmann_Characters_SparseWeightUnitMean`, `Ostmann_Characters_TailCharacterRotation`, `Ostmann_Characters_TensorUnitMean`, `Ostmann_Characters_TreeLeafIndex`, `Ostmann_Characters_TreeProfile`, `Ostmann_Construction_ActiveNonbulkCount`, `Ostmann_Construction_BiasedTailSelection`, `Ostmann_Construction_ConstituentPivotEnumeration`, `Ostmann_Construction_FinalReassignments`, `Ostmann_Construction_FiniteFrequencyExpansion`, `Ostmann_Construction_FixedPivotEnergyTransport`, `Ostmann_Construction_OriginalProductRange`, `Ostmann_Construction_PreorderTransferPaths`, `Ostmann_Construction_PrimeCellPartitionConstruction`, `Ostmann_Construction_PrimeExternalAverage`, `Ostmann_Construction_RetainedCharacterPrimeBound`, `Ostmann_Construction_ReverseAtomSources`, `Ostmann_Construction_ScaledWordLeaves`, `Ostmann_Construction_SchedulePairwiseReplay`, `Ostmann_Construction_ScheduledFinalComparison`, `Ostmann_Construction_ScheduledFrequencyHistory`, `Ostmann_Construction_ScheduledFullFinalPermutation`, `Ostmann_Construction_ScheduledFullMatchingGraph`, `Ostmann_Construction_ScheduledInputPhase`, `Ostmann_Construction_ScheduledNodeSources`, `Ostmann_Construction_ScheduledPageDeletions`, `Ostmann_Construction_ScheduledPreorderNodes`, `Ostmann_Construction_ScheduledPriorFubini`, `Ostmann_Construction_ScheduledSampleQuotient`, `Ostmann_Construction_ScheduledWordLeafCoordinates`, `Ostmann_Construction_ScheduledWordLeafProducts`, `Ostmann_Construction_SelectedCompensationPrior`, `Ostmann_Construction_SelectedFinalInteraction`, `Ostmann_Construction_SelectedFinalPermutation`, `Ostmann_Construction_SelectedFullFinalPermutation`, `Ostmann_Construction_SelectedInitialPriorBounds`, `Ostmann_Construction_SeparatedMatchingCount`, `Ostmann_Construction_SmoothGiantExternalAverage`, `Ostmann_Construction_StablePrimeSelection`, `Ostmann_Construction_TailMaskCollision`, `Ostmann_Construction_TransferCharacterProduct`, `Ostmann_Construction_TransferGraphPhase`, `Ostmann_Construction_WordTransferGuardFamily`, `Ostmann_Construction_WordTransferWeightIdentity`, `Ostmann_Construction_WordUnitCoefficient`, `Ostmann_Preliminaries_AdditiveSieveProof`, `Ostmann_Preliminaries_TailStability`, `Ostmann_QuadraticCenter_FixedQuadraticFamily`, `Ostmann_QuadraticCenter_LargeKernelFamily`, `Ostmann_QuadraticCenter_MaximalQuadraticBias`, `Ostmann_QuadraticCenter_OuterKernelFamily`, `Ostmann_QuadraticCenter_RootCollisions`, `Ostmann_QuadraticCenter_SmallKernelFamily`, `Ostmann_QuadraticSieve_PrimitiveKernelCharacter`, `Ostmann_Quadratic_QuadraticBilinearExpansion`, `Ostmann_Quadratic_QuadraticCorrectionEnvelope`, `Ostmann_Quadratic_QuadraticDivisorFamily`, `Ostmann_Quadratic_QuadraticDivisorRange`, `Ostmann_Quadratic_QuadraticDivisorSplit`, `Ostmann_Quadratic_QuadraticDyadicDivisors`, `Ostmann_Quadratic_QuadraticDyadicSelection`, `Ostmann_Quadratic_QuadraticFirstFrequencyCutoff`, `Ostmann_Quadratic_QuadraticFirstKernelError`, `Ostmann_Quadratic_QuadraticFirstMomentTransform`, `Ostmann_Quadratic_QuadraticFirstSecondKernel`, `Ostmann_Quadratic_QuadraticFirstSecondMain`, `Ostmann_Quadratic_QuadraticFullHighGrowth`, `Ostmann_Quadratic_QuadraticFullLowGrowth`, `Ostmann_Quadratic_QuadraticFullMiddleGrowth`, `Ostmann_Quadratic_QuadraticFullSmallHighGrowth`, `Ostmann_Quadratic_QuadraticFullSmallMiddleGrowth`, `Ostmann_Quadratic_QuadraticGaussBilinear`, `Ostmann_Quadratic_QuadraticGcdExpansion`, `Ostmann_Quadratic_QuadraticGcdRemainder`, `Ostmann_Quadratic_QuadraticGcdSecondFrequency`, `Ostmann_Quadratic_QuadraticGcdSecondTotal`, `Ostmann_Quadratic_QuadraticGrowthCorrectionBands`, `Ostmann_Quadratic_QuadraticGrowthDivisorBudget`, `Ostmann_Quadratic_QuadraticMainCoefficients`, `Ostmann_Quadratic_QuadraticMainComparison`, `Ostmann_Quadratic_QuadraticMiddleBandGrowth`, `Ostmann_Quadratic_QuadraticMiddleDivisor`, `Ostmann_Quadratic_QuadraticMomentMainComparison`, `Ostmann_Quadratic_QuadraticOffDiagonalPairSums`, `Ostmann_Quadratic_QuadraticOriginalMainTerms`, `Ostmann_Quadratic_QuadraticRootDivisor`, `Ostmann_Quadratic_QuadraticRoughBound`, `Ostmann_Quadratic_QuadraticRoughDyadic`, `Ostmann_Quadratic_QuadraticRowNorm`, `Ostmann_Quadratic_QuadraticSecondSignedCore`, `Ostmann_Quadratic_QuadraticSieveAdditiveStart`, `Ostmann_Quadratic_QuadraticSieveWeight`, `Ostmann_Quadratic_QuadraticSignedInfiniteSum`, `Ostmann_Quadratic_QuadraticSmallCorrectionGrowth`, `Ostmann_Quadratic_QuadraticSmallGcdTransform`, `Ostmann_Quadratic_QuadraticSmallKernelMain`, `Ostmann_Quadratic_QuadraticSmallKernels`, `Ostmann_Quadratic_QuadraticSmallMomentMain`, `Ostmann_Quadratic_QuadraticSmallTotalIdentity`, `Ostmann_Quadratic_QuadraticSquarefreePart`, `Ostmann_Quadratic_QuadraticTotientKernel`, `Ostmann_Quadratic_QuadraticTransformedMain`, `Ostmann_Quadratic_QuadraticUnitCorrectionGrowth`, `Ostmann_Quadratic_QuadraticUnitMiddleGrowth`, `Ostmann_Quadratic_QuadraticWeightedBilinear`, `Ostmann_Quadratic_QuadraticWeightedGaussBound`, `Ostmann_Quadratic_QuadraticWholeHighGrowth`, `Ostmann_Quadratic_QuadraticWholeLowGrowth`, `Ostmann_Quadratic_QuadraticWholeMiddleGrowth`, `Ostmann_Quadratic_QuadraticWholeSmallHighGrowth`, `Ostmann_Quadratic_QuadraticWholeSmallMiddleGrowth`, `Ostmann_Quadratic_QuadraticWideRows`, `Ostmann_Tree_RationalQuartetCut`, `Ostmann_Tree_RationalTree`, `Ostmann_Tree_RationalTreeLeaves`, `Ostmann_Tree_RationalTreeProfile`, `Ostmann_Tree_SampleEqualityPatterns`, `Ostmann_ZeroDensity_OriginalDensityCorrelation`, `Ostmann_ZeroDensity_RationalNodeDensity`, `Ostmann_ZeroDensity_SmoothPrimePowerRemoval`, `Ostmann_ZeroDensity_SparsePrincipalMean`.
--
--   **Imports.** It imports the bundles `OAIQ095D000`, `OAIQ095D001` and `OAIQ095D002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ095D006` and `OAIQ095D007`; the statements `OAI_Ostmann_EventuallyPrimeSumset_sparse_tail_mass_bound`, `OAI_Ostmann_PublishedProgressionInput_constructed_binned_character_priors`, `OAI_Ostmann_PublishedProgressionInput_moving_selected_initial_amplitude_energy`, `OAI_Ostmann_PublishedProgressionInput_moving_selected_initial_early_log_diagonal`, `OAI_Ostmann_PublishedProgressionInput_moving_selected_initial_full_energy`, `OAI_Ostmann_eventual_character_diagonal_decay`, `OAI_Ostmann_eventual_fixed_coefficient_moment`, `OAI.Ostmann.eventual_large_kernel_prime_moment`, `OAI_Ostmann_eventual_original_large_first_moment`, `OAI_Ostmann_eventual_uniform_character_iteration_contradiction`, `OAI_Ostmann_movingSymmetrizedTemplateCoefficient_original_initial_full_lower`, `OAI_Ostmann_movingTemplateCoefficient_original_initial_full_lower`, `OAI_Ostmann_movingTemplate_initial_symmetrized_energy_bound`, `OAI.Ostmann.quadraticBandMass_isLittleO`, `OAI.Ostmann.quadratic_first_total_growth`, `OAI.Ostmann.quadratic_full_middle_growth`, `OAI.Ostmann.quadratic_gcd_corrections_power_bound`, `OAI.Ostmann.quadratic_gcd_main_growth`, `OAI_Ostmann_quadratic_small_gcd_comparison`, `OAI_Ostmann_retained_graph_original_pair_ratio_bound`, `OAI_Ostmann_selected_natural_final_contradiction`, `OAI_Ostmann_sparse_pair_coverage_size_bound`, `OAI_Ostmann_uniform_constituent_natural_history_energy` and `OAI_Ostmann_uniform_constituent_natural_square_rate`; the proofs of `OAI_Ostmann_PublishedProgressionInput_concrete_character_band_contradiction`, `OAI_Ostmann_PublishedProgressionInput_constructed_binned_character_priors`, `OAI_Ostmann_PublishedProgressionInput_moving_selected_initial_amplitude_energy`, `OAI_Ostmann_PublishedProgressionInput_moving_selected_initial_early_log_diagonal`, `OAI_Ostmann_PublishedProgressionInput_moving_selected_initial_full_energy`, `OAI_Ostmann_eventual_character_diagonal_decay`, `OAI_Ostmann_eventual_fixed_coefficient_moment`, `OAI_Ostmann_eventual_original_large_first_moment`, `OAI.Ostmann.eventual_original_outer_first_moment`, `OAI_Ostmann_eventual_uniform_character_iteration_contradiction`, `OAI.Ostmann.exists_selected_small_primes`, `OAI.Ostmann.groupedFullCoprimeFourierWeight_coefficient`, `OAI_Ostmann_movingSymmetrizedTemplateCoefficient_original_initial_full_lower`, `OAI_Ostmann_movingTemplateCoefficient_original_initial_full_lower`, `OAI_Ostmann_movingTemplate_initial_symmetrized_energy_bound`, `OAI.Ostmann.quadraticBandMass_isLittleO`, `OAI.Ostmann.quadratic_first_total_growth`, `OAI.Ostmann.quadratic_full_middle_growth`, `OAI.Ostmann.quadratic_gcd_corrections_power_bound`, `OAI.Ostmann.quadratic_gcd_main_growth`, `OAI_Ostmann_quadratic_rough_iteration`, `OAI.Ostmann.quadratic_rough_power_growth` and `OAI_Ostmann_quadratic_small_gcd_comparison`.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ095D000
import Definitions.Def_OAIQ095D001
import Definitions.Def_OAIQ095D002

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticFrequencyTree
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full arithmetic frequency-tree budget -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def pairedFrequencyKernel (S : Finset ℤ) (D : ℝ)
    (root left right : S × S) : ℝ :=
  2 * D ^ 2 *
    (((reducedFrequency ((left.1 : ℤ).natAbs.gcd (right.1 : ℤ).natAbs) (root.1 : ℤ).natAbs).lcm
       (reducedFrequency ((left.2 : ℤ).natAbs.gcd (right.2 : ℤ).natAbs) (root.2 : ℤ).natAbs) : ℕ) : ℝ)⁻¹

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SequentialSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplying support bounds under the original independent prior

The test at a split can depend on the entire already exposed prefix. This
records the order of exposure, so future validity never changes its law.
-/

namespace Ostmann

open scoped BigOperators Classical

instance splitSamplesFintype (A : Type) [Fintype A] (n : ℕ) : Fintype (SplitSamples A n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => exact @instFintypeProd _ _ _ ih

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticSplitTreeSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplying the actual split probabilities at fixed frequencies -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def pairFrequencySupportBound (D : ℝ) (f : NodeFrequencies × NodeFrequencies) : ℝ :=
  2 * D ^ 2 / f.1.reducedModulus.lcm f.2.reducedModulus

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_OriginalDensityCorrelation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Correlation estimates for the original two divisor transforms -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable def supportCorrelationSide (U V : Finset ℕ) (p : ℕ) : CorrelationSide :=
  if p ∈ U then if p ∈ V then .both else .left else .right

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_PrimitiveKernelCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Primitive real characters representing the four signed kernel shapes -/

namespace Ostmann

noncomputable def primitiveRealOfCharacter {n : ℕ} [NeZero n]
    (χ : DirichletCharacter ℝ n) (hχ : χ ≠ 1) : PrimitiveRealCharacter where
  modulus := χ.conductor
  positive := Nat.pos_of_ne_zero χ.conductor_ne_zero
  character := χ.primitiveCharacter
  primitive := χ.primitiveCharacter_isPrimitive
  nontrivial := by
    intro h
    have he : χ = 1 := by
      rw [← χ.changeLevel_primitiveCharacter, h, map_one]
    exact hχ he

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialWeightPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual off-diagonal product of two polynomial weights -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

noncomputable def pairedPolynomialFactors {n m : ℕ}
    (F : Fin n → ClippedPolynomialFactor) (G : Fin m → ClippedPolynomialFactor) :
    Fin (n + m) → ClippedPolynomialFactor := Fin.append F (fun i => (G i).conjugate)

noncomputable def polynomialWeightComplexity {n t : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) : ℕ :=
  (∑ i, (F i).polynomial.derivative.natDegree) + ∑ i, (H i).natDegree

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeCellPartitionConstruction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the actual prime log/residue partition

The fiber identities used by the joint comparison follow from separated
log intervals and residue classes. They are not additional distribution
hypotheses.
-/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def primeCellSupport {C : Type*} [Fintype C]
    (q : ℕ) (a : C → ℕ) (s t : C → ℝ) : Finset ℕ :=
  Finset.univ.biUnion fun c => primeLogCellSet q (a c) (s c) (t c)

noncomputable def primeCellLabel {C : Type*}
    (q : ℕ) (a : C → ℕ) (s t : C → ℝ) (c₀ : C) (p : ℕ) : C :=
  if h : ∃ c, p ∈ primeLogCellSet q (a c) (s c) (t c) then h.choose else c₀

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RecursiveLeafExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact signed leaves and real support factor of a recursive history -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap FourierTransform Classical

/-- The flag records the conjugations accumulated from right branches. -/
noncomputable def transferLeafList {State : Type*} (sys : TransferHistorySystem State) :
    (n : ℕ) → State → FrequencyTree ℤ n → List ((State × ℤ) × Bool)
  | 0, σ, v => [((σ, v), true)]
  | n + 1, σ, t =>
      let P := historyPivot sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      transferLeafList sys n (sys.leftState σ P) t.2.1 ++
        (transferLeafList sys n (sys.rightState σ P) t.2.2).map (fun z => (z.1, !z.2))

/-- Leaf bins and all intermediate arithmetic/range gates are real. They
remain real under every conjugation in the frequency tree. -/
noncomputable def recursiveSupportFactor {State : Type*} (sys : TransferHistorySystem State)
    (leafCutoff : State → ℤ → ℝ) (cutoff : State → ℤ → ℤ → ℤ → ℝ) :
    (n : ℕ) → State → FrequencyTree ℤ n → ℝ
  | 0, σ, v => leafCutoff σ v
  | n + 1, σ, t =>
      let v := frequencyRoot n t.2.1
      let w := frequencyRoot n t.2.2
      let P := historyPivot sys σ t.1 v w
      if ValidTransferNode sys σ t.1 v w P then
        cutoff σ t.1 v w * recursiveSupportFactor sys leafCutoff cutoff n (sys.leftState σ P) t.2.1 *
          recursiveSupportFactor sys leafCutoff cutoff n (sys.rightState σ P) t.2.2
      else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RationalNodeDensity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The density bound for an actual reconstructed node

The fixed parent product makes its argument independent of the split.
The reconstructed entry vanishes exactly when the child ratio is one.
Thus the inverse-square density estimate applies to the actual formulas,
with the manuscript's invalid-node convention.
-/

namespace Ostmann

open scoped BigOperators

noncomputable def rationalNodeValue {p : ℕ} [Fact p.Prime]
    (s sL sR D u XL XR CL CR P : (ZMod p)ˣ)
    (f g : ZMod p → ℝ) (m : (ZMod p)ˣ) : ℝ :=
  let HL : (ZMod p)ˣ := XL * CL * m
  let HR : (ZMod p)ˣ := XR * CR * (P / m)
  let v := reconstructedEntry (s : ZMod p) sL sR u HL HR
  if v = 0 then 0 else
    f (childArgument sL D u HL v) * g (childArgument sR D u HR v)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_RationalTree
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Recursive rational tree data

The product coefficient is an index of the data type. At every split,
its child indices encode exactly the consistency conditions on the
fixed constants in `src36`.
-/

namespace Ostmann

open scoped BigOperators

noncomputable def rationalTreeMoment {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (D : (ZMod p)ˣ) :
    {n : ℕ} → {C : (ZMod p)ˣ} → RationalTreeData (ZMod p)ˣ n C →
      (ZMod p)ˣ → (ZMod p)ˣ → (ZMod p)ˣ → ℝ
  | _, _, .leaf s C, XL, XR, P => w (rationalTreeArgument s C D XL XR P)
  | _, _, .node s CL CR u left right, XL, XR, P =>
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ m : (ZMod p)ˣ,
      let HL : (ZMod p)ˣ := XL * CL * m
      let HR : (ZMod p)ˣ := XR * CR * (P / m)
      let v := reconstructedEntry (s : ZMod p) left.frequency right.frequency u HL HR
      if hv : v = 0 then 0 else
        rationalTreeMoment w D left (Units.mk0 v hv) XL m *
          rationalTreeMoment w D right (Units.mk0 v hv) XR (P / m)

/-- With the other root data fixed, exposing the total leaf product gives a uniform argument. -/
noncomputable def rationalTreeArgumentEquiv {p : ℕ} [Fact p.Prime]
    (s C D XL XR : (ZMod p)ˣ) : (ZMod p)ˣ ≃ (ZMod p)ˣ where
  toFun P := rationalTreeArgument s C D XL XR P
  invFun y := s / (D * XL * XR * C * y)
  left_inv P := by simp [rationalTreeArgument, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  right_inv y := by simp [rationalTreeArgument, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_RationalTreeLeaves
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The rational tree under independent uniform leaf sampling -/

namespace Ostmann

open scoped BigOperators

noncomputable def rationalTreeLeafValue {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (D : (ZMod p)ˣ) :
    {n : ℕ} → {C : (ZMod p)ˣ} → RationalTreeData (ZMod p)ˣ n C →
      (ZMod p)ˣ → (ZMod p)ˣ → TreeLeafTuple (ZMod p)ˣ n → ℝ
  | _, _, .leaf s C, XL, XR, m => w (rationalTreeArgument s C D XL XR m)
  | n + 1, _, .node s CL CR u left right, XL, XR, ab =>
    let HL : (ZMod p)ˣ := XL * CL * treeLeafProduct n ab.1
    let HR : (ZMod p)ˣ := XR * CR * treeLeafProduct n ab.2
    let v := reconstructedEntry (s : ZMod p) left.frequency right.frequency u HL HR
    if hv : v = 0 then 0 else
      rationalTreeLeafValue w D left (Units.mk0 v hv) XL ab.1 *
        rationalTreeLeafValue w D right (Units.mk0 v hv) XR ab.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TreeLeafIndex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Labeled leaves and bottom quartets of a full binary tree -/

namespace Ostmann

open scoped BigOperators

instance treeLeafIndexNonempty (n : ℕ) : Nonempty (TreeLeafIndex n) := by
  induction n with
  | zero => exact ⟨()⟩
  | succ n ih => exact ⟨Sum.inl (Classical.choice ih)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetSymmetry
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Interchanging the two bottom pairs

Swapping the pairs inverts the quotient character and negates additive
frequency. This supplies the right-friendly estimate from the left one.
-/

namespace Ostmann

open scoped BigOperators

attribute [local instance] OAI.Ostmann.quartetSymmetryFintype
noncomputable def quartetFourierEnergy {p : ℕ} [Fact p.Prime]
    (P Q : MulChar (ZMod p) ℂ → ZMod p → ℂ)
    (left right : Bool) (ν : MulChar (ZMod p) ℂ) : ℝ :=
  ∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
    ‖additiveFourier (fun x => P χ x * quartetLeftTwist left right ν χ ψ x) a‖ ^ 2 *
    ‖additiveFourier (fun x => Q ψ x * quartetRightTwist left right ν χ ψ x) (-a)‖ ^ 2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetFriendlyCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two-friendly orientation of an actual rational quartet -/

namespace Ostmann

open scoped BigOperators

noncomputable def quartetLeftHeld {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ) (XL : (ZMod p)ˣ) : (ZMod p)ˣ :=
  (D * Q.s₁ / (Q.s₂ * Q.sL)) * (XL * Q.C₂) ^ 2

noncomputable def quartetRightHeld {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ) (XR : (ZMod p)ˣ) : (ZMod p)ˣ :=
  (D * Q.s₃ / (Q.s₄ * Q.sR)) * (XR * Q.C₄) ^ 2

noncomputable def quartetMovingMultiplier {p : ℕ} [Fact p.Prime]
    (Q : RationalQuartetData (ZMod p)ˣ) (XL XR P a : (ZMod p)ˣ) : (ZMod p)ˣ :=
  (Q.sL / Q.sR) * (XR * Q.CR * P / (XL * Q.CL)) * (a⁻¹) ^ 2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetBadCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Shared-entry square cancellation in the bad quartet orientations -/

namespace Ostmann

noncomputable def quartetSharedConstant {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ) : (ZMod p)ˣ :=
  Q.sL * Q.sR / (Q.s * D * Q.u ^ 2)

noncomputable def quartetLeftBadHeld {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ) (XL XR P : (ZMod p)ˣ) : (ZMod p)ˣ :=
  (D * Q.s₂ / (Q.s₁ * Q.sL) * Q.C₁ ^ 2) * quartetSharedConstant D Q *
    rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P

noncomputable def quartetRightBadHeld {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ) (XL XR P : (ZMod p)ˣ) : (ZMod p)ˣ :=
  (D * Q.s₄ / (Q.s₃ * Q.sR) * Q.C₃ ^ 2) * quartetSharedConstant D Q *
    rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetOrientedValue
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All free/held orientations in the local quartet value -/

namespace Ostmann

open scoped ComplexConjugate

noncomputable def quartetLeftParameter {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ) (XL XR P : (ZMod p)ˣ)
    (friendly : Bool) (m₁ m₂ : (ZMod p)ˣ) : (ZMod p)ˣ :=
  if friendly then quartetLeftHeld D Q XL * m₂ ^ 2
  else quartetLeftBadHeld D Q XL XR P * m₁ ^ 2

noncomputable def quartetRightParameter {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ) (XL XR P : (ZMod p)ˣ)
    (friendly : Bool) (m₃ m₄ : (ZMod p)ˣ) : (ZMod p)ˣ :=
  if friendly then quartetRightHeld D Q XR * m₄ ^ 2
  else quartetRightBadHeld D Q XL XR P * m₃ ^ 2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetSamePairBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Two moving leaves in the same bottom pair of an actual quartet -/

namespace Ostmann

open scoped BigOperators

noncomputable def samePairParentMultiplier {U : Type*} [CommGroup U]
    (Q : RationalQuartetData U) (XL XR P : U) : U :=
  (Q.sL / Q.sR) * (XR * Q.CR / (XL * Q.CL * P))

noncomputable def samePairRightParentMultiplier {U : Type*} [CommGroup U]
    (Q : RationalQuartetData U) (XL XR P : U) : U :=
  (Q.sL / Q.sR) * (XR * Q.CR * P / (XL * Q.CL))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RecursiveNodeExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact preorder list of reconstructed arithmetic tests -/

namespace Ostmann

open scoped Classical

noncomputable def transferNodeList {State : Type*} (sys : TransferHistorySystem State) :
    (n : ℕ) → State → FrequencyTree ℤ n → List (ReconstructedTransferNode State)
  | 0, _, _ => []
  | n + 1, σ, t =>
      let node : ReconstructedTransferNode State :=
        ⟨σ, t.1, frequencyRoot n t.2.1, frequencyRoot n t.2.2⟩
      node :: (transferNodeList sys n (sys.leftState σ (node.pivot sys)) t.2.1 ++
        transferNodeList sys n (sys.rightState σ (node.pivot sys)) t.2.2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferGuardFamily
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One residue gate and one polynomial partition for a complete guard family -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def wordGuardNumerators {σ : Type*} {k : ℕ} (G : Fin k → WordTransferGuard σ) :
    Fin (k + k) → MvPolynomial σ ℤ :=
  Fin.append (fun i => (G i).pivot.cleared.numerator) (fun i => (G i).rightProduct.cleared.numerator)

noncomputable def wordGuardDenominators {σ : Type*} {k : ℕ} (G : Fin k → WordTransferGuard σ) :
    Fin (k + k) → ℤ :=
  Fin.append (fun i => (G i).pivot.cleared.denominator) (fun i => (G i).rightProduct.cleared.denominator)

def wordGuardModuli {σ : Type*} {k : ℕ} (G : Fin k → WordTransferGuard σ) : Fin (k + k) → ℕ :=
  Fin.append (fun i => (G i).right.natAbs) (fun i => (G i).root.natAbs)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingGiantSamples
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the moving-giant tree from the sampled compensation slots

Each reversing node samples four positions per leaf of either child. Their
products are inserted into both child regular lists. The constructor proves
the required product consistency; it does not ask for a pre-existing diagram.
-/

namespace Ostmann
open scoped BigOperators

def movingGiantFrequencyUnits (q : ℕ) : (n : ℕ) → FrequencyTree ℤ n → Prop
  | 0, t => ((frequencyRoot 0 t : ℤ) : ZMod q) ≠ 0
  | n + 1, t => (t.1 : ZMod q) ≠ 0 ∧
      movingGiantFrequencyUnits q n t.2.1 ∧ movingGiantFrequencyUnits q n t.2.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AnchorPairCode
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Anchor codes from the actual graph update -/

namespace Ostmann

theorem transferCopySign_injective : Function.Injective transferCopySign := by
  intro a b h
  cases a <;> cases b <;> simp_all [transferCopySign]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferGraphPhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identification of every surviving local factor with the new graph phase -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable def updatedGraphRow {H Y : Type*} [Fintype H] [Fintype Y] {p : ℕ}
    (χ : DirichletCharacter ℂ p) (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (i : (Bool × H) ⊕ Y) (L R : H → ZMod p) (U : Y → ZMod p) : ℂ :=
  ∏ j, χ (transferredLabels L R U j) ^ transferredGraph b i j

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FinalReassignments
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual independent, parity-preserving bulk reassignments -/

namespace Ostmann

open scoped Classical

def parityPathValue {n : ℕ} : ParityPathSum n → (Fin (n + 1) → Bool)
  | .inl t => t.val
  | .inr t => t.val

theorem parityPathValue_injective (n : ℕ) : Function.Injective (@parityPathValue n) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Subtype.ext hab)
    | inr b => have := a.property.symm.trans ((congrArg finalCopyParity hab).trans b.property); omega
  | inr a =>
    cases b with
    | inl b => have := a.property.symm.trans ((congrArg finalCopyParity hab).trans b.property); omega
    | inr b => exact congrArg Sum.inr (Subtype.ext hab)

def paritySlotPerm {n m : ℕ} (e : FinalParityReassignments n m) :
    Equiv.Perm (ParityPathSum n × Fin m) where
  toFun x := ((Equiv.sumCongr (e x.2).1 (e x.2).2) x.1, x.2)
  invFun x := ((Equiv.sumCongr (e x.2).1 (e x.2).2).symm x.1, x.2)
  left_inv x := by simp
  right_inv x := by simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RecursiveSupportExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All original range factors and all arithmetic tests in a flat history -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def transferNodeCutoff {State : Type*}
    (cutoff : State → ℤ → ℤ → ℤ → ℝ) (node : ReconstructedTransferNode State) : ℝ :=
  cutoff node.state node.root node.left node.right

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferWeightIdentity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identification of the original recursive weight with its polynomial leaves -/

namespace Ostmann

open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical

noncomputable def polynomialLeafProduct {σ : Type*}
    (leaves : List (WeightedWordLeaf σ)) (ψ : ℝ → ℂ) (X lo hi : ℝ) (x : σ → ℤ) : ℂ :=
  (leaves.map (fun z =>
    (if z.formula.realValue x / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
      normalizedFourierProfile ψ (if z.positive then (z.frequency : ℝ) else -(z.frequency : ℝ))
        (z.formula.realValue x / X))).prod

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordUnitCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact residue support for all inherited word units -/

namespace Ostmann

open scoped Classical

noncomputable def wordUnitNumerators {σ : Type*} {m : ℕ} (G : Fin m → HistoryUnitGuard σ) :=
  fun i => (G i).formula.cleared.numerator

noncomputable def wordUnitDenominators {σ : Type*} {m : ℕ} (G : Fin m → HistoryUnitGuard σ) :=
  fun i => (G i).formula.cleared.denominator

def wordUnitModuli {σ : Type*} {m : ℕ} (G : Fin m → HistoryUnitGuard σ) := fun i => (G i).modulus

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SchedulePairwiseReplay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The reduced support implies every original pairwise-coprimality gate -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def scheduleAtomPairwiseValid {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ) :
    (n : ℕ) → (CopyScheduleAtoms role n → ℕ) → FrequencyTree ℤ n → Prop
  | 0, x, _ => Pairwise (fun i j => (x i).Coprime (x j))
  | n + 1, x, t =>
      let P := historyPivot (scheduleAtomSystem role childBound pivotBound) ⟨n + 1, x⟩
        t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      Pairwise (fun i j => (x i).Coprime (x j)) ∧
        scheduleAtomPairwiseValid role childBound pivotBound n
          (reverseCopyLabelMap role n true P x) t.2.1 ∧
        scheduleAtomPairwiseValid role childBound pivotBound n
          (reverseCopyLabelMap role n false P x) t.2.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSlotSpectator
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Spectator factorization for the source moving-giant coefficient -/

namespace Ostmann
open scoped Classical

noncomputable def movingSlotSpectator {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (g : ZMod q → ℂ) (D : (ZMod q)ˣ) :
    {n : ℕ} → MovingSlotData σ n → ℕ → ℕ → ℂ
  | _, .leaf s regular, XL, XR =>
      g ((s : ZMod q) / ((D : ZMod q) *
        ((XL * XR * MovingSlotReversal.naturalProduct value regular : ℕ) : ZMod q)))
  | _, .node s CL CR u left right, XL, XR =>
      let p := (MovingSlotData.step s CL CR u left right false).naturalPivot value XL XR
      if (p : ZMod q) = 0 then 0 else
        movingSlotSpectator value g D left p XL * star (movingSlotSpectator value g D right p XR)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TreeProfile
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonuniform nonnegative weights at a horizontal level of the tree -/

namespace Ostmann

open scoped BigOperators

def treeWeightsNonneg {p : ℕ} : (n : ℕ) → TreeLeafTuple (ZMod p → ℝ) n → Prop
  | 0, w => ∀ x, 0 ≤ w x
  | n + 1, w => treeWeightsNonneg n w.1 ∧ treeWeightsNonneg n w.2

noncomputable def treeProfileMean {p : ℕ} [Fact p.Prime] :
    (n : ℕ) → TreeLeafTuple (ZMod p → ℝ) n → ℝ
  | 0, w => (∑ x : (ZMod p)ˣ, w x) / (Fintype.card (ZMod p)ˣ : ℝ)
  | n + 1, w => treeProfileMean n w.1 * treeProfileMean n w.2

noncomputable def treeProfileMajorant {p : ℕ} [Fact p.Prime] :
    (n : ℕ) → TreeLeafTuple (ZMod p → ℝ) n → ZMod p → ℝ
  | 0, w, d => if d = 0 then 0 else w d
  | n + 1, w, d => if d = 0 then 0 else
      (2 / (Fintype.card (ZMod p)ˣ : ℝ)) *
        differenceMoment (treeProfileMajorant n w.1) (treeProfileMajorant n w.2) d

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_RationalTreeProfile
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual rational tree with different weights at a horizontal level -/

namespace Ostmann

open scoped BigOperators

noncomputable def rationalProfileMoment {p : ℕ} [Fact p.Prime] (D : (ZMod p)ˣ) :
    {n : ℕ} → {C : (ZMod p)ˣ} → RationalTreeData (ZMod p)ˣ n C →
      TreeLeafTuple (ZMod p → ℝ) n → (ZMod p)ˣ → (ZMod p)ˣ → (ZMod p)ˣ → ℝ
  | _, _, .leaf s C, w, XL, XR, P => w (rationalTreeArgument s C D XL XR P)
  | _, _, .node s CL CR u left right, w, XL, XR, P =>
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ m : (ZMod p)ˣ,
      let HL : (ZMod p)ˣ := XL * CL * m
      let HR : (ZMod p)ˣ := XR * CR * (P / m)
      let v := reconstructedEntry (s : ZMod p) left.frequency right.frequency u HL HR
      if hv : v = 0 then 0 else
        rationalProfileMoment D left w.1 (Units.mk0 v hv) XL m *
          rationalProfileMoment D right w.2 (Units.mk0 v hv) XR (P / m)

noncomputable def rationalProfileLeafValue {p : ℕ} [Fact p.Prime] (D : (ZMod p)ˣ) :
    {n : ℕ} → {C : (ZMod p)ˣ} → RationalTreeData (ZMod p)ˣ n C →
      TreeLeafTuple (ZMod p → ℝ) n → (ZMod p)ˣ → (ZMod p)ˣ →
        TreeLeafTuple (ZMod p)ˣ n → ℝ
  | _, _, .leaf s C, w, XL, XR, m => w (rationalTreeArgument s C D XL XR m)
  | n + 1, _, .node s CL CR u left right, w, XL, XR, ab =>
    let HL : (ZMod p)ˣ := XL * CL * treeLeafProduct n ab.1
    let HR : (ZMod p)ˣ := XR * CR * treeLeafProduct n ab.2
    let v := reconstructedEntry (s : ZMod p) left.frequency right.frequency u HL HR
    if hv : v = 0 then 0 else
      rationalProfileLeafValue D left w.1 (Units.mk0 v hv) XL ab.1 *
        rationalProfileLeafValue D right w.2 (Units.mk0 v hv) XR ab.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_RationalQuartetCut
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cutting an actual rational tree at its bottom quartets

The option-valued state records ancestor validity. On a valid cut each
state contains the original depth-two tree and its propagated current
entries. No quartet replacement or independence hypothesis is used.
-/

namespace Ostmann

open scoped BigOperators

noncomputable def rationalQuartetStates {p : ℕ} [Fact p.Prime] :
    (n : ℕ) → {C : (ZMod p)ˣ} → RationalTreeData (ZMod p)ˣ (n + 2) C →
      (ZMod p)ˣ → (ZMod p)ˣ → TreeLeafTuple Bool (n + 2) →
      TreeLeafTuple (ZMod p)ˣ n → Option (TreeLeafTuple (RationalQuartetState p) n)
  | 0, C, T, XL, XR, c, _ => some ⟨C, T, XL, XR, c⟩
  | n + 1, _, .node s CL CR u left right, XL, XR, c, P =>
    let HL := XL * CL * treeLeafProduct n P.1
    let HR := XR * CR * treeLeafProduct n P.2
    let v := reconstructedEntry (s : ZMod p) left.frequency right.frequency u HL HR
    if hv : v = 0 then none else do
      let L ← rationalQuartetStates n left (Units.mk0 v hv) XL c.1 P.1
      let R ← rationalQuartetStates n right (Units.mk0 v hv) XR c.2 P.2
      pure (L, R)

def quartetCutValue {A B R : Type*} [Zero R] [Mul R] (f : A → B → R) (n : ℕ)
    (states : Option (TreeLeafTuple A n)) (b : TreeLeafTuple B n) : R :=
  match states with
  | none => 0
  | some a => treeLeafZipProduct f n a b

noncomputable def rationalQuartetStateAmplitude {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (S : RationalQuartetState p)
    (m : TreeLeafTuple (ZMod p)ˣ 2) : ℂ :=
  rationalTreeAmplitude g D S.tree S.XL S.XR S.conjugations m

noncomputable def rationalQuartetStateArgument {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (S : RationalQuartetState p) (P : (ZMod p)ˣ) : (ZMod p)ˣ :=
  rationalTreeArgument S.tree.frequency S.C D S.XL S.XR P

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFourierFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial smooth factors in the full moving-giant coefficient -/

namespace Ostmann
open scoped Classical ComplexConjugate

noncomputable def movingPolynomialFourierTree {σ : Type*}
    (value : σ → ℕ) (ψ : ℝ → ℂ) (X z : ℝ) :
    {n : ℕ} → MovingSlotData σ n → Polynomial ℝ → Polynomial ℝ → ℂ
  | _, .leaf s regular, L, R =>
      normalizedFourierProfile ψ s
        ((L * R * Polynomial.C (MovingSlotReversal.naturalProduct value regular : ℝ)).eval z / X)
  | _, .node s CL CR u left right, L, R =>
      let p := (MovingSlotData.step s CL CR u left right false).pivotPolynomial value L R
      movingPolynomialFourierTree value ψ X z left p L *
        star (movingPolynomialFourierTree value ψ X z right p R)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSupportWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the exact arithmetic indicator from the recursive weight -/

namespace Ostmann
open scoped Classical

/-- Evaluation along the forced integer pivots with just the arithmetic
indicators removed. The same leaf and node factors remain. -/
noncomputable def movingUnrestrictedWeight {σ : Type*} (value : σ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ)
    (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ) :
    {n : ℕ} → MovingSlotData σ n → ℕ → ℕ → ℂ
  | _, .leaf s regular, XL, XR => F ⟨0, .leaf s regular, XL, XR⟩ s
  | n + 1, .node s CL CR u left right, XL, XR =>
      let p := (MovingSlotData.step s CL CR u left right false).naturalPivot value XL XR
      (extra ⟨n + 1, .node s CL CR u left right, XL, XR⟩ s left.frequency right.frequency : ℂ) *
        movingUnrestrictedWeight value F extra left p XL *
        star (movingUnrestrictedWeight value F extra right p XR)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSpectatorCongruence
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Residue constancy of the actual moving spectator recursion

The extra denominator clears the integer divisions along both children.
No coprimality between a spectator prime and a node frequency is required.
-/

namespace Ostmann
open scoped Classical

def movingSpectatorDenominator {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℤ
  | _, .leaf _ _ => 1
  | _, .node s _ _ U left right =>
      s * (MovingSlotReversal.naturalProduct value U : ℤ) *
        movingSpectatorDenominator value left * movingSpectatorDenominator value right

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRealResidues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the original arithmetic gate into residues and real inequalities -/

namespace Ostmann
open scoped Classical

noncomputable def movingResidueGate (nodes : List MovingFormulaNode) (a : Bool → ℤ) : Prop :=
  ∀ f ∈ nodes, f.residueTests a ∧ f.guard.frequencyBounds

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSignedSpectator
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Signed residue representatives for the literal spectator recursion -/

namespace Ostmann
open scoped Classical

noncomputable def movingSignedSpectator {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (g : ZMod q → ℂ) (D : (ZMod q)ˣ) :
    {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℂ
  | _, .leaf s regular, XL, XR =>
      g ((s : ZMod q) / ((D : ZMod q) *
        ((XL * XR * (MovingSlotReversal.naturalProduct value regular : ℤ) : ℤ) : ZMod q)))
  | _, .node s CL CR U left right, XL, XR =>
      let p := (MovingSlotData.step s CL CR U left right false).signedPivot value XL XR
      if (p : ZMod q) = 0 then 0 else
        movingSignedSpectator value g D left p XL * star (movingSignedSpectator value g D right p XR)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingResidueFactorization
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed residue factors separated from the real moving support -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingResidueFlag (nodes : List MovingFormulaNode) (a : Bool → ℤ) : ℂ :=
  if movingResidueGate nodes a then 1 else 0

noncomputable def movingSpectatorResidue {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (g : ∀ i, ZMod (q i) → ℂ)
    (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I) {n : ℕ} (T : MovingSlotData σ n)
    (a b : ℤ) : ℂ := ∏ i ∈ S, movingSignedSpectator value (g i) (D i) T a b

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCutoffPolynomials
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All actual logarithmic node cutoffs as polynomial factors -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingRealNodeCutoff {σ : Type*} (value : σ → ℕ) (φ : ℝ → ℝ) (G : ℕ → ℝ) :
    {n : ℕ} → MovingSlotData σ n → ℝ → ℝ → ℂ
  | _, .leaf _ _, _, _ => 1
  | n + 1, .node s CL CR u left right, L, R =>
      let p := (MovingSlotData.step s CL CR u left right false).realPivot value L R
      (positiveLogCutoff φ (G (n + 1)) p : ℂ) *
        movingRealNodeCutoff value φ G left p L * movingRealNodeCutoff value φ G right p R

noncomputable def movingNodeCutoffFactors {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) :
    Fin (T.nodeCutoffPolynomials value L R).length → ClippedPolynomialFactor := fun i =>
  let f := (T.nodeCutoffPolynomials value L R)[i]
  logCutoffPolynomialFactor f.2 φ (G f.1) B D hB hD hφ hlip

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingNodeCutoffFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Keeping the original logarithmic cutoff in every moving node -/

namespace Ostmann
open scoped Classical

noncomputable def movingNaturalNodeCutoff {σ : Type*} (value : σ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) : {n : ℕ} → MovingSlotData σ n → ℕ → ℕ → ℂ
  | _, .leaf _ _, _, _ => 1
  | n + 1, .node s CL CR u left right, L, R =>
      let p := (MovingSlotData.step s CL CR u left right false).naturalPivot value L R
      (positiveLogCutoff φ (G (n + 1)) p : ℂ) *
        movingNaturalNodeCutoff value φ G left p L * movingNaturalNodeCutoff value φ G right p R

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRealWindows
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The terminal-window factor on two real giant coordinates -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingRealWindowFlag {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (X lo hi XL XR : ℝ) : ℂ :=
  if ∀ i, T.realLeafModuli value XL XR i / X ∈ Set.Icc lo hi then 1 else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkPrimeAtoms
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Expanding the actual joint prime cells on the common sample space -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

noncomputable def primeCellAtomWeight (q a : ℕ) (u v : ℝ) (p : ℕ) : ℝ :=
  if p ∈ primeLogCellSet q a u v then (p : ℝ)⁻¹ else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SquareLiftExclusions
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dropping the prime-square exclusions in a two-history expansion -/

namespace Ostmann

open scoped BigOperators

def zeroLiftEquiv {p : ℕ} (a : (ZMod (p ^ 2))ˣ)
    (b : ZMod (p ^ 2)) (x₀ y₀ : ZMod p) :
    {v : SquareLiftPairs p x₀ y₀ // (a : ZMod (p ^ 2)) * v.1.1 + b * v.2.1 = 0} ≃
    {xy : ZMod (p ^ 2) × ZMod (p ^ 2) //
      squareReduction p xy.1 = x₀ ∧ squareReduction p xy.2 = y₀ ∧
        (a : ZMod (p ^ 2)) * xy.1 + b * xy.2 = 0} where
  toFun v := ⟨(v.1.1, v.1.2), v.1.1.property, v.1.2.property, v.property⟩
  invFun v := ⟨(⟨v.1.1, v.property.1⟩, ⟨v.1.2, v.property.2.1⟩), v.property.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- All forbidden prime-square zeros, one for each occurrence of the prime. -/
noncomputable def squareLiftBad {I : Type*} [Fintype I] {p : ℕ} [Fact p.Prime]
    (a : I → (ZMod (p ^ 2))ˣ) (b : I → ZMod (p ^ 2)) (x₀ y₀ : ZMod p) :
    Finset (SquareLiftPairs p x₀ y₀) := by
  classical
  exact Finset.univ.filter fun v => ∃ i, (a i : ZMod (p ^ 2)) * v.1.1 + b i * v.2.1 = 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOutsideResidues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Outside giant-unit tests in spectator coordinates -/

namespace Ostmann
open scoped Classical

def movingSignedOutsideUnits {σ : Type*} (value : σ → ℕ) (M : ℤ) :
    {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → Prop
  | _, .leaf _ _, x, y => IsCoprime x M ∧ IsCoprime y M
  | _, .node s CL CR U left right, x, y =>
      let p := (MovingSlotData.step s CL CR U left right false).signedPivot value x y
      (IsCoprime x M ∧ IsCoprime y M) ∧
        movingSignedOutsideUnits value M left p x ∧ movingSignedOutsideUnits value M right p y

def movingModularGiantUnits {σ : Type*} (value : σ → ℕ) (q : ℕ) [Fact q.Prime] :
    {n : ℕ} → MovingSlotData σ n → ZMod q → ZMod q → Prop
  | _, .leaf _ _, x, y => x ≠ 0 ∧ y ≠ 0
  | _, .node s CL CR U left right, x, y =>
      let p := (MovingSlotData.step s CL CR U left right false).modularPivot value q x y
      (x ≠ 0 ∧ y ≠ 0) ∧
        movingModularGiantUnits value q left p x ∧ movingModularGiantUnits value q right p y

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed coordinates for the actual internal prime samples

The coordinates count each sample when it is made, not its later occurrences
in descendant lists. Their number is independent of the number of bulk slots.
-/

namespace Ostmann
open scoped Classical BigOperators

instance movingSampleIndexFintype : (n : ℕ) → Fintype (MovingSampleIndex n)
  | 0 => inferInstanceAs (Fintype Empty)
  | n + 1 => @instFintypeSum _ _ inferInstance
      (@instFintypeProd _ _ inferInstance (movingSampleIndexFintype n))

def movingSampleTier : {n : ℕ} → MovingSampleIndex n → ℕ
  | n + 1, .inl _ => n
  | _ + 1, .inr (_, i) => movingSampleTier i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_SampleEqualityPatterns
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact decomposition of finite samples by equality pattern -/

namespace Ostmann
open scoped Classical BigOperators

/-- Every sample has a unique equality pattern and a unique injective assignment
of values to its classes. -/
noncomputable def sampleEqualityPatternEquiv (I A : Type*) :
    SampleEqualityPattern I A ≃ (I → A) :=
  Equiv.ofBijective SampleEqualityPattern.evaluate ⟨by
    rintro ⟨s, x⟩ ⟨t, y⟩ h
    have hs : s = t := (SampleEqualityPattern.kernel_evaluate ⟨s, x⟩).symm.trans
      ((congrArg Setoid.ker h).trans (SampleEqualityPattern.kernel_evaluate ⟨t, y⟩))
    cases hs
    congr 1
    apply Subtype.ext
    funext q
    induction q using Quotient.inductionOn with
    | _ i => exact congrFun h i,
    fun x => ⟨⟨Setoid.ker x, ⟨Setoid.kerLift x, Setoid.kerLift_injective x⟩⟩, rfl⟩⟩

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

theorem treeLeafMap_list_comp {A B C : Type*} (f : A → B) (g : B → C)
    (n : ℕ) (x : TreeLeafTuple (List A) n) :
    treeLeafMap (List.map g) n (treeLeafMap (List.map f) n x) =
      treeLeafMap (List.map (g ∘ f)) n x := by
  induction n with
  | zero => exact List.map_map
  | succ n ih => exact Prod.ext (ih x.1) (ih x.2)

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

theorem movingPairRepresentative_map_nonempty {σ τ : Type*} (f : σ → τ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (i : σ)
    (base : MovingPairRepresentativeOccurrences T i) :
    Nonempty (MovingPairRepresentativeOccurrences (fun b => (T b).map f) (f i)) := by
  let o := (T base.1).occurrences.get base.2.val
  have ho : o.map f ∈ ((T base.1).map f).occurrences := by
    rw [MovingSlotData.occurrences_map]
    exact List.mem_map.mpr ⟨o, List.get_mem _ _, rfl⟩
  have hi : f i ∈ (o.map f).current.compensationSlots :=
    List.mem_map.mpr ⟨i, base.2.property, rfl⟩
  obtain ⟨k, hk, hko⟩ := List.mem_iff_getElem.mp ho
  refine ⟨⟨base.1, ⟨⟨k, hk⟩, ?_⟩⟩⟩
  simpa only [List.get_eq_getElem, hko] using hi

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingIndexedLineSystem
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed finite index for every representative's actual line system -/

namespace Ostmann
open scoped Classical BigOperators

/-- Indices outside a representative's system repeat its selected base row.
Thus every representative uses the same finite index without changing any test. -/
noncomputable def movingRepresentativeIndex {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) (rep : σ) (base : MovingPairRepresentativeOccurrences T rep)
    (o : MovingPairOccurrenceIndex T) : MovingPairRepresentativeOccurrences T rep :=
  if h : rep ∈ ((T o.1).occurrences.get o.2).current.compensationSlots then
    ⟨o.1, ⟨o.2, h⟩⟩ else base

noncomputable def movingIndexedOccurrence {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) (rep : σ) (base : MovingPairRepresentativeOccurrences T rep)
    (o : MovingPairOccurrenceIndex T) : MovingSlotOccurrence σ :=
  let j := movingRepresentativeIndex T rep base o
  (T j.1).occurrences.get j.2.val

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SingleFrequencyTree
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The frequency budget for one squared history

Unlike a pair of histories, this sum has exactly one frequency at each leaf.
This is needed before the level-zero square-weight cancellation.
-/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def singleFrequencyKernel (S : Finset ℤ) (D : ℝ)
    (root left right : S) : ℝ :=
  2 * D ^ 2 / reducedFrequency ((left : ℤ).natAbs.gcd (right : ℤ).natAbs) (root : ℤ).natAbs

noncomputable def singleFrequencySupportBound (D : ℝ) (f : NodeFrequencies) : ℝ :=
  2 * D ^ 2 / f.reducedModulus

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferCharacterProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete multiplicative phase and unary update on actual prime lists -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

section
variable {H Y : Type*} [Fintype H] [Fintype Y]
variable (L R : H → ℕ) (U : Y → ℕ)
variable [∀ h, Fact (L h).Prime] [∀ h, Fact (R h).Prime] [∀ y, Fact (U y).Prime]

noncomputable def transferredCharacterFactor
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (νL νR : H → ℂ) (νYL νYR : Y → ℂ) (v w s : ℤ) : (Bool × H) ⊕ Y → ℂ
  | .inl (true, h) =>
      (νL h * χH h (L h) ((v : ZMod (L h)) / (s : ZMod (L h))) ^ b (some (.inl h)) none) *
        updatedGraphRow (χH h (L h)) b (.inl (true, h))
          (fun k => (L k : ZMod (L h))) (fun k => (R k : ZMod (L h))) (fun y => (U y : ZMod (L h)))
  | .inl (false, h) =>
      (conj (νR h) * χH h (R h) ((-w : ZMod (R h)) / (s : ZMod (R h))) ^ (-b (some (.inl h)) none)) *
        updatedGraphRow (χH h (R h)) b (.inl (false, h))
          (fun k => (L k : ZMod (R h))) (fun k => (R k : ZMod (R h))) (fun y => (U y : ZMod (R h)))
  | .inr y => (νYL y * conj (νYR y)) *
      updatedGraphRow (χY y (U y)) b (.inr y)
        (fun k => (L k : ZMod (U y))) (fun k => (R k : ZMod (U y))) (fun z => (U z : ZMod (U y)))

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledPriorFubini
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact decomposition of the original prior at a scheduled pivot -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def scheduledPartitionAssignment {I A : Type*}
    (role : I → CopyScheduleRole) (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n)
    (u : CopyScheduleY role n → A) (x : Fin r → A) (l : CopyScheduleH role n → A) :
    {i : CopyScheduleVertex I n // CopyScheduleSurvives role n i} → A :=
  fun i => Sum.elim x (Sum.elim l u) ((enumeratedPartitionEquiv role n r e).symm i)

theorem scheduledPartitionAssignment_apply {I A : Type*}
    (role : I → CopyScheduleRole) (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n)
    (u : CopyScheduleY role n → A) (x : Fin r → A) (l : CopyScheduleH role n → A)
    (j : Fin r ⊕ (CopyScheduleH role n ⊕ CopyScheduleY role n)) :
    scheduledPartitionAssignment role n r e u x l (enumeratedPartitionEquiv role n r e j) =
      Sum.elim x (Sum.elim l u) j := by
  simp only [scheduledPartitionAssignment, Equiv.symm_apply_apply]

noncomputable def scheduledPartitionAssignmentEquiv {I A : Type*}
    (role : I → CopyScheduleRole) (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n) :
    ((CopyScheduleY role n → A) × ((Fin r → A) × (CopyScheduleH role n → A))) ≃
      ({i : CopyScheduleVertex I n // CopyScheduleSurvives role n i} → A) where
  toFun a := scheduledPartitionAssignment role n r e a.1 a.2.1 a.2.2
  invFun a := ((fun y => a (enumeratedPartitionEquiv role n r e (.inr (.inr y)))),
    (fun i => a (enumeratedPartitionEquiv role n r e (.inl i))),
    (fun h => a (enumeratedPartitionEquiv role n r e (.inr (.inl h)))))
  left_inv a := by
    apply Prod.ext
    · funext y
      exact scheduledPartitionAssignment_apply role n r e a.1 a.2.1 a.2.2 (.inr (.inr y))
    · apply Prod.ext
      · funext i
        exact scheduledPartitionAssignment_apply role n r e a.1 a.2.1 a.2.2 (.inl i)
      · funext h
        exact scheduledPartitionAssignment_apply role n r e a.1 a.2.1 a.2.2 (.inr (.inl h))
  right_inv a := by
    funext j
    obtain ⟨i, rfl⟩ := (enumeratedPartitionEquiv role n r e).surjective j
    dsimp only
    rw [scheduledPartitionAssignment_apply]
    rcases i with i | h | y <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentPivotEnumeration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete pivot enumeration and its exact harmonic-prior dimension -/

namespace Ostmann

/-- A single pivot atom contributes exactly its original number of prime
constituents, even after the earlier copy steps. -/
noncomputable def pivotConstituentEquiv {I : Type*}
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ) (p : I)
    (hp : role p = .pivot n) (hu : ∀ i, role i = .pivot n → i = p) :
    Fin (size p) ≃ CurrentPivotConstituent (fun i : Σ a, Fin (size a) => role i.1) n :=
  Equiv.ofBijective (fun k => ⟨⟨p, k⟩, hp⟩) (by
    constructor
    · intro i j he
      have he' : (⟨p, i⟩ : Σ a, Fin (size a)) = ⟨p, j⟩ := congrArg Subtype.val he
      exact eq_of_heq (Sigma.mk.inj_iff.mp he').2
    · rintro ⟨⟨i, k⟩, hi⟩
      have he : i = p := hu i hi
      subst i
      exact ⟨k, rfl⟩)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledInputPhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual current phase under independent pivot/H/Y assignments -/

namespace Ostmann

open scoped BigOperators Classical

theorem scheduledInputPrimeFact {I : Type*} (role : I → CopyScheduleRole)
    (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n)
    (P : Fin r → ℕ) (L : CopyScheduleH role n → ℕ) (U : CopyScheduleY role n → ℕ)
    [hp : ∀ i, Fact (P i).Prime] [hl : ∀ i, Fact (L i).Prime] [hu : ∀ i, Fact (U i).Prime] :
    ∀ i, Fact (scheduledInputLabels role n r e P L U i).Prime := by
  intro i
  unfold scheduledInputLabels
  rcases (enumeratedPartitionEquiv role n r e).symm i with p | h | y
  · exact hp p
  · exact hl h
  · exact hu y

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

theorem scheduledFrequencyHistory_injective (V : ℕ → ℕ) (n : ℕ) :
    Function.Injective (scheduledFrequencyHistory V n) := by
  induction n with
  | zero => exact Subtype.val_injective
  | succ n ih =>
    intro a b he
    have hr : a.1 = b.1 := Subtype.ext (congrArg Prod.fst he)
    have hl := ih (congrArg (fun x : FrequencyTree ℤ (n + 1) => x.2.1) he)
    have hright := ih (congrArg (fun x : FrequencyTree ℤ (n + 1) => x.2.2) he)
    exact Prod.ext hr (Prod.ext hl hright)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SplitSampleLists
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The checked split-coordinate equivalence records actual product splits -/

namespace Ostmann

@[implicit_reducible] def splitSampleList {G : Type} : (n : ℕ) → SplitSamples G n → List G
  | 0, _ => []
  | n + 1, x => x.1 :: splitSampleList n x.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SampledHistoryEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The squared-history sum with its constructed arithmetic support -/

namespace Ostmann

open scoped BigOperators Classical

theorem treeIntegerResidues_prime_sample (P : Finset ℕ) (Q n : ℕ)
    (hunit : ∀ p : P, (p : ℕ).Coprime Q) (x : TreeLeafTuple P n) :
    treeIntegerResidues Q n
      (treeLeafMap (fun p : P => ((p : ℕ) : ℤ)) n x)
      (treeLeafMap (fun p : P => ZMod.unitOfCoprime (p : ℕ) (hunit p)) n x) := by
  induction n with
  | zero =>
    simpa only [treeIntegerResidues, treeLeafMap, Int.cast_natCast] using
      ZMod.coe_unitOfCoprime (n := Q) (Subtype.val (show P from x)) (hunit x)
  | succ n ih => exact ⟨ih x.1, ih x.2⟩

noncomputable def sampledPrimeHistory (P : Finset ℕ) (Q n : ℕ)
    (hunit : ∀ p : P, (p : ℕ).Coprime Q) (x : TreeLeafIndex n → P)
    (pivots : Fin (2 ^ n - 1) → ℤ) : SampledPivotHistory n Q where
  bulk := treeLeafMap (fun p : P => ((p : ℕ) : ℤ)) n ((treeLeafTupleEquiv P n).symm x)
  residue := treeLeafMap (fun p : P => ZMod.unitOfCoprime (p : ℕ) (hunit p)) n
    ((treeLeafTupleEquiv P n).symm x)
  pivots := pivots
  compatible := treeIntegerResidues_prime_sample P Q n hunit _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PreorderTransferPaths
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual reconstructed node at a preorder path -/

namespace Ostmann
open scoped Classical

noncomputable def transferNodeAtPath {State : Type*} (sys : TransferHistorySystem State) :
    (n : ℕ) → State → FrequencyTree ℤ n → List Bool → ReconstructedTransferNode State
  | 0, σ, t, _ => ⟨σ, t, t, t⟩
  | n + 1, σ, t, [] => ⟨σ, t.1, frequencyRoot n t.2.1, frequencyRoot n t.2.2⟩
  | n + 1, σ, t, b :: path =>
      let P := historyPivot sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      if b then transferNodeAtPath sys n (sys.rightState σ P) t.2.2 path
      else transferNodeAtPath sys n (sys.leftState σ P) t.2.1 path

noncomputable def replayNodeIndices {State : Type*} (sys : TransferHistorySystem State) :
    List Bool → ℕ → (ℕ → ℕ) → State → State
  | [], _, _, σ => σ
  | b :: path, d, p, σ => replayNodeIndices sys path (d + 1) p
      (if b then sys.rightState σ (p d) else sys.leftState σ (p d))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ReverseAtomSources
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Distinct sources in the actual reverse atom substitution -/

namespace Ostmann
open scoped Classical

/-- None is the newly reconstructed pivot. Every other atom reads one
particular copied or retained atom from the parent assignment. -/
noncomputable def reverseAtomSource {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) : CopyScheduleAtoms role n → Option (CopyScheduleAtoms role (n + 1)) :=
  reverseCopyLabelMap role n b none some

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

def scheduledReversePath (n : ℕ) (j : Fin (2 ^ n - 1)) :
    Fin (preorderNodePath n j).length → Bool :=
  fun a => !((preorderNodePath n j)[a.val])

noncomputable def nodeAncestorValues {A : Type*} [Zero A] (n : ℕ) (j : Fin (2 ^ n - 1))
    (p : Fin (2 ^ n - 1) → A) (k : ℕ) : A :=
  if hk : k < (preorderNodePath n j).length then p (ancestorNodeIndex n j ⟨k, hk⟩) else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledPreorderNodes
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preorder pivots reproduce the literal scheduled atom assignments -/

namespace Ostmann
open scoped Classical

noncomputable def transferNodeArray {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) (j : Fin (2 ^ n - 1)) :
    ReconstructedTransferNode State :=
  (transferNodeList sys n σ t).getD j.val ⟨σ, 0, 0, 0⟩

noncomputable def transferPivotArray {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) : Fin (2 ^ n - 1) → ℕ :=
  fun j => (transferNodeArray sys n σ t j).pivot sys

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

def movingRootState {σ : Type*} (n : ℕ) (t : FrequencyTree ℤ (n + 1))
    (CL CR u : List σ) (XL XR : ℕ) : MovingSlotState σ :=
  ⟨n + 1, .node t.1 CL CR u
    (movingFrequencySkeleton σ n t.2.1) (movingFrequencySkeleton σ n t.2.2), XL, XR⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFrequencyCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the actual sampled coefficient over its internal frequencies -/

namespace Ostmann
open scoped Classical BigOperators

def scheduledFrequencyRootEquiv (V : ℕ → ℕ) (n : ℕ) :
    ScheduledFrequencyIndex V n ≃ transferFrequencyRange (V n) × MovingDescendantFrequencyIndex V n := by
  cases n with
  | zero => exact (Equiv.prodUnique _ Unit).symm
  | succ n => exact Equiv.refl _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFrequencyPrimeSquare
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual coefficient square inside the original two prime intervals -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap ComplexConjugate

/-- Two descendant histories in a coefficient square share their root.
Their inclusion in the full pair of scheduled histories is injective. -/
def sameRootScheduledPairEmbedding (V : ℕ → ℕ) (n : ℕ) :
    (transferFrequencyRange (V n) ×
      (MovingDescendantFrequencyIndex V n × MovingDescendantFrequencyIndex V n)) ↪
    (ScheduledFrequencyIndex V n × ScheduledFrequencyIndex V n) where
  toFun a := ((scheduledFrequencyRootEquiv V n).symm (a.1, a.2.1),
    (scheduledFrequencyRootEquiv V n).symm (a.1, a.2.2))
  inj' := by
    intro a b h
    have hl := congrArg (scheduledFrequencyRootEquiv V n) (congrArg Prod.fst h)
    have hr := congrArg (scheduledFrequencyRootEquiv V n) (congrArg Prod.snd h)
    simp only [Equiv.apply_symm_apply] at hl hr
    apply Prod.ext
    · exact congrArg (fun t : transferFrequencyRange (V n) ×
        MovingDescendantFrequencyIndex V n => t.1) hl
    · apply Prod.ext
      · exact congrArg (fun t : transferFrequencyRange (V n) ×
          MovingDescendantFrequencyIndex V n => t.2) hl
      · exact congrArg (fun t : transferFrequencyRange (V n) ×
          MovingDescendantFrequencyIndex V n => t.2) hr

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetConjugation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent opposite conjugations on the two bottom sibling pairs -/

namespace Ostmann

open scoped ComplexConjugate

noncomputable def rationalQuartetPairsValue {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR m₁ m₂ m₃ m₄ : (ZMod p)ˣ) : ℂ :=
  let HL := XL * Q.CL * (m₁ * m₂)
  let HR := XR * Q.CR * (m₃ * m₄)
  let v := reconstructedEntry (Q.s : ZMod p) Q.sL Q.sR Q.u HL HR
  if hv : v = 0 then 0 else
    let V := Units.mk0 v hv
    fieldBottomPairValue g (rationalTreeArgument Q.sL (Q.u * Q.CL) D V XL (m₁ * m₂))
      (((Q.s₁ / Q.s₂) * ((XL * Q.C₂ * m₂) / (V * Q.C₁ * m₁)) : (ZMod p)ˣ) : ZMod p) *
    fieldBottomPairValue h (rationalTreeArgument Q.sR (Q.u * Q.CR) D V XR (m₃ * m₄))
      (((Q.s₃ / Q.s₄) * ((XR * Q.C₄ * m₄) / (V * Q.C₃ * m₃)) : (ZMod p)ˣ) : ZMod p)

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

def movingPatternBulkEmbedding {B C : Type*} {N : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    {n m : ℕ} (slot : (TreeLeafIndex n × Fin m) ↪ B) :
    (TreeLeafIndex n × Fin m) ↪ Fin (N + 1) where
  toFun j := e.symm (.inl (slot j))
  inj' := fun _ _ h => slot.injective (Sum.inl.inj (e.symm.injective h))

def movingPatternFiniteSmall {B C : Type*} {N : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (n : ℕ) (small : TreeLeafTuple (List B) n) : TreeLeafTuple (List (Fin (N + 1))) n :=
  treeLeafMap (List.map (fun b => e.symm (.inl b))) n small

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternBulkFrozen
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original pattern has fixed nonbulk data under bulk resampling -/

namespace Ostmann
open scoped Classical

theorem movingPatternBulkEmbedding_internal_absent {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (slot : (TreeLeafIndex n × Fin m) ↪ B) (c : C) :
    e.symm (.inr c) ∉ Set.range (movingPatternBulkEmbedding e slot) := by
  rintro ⟨j, hj⟩
  have h := e.symm.injective hj
  cases h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingGiantPhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two original giant Fourier phases on a fixed product fibre -/

namespace Ostmann
open scoped Classical BigOperators

/-- The two giant factors of Section 7.4, evaluated at their exact cofactors.
The definition also applies to the integer giant in a transfer diagonal. -/
noncomputable def movingGiantPhase {σ B : Type*} {n : ℕ}
    (value : σ → ℕ) (outside : List ℕ) (small bulk : TreeLeafTuple (List B) n)
    (g : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (s : ℤ) (y : B → σ) (x z : ℝ) : ℂ :=
  giantPairPhase g favorable outside.prod
    (MovingSlotReversal.naturalProduct (value ∘ y)
      (flattenMovingSlots n small ++ flattenMovingSlots n bulk))
    ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊ s

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeExternalAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing from the integer/prime comparison law to two prime giants -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def primeExternalAverage {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v r w : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) : ℂ :=
  ∑ s : transferFrequencyRange N, ∑ y : B → A, ((∏ b, ν b (y b) : ℝ) : ℂ) *
    complexPrimeInterval 1 0 r w (fun z =>
      complexPrimeInterval 1 0 u v (fun x => F s.val y x z))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothGiantExternalAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two original normalized giant priors in the exterior average -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def smoothGiantExternalAverage {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (φ : ℝ → ℝ) (G H : ℝ)
    (F : ℤ → (B → A) → ℕ → ℕ → ℂ) : ℂ :=
  ∑ s : transferFrequencyRange N, ∑ y : B → A, ((∏ i, ν i (y i) : ℝ) : ℂ) *
    ∑ q : smoothGiantPrimeRange H, (smoothGiantPrior (smoothGiantPrimeRange H) φ H q : ℂ) *
      ∑ p : smoothGiantPrimeRange G, (smoothGiantPrior (smoothGiantPrimeRange G) φ G p : ℂ) *
        F s.val y p q

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPrimeNodeFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual top node factor before summing descendant histories -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingTopPivot {σ : Type*} (value : σ → ℕ)
    (CL CR u : List σ) (XL XR : ℕ) (s v w : ℤ) : ℕ :=
  reconstructedPivot
    (v * (XR * MovingSlotReversal.naturalProduct value CR : ℕ) -
      w * (XL * MovingSlotReversal.naturalProduct value CL : ℕ))
    (s * MovingSlotReversal.naturalProduct value u)

/-- This factor uses only the current lists and three root frequencies.
Descendant support is retained in the two child coefficients. -/
noncomputable def movingPrimeNodeFactor {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (CL CR u : List σ) (XL XR : ℕ) (s v w : ℤ) : ℂ :=
  let U := MovingSlotReversal.naturalProduct value u
  let p := movingTopPivot value CL CR u XL XR s v w
  if (XL :: XR :: ((CL ++ CR).map value ++ outside)).Pairwise Nat.Coprime ∧
      (movingNodeArithmeticGuard (childBound (n + 1)) (pivotBound (n + 1))
        (XL * MovingSlotReversal.naturalProduct value CL)
        (XR * MovingSlotReversal.naturalProduct value CR) s v w (p * U) ∧ 0 < U)
    then ((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplatePrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unchanged independent prime law under one template restoration -/

namespace Ostmann
open scoped Classical BigOperators

/-- The compensation block is sampled once, in precisely the coordinates
of `movingCompensationPrior`; the two child histories will share this block. -/
def movingTemplateCompensationEquiv (A : Type*) (n : ℕ) :
    TreeLeafTuple (Fin 4 → A) n ≃ (TreeLeafIndex n × Fin 4 → A) :=
  (treeLeafTupleEquiv (Fin 4 → A) n).trans (Equiv.curry (TreeLeafIndex n) (Fin 4) A).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteFrequencyExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite reindexing by squarefree kernel and square part -/

namespace Ostmann

open scoped BigOperators

def frequencyTripleData {L U : ℕ} {z : ℕ × ℕ × ℕ}
    (hz : z ∈ frequencyTriples L U) : SquarefreeFrequency L (z.1 * z.2.1 * z.2.2 ^ 2) where
  s := z.1
  v := z.2.1
  w := z.2.2
  s_pos := (mem_frequencyTriples.mp hz).1
  v_pos := Nat.pos_of_mem_divisors (mem_frequencyTriples.mp hz).2.2.1
  w_pos := (mem_frequencyTriples.mp hz).2.2.2.1
  kernel_squarefree := (mem_frequencyTriples.mp hz).2.2.2.2.2.1
  v_dvd := (Nat.mem_divisors.mp (mem_frequencyTriples.mp hz).2.2.1).1
  s_coprime := (mem_frequencyTriples.mp hz).2.2.2.2.2.2.1
  value := rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_TailStability
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Collision stability on the two summand tails

This specializes the finite collision bound to the complementary supports
forced by an eventual prime decomposition. Prime-sum estimates remain
explicit hypotheses; no statement about the existence of a decomposition
is assumed as an analytic input.
-/

namespace Ostmann

open scoped BigOperators

/-- The finite defect for the two summands, with the second one reflected. -/
noncomputable def tailCollisionDefect (A : Set ℕ) (N p : ℕ) (A₀ B₀ : Finset ℕ)
    (μ ν : ℕ → ℝ) : ℝ :=
  collisionDefect p (tailSupport A N p) (Finset.range p \ tailSupport A N p)
    (residueMass A₀ μ p) (fiberMass B₀ ν (negativeResidue p))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledFullFinalPermutation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The final reassignments on every actual surviving prime coordinate -/

namespace Ostmann
open scoped BigOperators Classical

def scheduleHSurvivorEquiv {I : Type*} (role : I → CopyScheduleRole) (n : ℕ) :
    CopyScheduleH role n ≃
      {q : CopyScheduleAtoms role n // (copyScheduleRole role n q.val).copiedAt n = true} where
  toFun q := ⟨⟨q.val, q.property.1⟩, q.property.2⟩
  invFun q := ⟨q.val.val, q.val.property, q.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledFinalComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The final comparison on the actual original prime product law -/

namespace Ostmann
open scoped BigOperators Classical SchwartzMap FourierTransform

noncomputable def scheduledPrimePrior {I A : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (μ : I → A → ℝ)
    (x : CopyScheduleAtoms role n → A) : ℝ :=
  ∏ i, μ (copyScheduleOrigin n i.val) (x i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledWordLeafCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One original word-prime coordinate at each arithmetic tree leaf -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def wordLeafAssignmentEquiv {I A : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) :
    ((WordLeafOutside role i hi n → A) × (TreeLeafIndex n → A)) ≃
      (CopyScheduleAtoms role n → A) where
  toFun z := wordLeafAssignment role i hi n z.1 z.2
  invFun q := (fun v => q v.val, fun t => q (wordLeafSlot role i hi n t))
  left_inv z := by
    apply Prod.ext <;> funext v <;> simp
  right_inv q := by
    funext v
    obtain ⟨z, rfl⟩ := (wordLeafPartition role i hi n).surjective v
    cases z with
    | inl t => exact wordLeafAssignment_leaf role i hi n _ _ t
    | inr v => exact wordLeafAssignment_outside role i hi n _ _ v

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledWordLeafProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected prime products in the two actual H branches -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def wordLeafHPartition {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) :
    TreeLeafIndex n ⊕ WordLeafHOutside role i hi n ≃ CopyScheduleH role n :=
  (Equiv.sumCongr (Equiv.ofInjective _ (wordLeafHSlot role i hi n).injective)
    (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range (wordLeafHSlot role i hi n)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScaledWordLeaves
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selected prime factors through every actual ancestor substitution -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def wordLeafScale {I A : Type*} [Mul A]
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word) (n : ℕ)
    (base : CopyScheduleAtoms role n → A) (x : TreeLeafIndex n → A) :
    CopyScheduleAtoms role n → A :=
  wordLeafAssignment role i hi n (fun v => base v.val)
    (fun t => base (wordLeafSlot role i hi n t) * x t)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPairedTransform
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The surviving Fourier factors in the paired regular template -/

namespace Ostmann
open scoped Classical BigOperators

def movingPairedGiantEquiv (n r m : ℕ) :
    ((Unit ⊕ MovingRegularSlot n r m) ⊕ (Unit ⊕ MovingRegularSlot n r m)) ≃
      (Bool ⊕ MovingRegularSlot (n + 1) r m) where
  toFun
    | .inl (.inl _) => .inl true
    | .inl (.inr i) => .inr (.inl i.1, i.2)
    | .inr (.inl _) => .inl false
    | .inr (.inr i) => .inr (.inr i.1, i.2)
  invFun
    | .inl true => .inl (.inl ())
    | .inl false => .inr (.inl ())
    | .inr (.inl i, j) => .inl (.inr (i, j))
    | .inr (.inr i, j) => .inr (.inr (i, j))
  left_inv := by
    intro i
    rcases i with ((u | ⟨i, j⟩) | (u | ⟨i, j⟩))
    · cases u; rfl
    · rfl
    · cases u; rfl
    · rfl
  right_inv := by
    intro i
    rcases i with (b | ⟨i, j⟩)
    · cases b <;> rfl
    · cases i <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingAveragedIntegerNode
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaging the forced integer node under the surviving regular law -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingTemplateSidePrior {σ : Type} (n r m : ℕ)
    (ν : MovingRegularSlot (n + 1) r m → σ → ℝ) (left : Bool)
    (y : MovingRegularSlot n r m → σ) : ℝ :=
  ∏ i, ν (if left then (.inl i.1, i.2) else (.inr i.1, i.2)) (y i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateAmplitudeRestore
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restoring the original independent compensation law in the amplitude -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingTemplateRestoredPrior {σ : Type} (n r m : ℕ)
    (μ : σ → ℝ) (ν : MovingRegularSlot n r m → σ → ℝ) :
    MovingRegularSlot n (4 + r) m → σ → ℝ := fun i =>
  Sum.elim (fun _ => μ) ν ((movingReverseTemplate n r m).symm i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingAmplitudeNext
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying the transferred off-diagonal with the next prime amplitude -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingTemplateDoubledPrior {σ : Type} (n r m : ℕ)
    (ν : MovingRegularSlot n r m → σ → ℝ) :
    MovingRegularSlot (n + 1) r m → σ → ℝ :=
  fun i => ν (Sum.elim id id i.1, i.2)

@[simp] theorem movingTemplateDoubledPrior_side {σ : Type} (n r m : ℕ)
    (ν : MovingRegularSlot n r m → σ → ℝ) (b : Bool)
    (y : MovingRegularSlot n r m → σ) :
    movingTemplateSidePrior n r m (movingTemplateDoubledPrior n r m ν) b y =
      ∏ i, ν i (y i) := by
  cases b <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothPrimePowerRemoval
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing higher prime powers from the fixed smooth mean -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def smoothPrimeSum (g : ℕ → ℂ) (X : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime,
    (Real.log n : ℂ) * g n * primeMeanTest (n / X)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterPrimeMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime-power removal for a finite primitive character expansion -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def primitiveCharacterPolynomial (F : Finset PrimitiveComplexCharacter)
    (c : PrimitiveComplexCharacter → ℂ) (c₀ : ℂ) (a : ℕ) : ℂ :=
  c₀ + ∑ ρ ∈ F, c ρ * ρ.character (a : ZMod ρ.modulus)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TensorUnitMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The independent unit-residue mean of the sparse polynomial -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def tensorUnitMean {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (f : (∀ i, ZMod (p i)) → ℂ) : ℂ :=
  (∏ i, ((p i : ℂ) - 1)⁻¹) *
    ∑ x : (∀ i, NonzeroResidue (p i)), f (fun i => x i)

noncomputable def tensorUnitMeanLinearMap {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)] :
    ((∀ i, ZMod (p i)) → ℂ) →ₗ[ℂ] ℂ where
  toFun := tensorUnitMean p
  map_add' f g := by simp [tensorUnitMean, Finset.sum_add_distrib, mul_add]
  map_smul' c f := by
    simp only [tensorUnitMean, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseWeightUnitMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact real unit mean of the nonnegative sparse weight -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def tensorRealUnitMean {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (f : (∀ i, ZMod (p i)) → ℝ) : ℝ :=
  (∏ i, ((p i : ℝ) - 1)⁻¹) *
    ∑ x : (∀ i, NonzeroResidue (p i)), f (fun i => x i)

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

noncomputable def scheduledSurvivorGraph {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n : ℕ) (i j : CopyScheduleAtoms role n) : ℤ :=
  copyScheduleGraph initialCompleteGraph pivot n i.val j.val

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledFullMatchingGraph
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained anchor interaction inside the full surviving-prime graph -/

namespace Ostmann
open scoped Classical

noncomputable def scheduledHMatching {I : Type*} (role : I → CopyScheduleRole) (n : ℕ)
    (e : Equiv.Perm (CopyScheduleH role n)) : Equiv.Perm (CopyScheduleAtoms role n) :=
  ((scheduleHSurvivorEquiv role n).permCongr e).subtypeCongr (Equiv.refl _)

noncomputable def scheduledRetainedEmbedding {I : Type*} (role : I → CopyScheduleRole) (n : ℕ) :
    (CopyScheduleH role n ⊕ CopyScheduleY role n) ↪ CopyScheduleAtoms role n :=
  ⟨fun z => scheduledPartitionEquiv role n (.inr z), by
    intro x y h
    exact Sum.inr.inj ((scheduledPartitionEquiv role n).injective h)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_RootCollisions
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Collisions of uniform root populations

The root populations at the end of §3 occupy translated intervals. Their
collision upper bound depends on the diameter and their cardinality.
-/

namespace Ostmann

open scoped BigOperators

/-- Probability that two uniform elements of `s` are congruent modulo `p`. -/
noncomputable def uniformResidueCollision (s : Finset ℕ) (p : ℕ) : ℝ :=
  ∑ r ∈ Finset.range p, (residueMass s (fun _ => 1 / (s.card : ℝ)) p r) ^ 2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TailCharacterRotation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common rotation for the actual translated character averages -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def translatedTailCharacterMean (A : Set ℕ) (N : ℕ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (center : ∀ p : ℕ, ZMod p) (p : ℕ) : ℂ :=
  (∑ r ∈ tailSupport A N p, χ p ((r : ZMod p) - center p)) /
    ((tailSupport A N p).card : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SeparatedMatchingCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting bad bulk matchings while retaining every nonbulk slot -/

namespace Ostmann
open scoped Classical

noncomputable def sumSideRightEquiv (A B : Type*) :
    B ≃ {x : A ⊕ B // sumSide x = false} :=
  Equiv.ofBijective (fun b => ⟨Sum.inr b, rfl⟩) (by
    constructor
    · intro a b h; exact Sum.inr.inj (congrArg Subtype.val h)
    · rintro ⟨a | b, h⟩
      · cases h
      · exact ⟨b, rfl⟩)

noncomputable def separatedMatchingRight {A B : Type*}
    (e : PartitionMatching (@sumSide A B) (@sumSide A B)) : Equiv.Perm B :=
  ((sumSideRightEquiv A B).trans (e.restrict false)).trans (sumSideRightEquiv A B).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ActiveNonbulkCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting only original active nonword slots

Outside slots cannot enter H. In particular the negative copy of the whole
word must not be charged to the nonbulk harmonic normalization.
-/
namespace Ostmann
open scoped Classical

/-- A binary trace suffices on surviving vertices: at a fixed predecessor,
copying and retaining are mutually exclusive. -/
def survivorTrace {I : Type*} : (n : ℕ) → CopyScheduleVertex I n → (Fin n → Bool)
  | 0, _ => Fin.elim0
  | n + 1, .inl (b, i) => Fin.snoc (survivorTrace n i) b
  | n + 1, .inr i => Fin.snoc (survivorTrace n i) false

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_StablePrimeSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting stable primes directly from the total collision budget -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def stableBiasPrimes (P : Finset ℕ) (S T : ℕ → Finset ℕ)
    (μ ν : ℕ → ℕ → ℝ) (δ : ℝ) : Finset ℕ :=
  P.filter fun p => (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p) ≤ δ ^ 2 / 64

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_BiasedTailSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting actual oppositely biased endpoint tails -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def stableTailPrimes (A B : Set ℕ) (N lo hi : ℕ) (P : Finset ℕ) (δ : ℝ) : Finset ℕ :=
  stableBiasPrimes P (tailSupport A N) (fun p => Finset.range p \ tailSupport A N p)
    (fun p => residueMass (summandTail A lo hi) (fun _ => 1 / ((summandTail A lo hi).card : ℝ)) p)
    (fun p => fiberMass (summandTail B lo hi) (fun _ => 1 / ((summandTail B lo hi).card : ℝ)) (negativeResidue p)) δ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedPivotEnergyTransport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining selected-prime energy with an externally fixed composite pivot -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def scheduledReplacePivot {I : Type*} (role : I → CopyScheduleRole)
    (n M : ℕ) (base : CopyScheduleAtoms role n → ℕ) : CopyScheduleAtoms role n → ℕ :=
  fun a => if (copyScheduleRole role n a.val).erasedAt n then M else base a

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalProductRange
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Root cutoffs for the product of specified original prime coordinates -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def originalProductRange {V : Type*} (w : List V) (n : ℕ) (lo hi : ℝ) :
    WordRange (ExpandedScheduledVariable V n) := ⟨w.map Sum.inl, lo, hi⟩

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

/-- Equality on natural arguments compares characters even when their
moduli occur with different dependent types. -/
def samePrimitiveRealCharacter (e : PrimitiveRealZero) (χ : PrimitiveRealCharacter) : Prop :=
  e.modulus = χ.modulus ∧ ∀ n : ℕ, e.character n = χ.character n

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedInitialPriorBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Probability and point-mass bounds for the selected original half-list -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def selectedInitialHalfPrior (P : Finset ℕ) (A B : Set ℕ)
    (N hi : ℕ) (Y G : ℝ) (D Qb Qd : Finset ℕ) (b d top : ℕ)
    (centers : List ℕ) : Fin ((b + (d + (initialSmallCellList top centers).length)) + 1) → P → ℝ :=
  Fin.cons (smoothGiantPrior P logCellProfile G)
    (Fin.append (fun _ : Fin b => primeSubsetPrior P Qb)
      (Fin.append (fun _ : Fin d => primeSubsetPrior P Qd)
        (fun i => primeSubsetPrior P (selectedTailCellPrimes A B N Y hi D
          ((initialSmallCellList top centers).get i)))))

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

noncomputable def pageDeletionPrimes (z : Option PrimitiveRealZero) (cutoff : ℕ) : Finset ℕ :=
  match z with
  | none => ∅
  | some z => (deletedConductorPrime z.modulus cutoff).toFinset

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedCompensationPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual selected compensation cells as one common prime-space prior -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def selectedCompensationPrior (A B : Set ℕ) (N : ℕ) (X : ℝ)
    (hi : ℕ) (D P : Finset ℕ) (centers : List ℕ) (n : ℕ) : P → ℝ :=
  primeSubsetPrior P (selectedTailCellPrimes A B N X hi D ((centers.drop n).headD 0))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedFinalPermutation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Final parity permutations fix every top slot

Only the explicitly selected bulk slots are permuted among paths of equal
parity. The remaining word slots, in particular the top labels, stay fixed.
-/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def selectedParityH {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) :
    (ParityPathSum n × Fin m) ↪ CopyScheduleH role (n + 1) where
  toFun x := scheduledWordH role (n + 1) (parityPathValue x.1) ⟨bulk x.2, hbulk x.2⟩
  inj' := by
    intro x y h
    have he := @copySchedulePath_injective I (n + 1)
      (parityPathValue x.1, bulk x.2) (parityPathValue y.1, bulk y.2)
      (congrArg Subtype.val h)
    exact Prod.ext (parityPathValue_injective n (congrArg Prod.fst he))
      (bulk.injective (congrArg Prod.snd he))

noncomputable def selectedParityCoordinates {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) :
    (ParityPathSum n × Fin m) ≃
      {h : CopyScheduleH role (n + 1) // h ∈ Set.range (selectedParityH role n m bulk hbulk)} :=
  Equiv.ofInjective _ (selectedParityH role n m bulk hbulk).injective

noncomputable def selectedFinalPerm {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : FinalParityReassignments n m) : Equiv.Perm (CopyScheduleH role (n + 1)) :=
  ((selectedParityCoordinates role n m bulk hbulk).permCongr (paritySlotPerm e)).subtypeCongr
    (Equiv.refl _)

@[simp] theorem selectedParityH_origin {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (x : ParityPathSum n × Fin m) :
    copyScheduleOrigin (n + 1) (selectedParityH role n m bulk hbulk x).val = bulk x.2 :=
  copyScheduleOrigin_path (n + 1) _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedFullFinalPermutation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selected-bulk permutations on all actual surviving prime coordinates -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def selectedFullFinalPerm {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : FinalParityReassignments n m) : Equiv.Perm (CopyScheduleAtoms role (n + 1)) :=
  ((scheduleHSurvivorEquiv role (n + 1)).permCongr
    (selectedFinalPerm role n m bulk hbulk e)).subtypeCongr (Equiv.refl _)

noncomputable def selectedFullSamplePerm {I A : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : FinalParityReassignments n m) :
    (CopyScheduleAtoms role (n + 1) → A) ≃ (CopyScheduleAtoms role (n + 1) → A) :=
  Equiv.arrowCongr (selectedFullFinalPerm role n m bulk hbulk e).symm (Equiv.refl A)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedFinalInteraction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A moved selected-bulk slot gives the final one-sided interaction -/
namespace Ostmann
open scoped Classical

noncomputable def selectedPairMatching {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e f : FinalParityReassignments n m) : Equiv.Perm (CopyScheduleH role (n + 1)) :=
  (selectedFinalPerm role n m bulk hbulk f).symm.trans (selectedFinalPerm role n m bulk hbulk e)

noncomputable def selectedFinalRelativePerm {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e f : FinalParityReassignments n m) : Equiv.Perm (CopyScheduleAtoms role (n + 1)) :=
  (selectedFullFinalPerm role n m bulk hbulk f).trans (selectedFullFinalPerm role n m bulk hbulk e).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailMaskCollision
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual tail projection in the giant collision estimate -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def zmodResidueMass (E : Finset ℕ) (μ : ℕ → ℝ)
    (p : ℕ) (x : ZMod p) : ℝ := residueMass E μ p x.val

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_AdditiveSieveProof
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published additive large sieve, with its precise downstream constant

The finite cosecant Hilbert inequality and duality prove the separated-frequency
estimate. Reduced fractions of denominator at most Q are 1/Q²-separated.
This proves the specialization of Montgomery--Vaughan (1973), Theorem 1,
used throughout the conditional development.
-/

namespace Ostmann

open scoped BigOperators

noncomputable def reducedFractionPoint (Q : ℕ) (s : ReducedFractionIndex Q) : ℝ :=
  (s.2.val : ℝ) / s.1.val

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_FixedQuadraticFamily
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed finite family containing all discretized arithmetic arrays -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

noncomputable def quadraticFamilyParameters (T : ℝ) (L : ℕ) : Finset QuadraticFamilyIndex :=
  (Finset.range (4 * L)).product ((Finset.range L).product
    ((Finset.Icc 1 ⌊Real.exp (7 * T)⌋₊).product
      (quadraticParameterGrid (Real.exp (14 * T)) (Real.exp (-200 * T)))))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_SmallKernelFamily
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed family with the scale needed for the small-kernel estimate -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

noncomputable def smallKernelParameters (T : ℝ) (L : ℕ) : Finset QuadraticFamilyIndex :=
  (quadraticFamilyParameters T L).filter (fun i =>
    i.2.2.1 = 1 ∧ (L : ℝ) ^ 6 ≤ quadraticGridScale (Real.exp (-200 * T)) i.2.2.2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_LargeKernelFamily
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed principal family on the large squarefree kernels -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

noncomputable def principalQuadraticParameters (T : ℝ) (L : ℕ) : Finset QuadraticFamilyIndex :=
  (quadraticFamilyParameters T L).filter (fun i => i.2.2.1 = 1)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_OuterKernelFamily
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The nontrivial outer-divisor family has exponentially small moments -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

noncomputable def outerQuadraticParameters (T : ℝ) (L : ℕ) : Finset QuadraticFamilyIndex :=
  (quadraticFamilyParameters T L).filter (fun i => Real.exp T ≤ (i.2.2.1 : ℝ))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_MaximalQuadraticBias
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Maximizing translating residues and the little-o conclusion -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical

noncomputable def quadraticBandMass (A : Set ℕ) (N : ℕ) (T : ℝ) : ℝ :=
  ∑ p ∈ logPrimeBand T, (Real.log (p : ℝ) / p) * maximalQuadraticBias (tailSupport A N p) p

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGcdExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact common-divisor expansion of the quadratic second moment -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

def quadraticGcdPairs (N d : ℕ) : Finset (ℕ × ℕ) :=
  ((oddSquarefreeRange N).product (oddSquarefreeRange N)).filter
    fun z => z.1.gcd z.2 = d

noncomputable def quadraticGcdKernelSum (N d : ℕ) (b : ℕ → ℂ) (m : ℤ) : ℂ :=
  ∑ z ∈ quadraticGcdPairs N d,
    b z.1 * conj (b z.2) * (jacobiSym m (quadraticPairKernel z.1 z.2) : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticBilinearExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two-array coprime expansion needed for divisor restrictions -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

noncomputable def quadraticCoprimeBilinear (N₁ N₂ : ℕ) (a b : ℕ → ℂ) (m : ℤ) : ℂ :=
  ∑ n₁ ∈ oddSquarefreeRange N₁, ∑ n₂ ∈ oddSquarefreeRange N₂,
    (if n₁.Coprime n₂ then (1 : ℂ) else 0) *
      a n₁ * conj (b n₂) * (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDivisorSplit
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact split of a product divisor between coprime coefficients -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

noncomputable def quadraticDivisorBilinear (N₁ N₂ d : ℕ) (a b : ℕ → ℂ) (m : ℤ) : ℂ :=
  ∑ n₁ ∈ oddSquarefreeRange N₁, ∑ n₂ ∈ oddSquarefreeRange N₂,
    (if n₁.Coprime n₂ ∧ d ∣ n₁ * n₂ then (1 : ℂ) else 0) *
      a n₁ * conj (b n₂) * (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDivisorFamily
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the two divisor ranges in Heath-Brown's bilinear comparison -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticDivisorWeight (N s : ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ n ∈ oddSquarefreeRange N,
    (n.divisors.card : ℝ) * ‖if s ∣ n then a n else 0‖ ^ 2

noncomputable def quadraticDivisorMoment (N : ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ n ∈ oddSquarefreeRange N, (n.divisors.card : ℝ) ^ 2 * ‖a n‖ ^ 2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDivisorRange
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounding the original product-divisibility sum by its exact rectangle -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticDivisorRangePairs (N₁ N₂ D : ℕ) : Finset (ℕ × ℕ) :=
  ((oddSquarefreeRange N₁).product (oddSquarefreeRange N₂)).filter
    (fun z => D < z.1 * z.2 ∧ z.1 * z.2 ≤ 2 * D)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDyadicDivisors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A disjoint dyadic partition of the actual odd-squarefree divisors -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticDyadicDivisors (N j : ℕ) : Finset ℕ :=
  (oddSquarefreeRange N).filter (fun s => Nat.log 2 s = j)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDyadicSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting a genuine divisor block with the original product range -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticDyadicDivisorMass (M N₁ N₂ D i j : ℕ) (a b : ℕ → ℂ) : ℝ :=
  ∑ s ∈ quadraticDyadicDivisors N₁ i, ∑ t ∈ quadraticDyadicDivisors N₂ j,
    if D < s * t ∧ s * t ≤ 2 * D then
      ∑ m ∈ oddSquarefreeRange M, ‖quadraticCoprimeBilinear N₁ N₂
        (fun n => if s ∣ n then a n else 0)
        (fun n => if t ∣ n then b n else 0) m‖ else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGaussBilinear
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the Gauss factor in the actual divisor bilinear sum -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

noncomputable def quadraticGaussDivisorBilinear (N₁ N₂ d : ℕ)
    (a b : ℕ → ℂ) (m : ℤ) : ℂ :=
  ∑ s ∈ oddSquarefreeRange N₁, ∑ t ∈ oddSquarefreeRange N₂,
    (if s.Coprime t ∧ d ∣ s * t then (1 : ℂ) else 0) *
      a s * conj (b t) * quadraticGaussMultiplier (s * t) *
      (jacobiSym m s : ℂ) * (jacobiSym m t : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticWeightedBilinear
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth logarithmic weights in the literal divisor bilinear form -/

namespace Ostmann

open MeasureTheory
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

noncomputable def quadraticLogWeightedDivisor (f : 𝓢(ℝ, ℂ)) (N₁ N₂ d : ℕ)
    (a b : ℕ → ℂ) (m : ℤ) : ℂ :=
  ∑ s ∈ oddSquarefreeRange N₁, ∑ t ∈ oddSquarefreeRange N₂,
    ((if s.Coprime t ∧ d ∣ s * t then (1 : ℂ) else 0) *
      a s * conj (b t) * (jacobiSym m s : ℂ) * (jacobiSym m t : ℂ)) *
      f (Real.log s + Real.log t)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveAdditiveStart
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initial quadratic-sieve bound from the proved additive large sieve -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def quadraticArray (N : ℕ) (b : ℕ → ℂ) : Fin (N + 1) → ℂ :=
  fun n => if n.val ∈ oddSquarefreeRange N then b n.val else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGrowthDivisorBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual shorter sieve matrices supply every divisor-band budget -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticGrowthDivisorBudget (C ε ξ : ℝ) (B N D : ℕ)
    (v w : ℕ → ℂ) : ℝ :=
  quadraticGrowthBandBudget (C * ((B : ℝ) * N) ^ ε) ((B : ℝ) ^ ξ) N D
    (Real.sqrt (quadraticDivisorMoment N v) * Real.sqrt (quadraticDivisorMoment N w))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticWeightedGaussBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth divisor comparison with the actual quadratic Gauss coefficient -/

namespace Ostmann

open MeasureTheory
open scoped Classical BigOperators ComplexConjugate SchwartzMap FourierTransform

noncomputable def quadraticLogWeightedGaussDivisor (f : 𝓢(ℝ, ℂ)) (N₁ N₂ d : ℕ)
    (a b : ℕ → ℂ) (m : ℤ) : ℂ :=
  ∑ s ∈ oddSquarefreeRange N₁, ∑ t ∈ oddSquarefreeRange N₂,
    (if s.Coprime t ∧ d ∣ s * t then (1 : ℂ) else 0) *
      a s * conj (b t) * quadraticGaussMultiplier (s * t) *
      (jacobiSym m s : ℂ) * (jacobiSym m t : ℂ) * f (Real.log s + Real.log t)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticRootDivisor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal square-root weights in the second Poisson comparison -/

namespace Ostmann

open MeasureTheory
open scoped Classical BigOperators ComplexConjugate SchwartzMap FourierTransform

noncomputable def quadraticRootGaussDivisor (ρ : 𝓢(ℝ, ℂ)) (X : ℝ)
    (N d : ℕ) (a b : ℕ → ℂ) (m : ℤ) : ℂ :=
  ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
    (if s.Coprime t ∧ d ∣ s * t then (1 : ℂ) else 0) *
      a s * conj (b t) * quadraticGaussMultiplier (s * t) *
      (jacobiSym m s : ℂ) * (jacobiSym m t : ℂ) * ρ (X * Real.sqrt ((s : ℝ) * t))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticMiddleDivisor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal middle-frequency correction in the second Poisson formula -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate SchwartzMap FourierTransform

noncomputable def quadraticMiddleDivisor (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    (M : ℝ) (e N d : ℕ) (v w : ℕ → ℂ) (b : ℕ) (l : ℤ) : ℂ :=
  ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
    (if s.Coprime t ∧ d ∣ s * t then (1 : ℂ) else 0) *
      v s * conj (w t) * quadraticGaussMultiplier (s * t) *
      (jacobiSym (b : ℤ) s : ℂ) * (jacobiSym (b : ℤ) t : ℂ) *
      𝓕 (quadraticFourierSquare ρ a ha)
        ((l : ℝ) * (quadraticSecondScale M e (s * t) b / d))

noncomputable def quadraticMiddleWindow (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    (M : ℝ) (e N d : ℕ) (v w : ℕ → ℂ) (b L : ℕ) : ℂ :=
  ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
    (if s.Coprime t ∧ d ∣ s * t then (1 : ℂ) else 0) *
      v s * conj (w t) * quadraticGaussMultiplier (s * t) *
      (jacobiSym (b : ℤ) s : ℂ) * (jacobiSym (b : ℤ) t : ℂ) *
      quadraticLatticeWindow (𝓕 (quadraticFourierSquare ρ a ha))
        (quadraticSecondScale M e (s * t) b / d) L

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSquarefreePart
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unique square-times-squarefree decomposition for the Poisson comparison -/

namespace Ostmann

noncomputable def quadraticSquarePart (m : ℕ) : ℕ :=
  Classical.choose (exists_quadratic_factor m)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallKernels
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite reindexing of the small-squarefree-kernel contribution -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticSmallKernelRange (M K : ℕ) : Finset ℕ :=
  (Finset.Icc 1 M).filter fun m => Odd m ∧ quadraticSquarefreePart m ≤ K

def quadraticSmallKernelPairs (M K : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 M).product (oddSquarefreeRange K)).filter
    fun z => Odd z.1 ∧ z.1 ^ 2 * z.2 ≤ M

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGrowthCorrectionBands
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original low and high correction bands from the actual growth matrices -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticLowCorrectionBand (B N D : ℕ) (P : ℕ → ℕ → Prop)
    (v w : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
    if B ≤ b ∧ P d b then (ArithmeticFunction.moebius d : ℂ) *
      quadraticGaussDivisorBilinear (2 * N) (2 * N) d
        (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) b else 0

noncomputable def quadraticHighCorrectionBand (B N D : ℕ) (P : ℕ → ℕ → Prop)
    (v w : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
    if B ≤ b ∧ P d b then
      (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) *
        quadraticGaussDivisorBilinear (2 * N) (2 * N) d v w b else 0

noncomputable def quadraticCorrectionGrowthScale (C ε ξ M : ℝ) (e B N : ℕ)
    (v w : ℕ → ℂ) : ℝ :=
  (C * (((2 * B : ℕ) : ℝ) * (2 * N : ℕ)) ^ ε) *
    (2 * (M / e) + Real.sqrt (2 * (M / e)) / Real.sqrt B * ((2 * B : ℕ) : ℝ) ^ ξ) *
      (Real.sqrt (quadraticDivisorMoment (2 * N) v) *
        Real.sqrt (quadraticDivisorMoment (2 * N) w))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticMiddleBandGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original middle-divisor correction at the current sieve exponent -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

noncomputable def quadraticMiddleCorrectionBand (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    (M : ℝ) (e B N D L : ℕ) (P : ℕ → ℕ → Prop) (v w : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
    if B ≤ b ∧ P d b then
      (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) *
        quadraticMiddleWindow ρ a ha M e N d v w b L else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallCorrectionGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Both original small-kernel corrections from the same shorter matrices -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

noncomputable def quadraticSmallHighBand (E B N D : ℕ) (P : ℕ → ℕ → Prop)
    (v w : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
    if B ≤ b ∧ P d b then
      (((ArithmeticFunction.moebius (E * d) : ℂ) / (E * d : ℕ)) / (Real.sqrt b : ℂ)) *
        quadraticDivisorBilinear (2 * N) (2 * N) d v w b else 0

noncomputable def quadraticSmallMiddleBand (ρ : 𝓢(ℝ, ℂ)) (M : ℝ) (E B N D L : ℕ)
    (P : ℕ → ℕ → Prop) (v w : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
    if B ≤ b ∧ P d b then
      ((((ArithmeticFunction.moebius (E * d) : ℂ) / (E * d : ℕ)) / (Real.sqrt b : ℂ)) *
        quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest ρ))
          (quadraticSmallScale M b / (E * d : ℕ)) L) *
        quadraticDivisorBilinear (2 * N) (2 * N) d v w b else 0

noncomputable def quadraticSmallCorrectionGrowthScale (C ε ξ M A : ℝ) (B N : ℕ)
    (v w : ℕ → ℂ) : ℝ :=
  (C * (((2 * B : ℕ) : ℝ) * (2 * N : ℕ)) ^ ε) *
    (Real.sqrt M / Real.sqrt B * ((2 * B : ℕ) : ℝ) ^ ξ + A * (2 * N)) *
      (Real.sqrt (quadraticDivisorMoment (2 * N) v) *
        Real.sqrt (quadraticDivisorMoment (2 * N) w))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticUnitCorrectionGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The missing unit-divisor endpoint has the same normalized growth rate -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticLowCorrectionUnit (B N : ℕ) (P : ℕ → Prop)
    (v w : ℕ → ℂ) : ℂ :=
  ∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P b then
    quadraticGaussDivisorBilinear (2 * N) (2 * N) 1
      (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) b else 0

noncomputable def quadraticHighCorrectionUnit (B N : ℕ) (P : ℕ → Prop)
    (v w : ℕ → ℂ) : ℂ :=
  ∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P b then
    (1 / (Real.sqrt b : ℂ)) * quadraticGaussDivisorBilinear (2 * N) (2 * N) 1 v w b else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticWholeHighGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete high-divisor correction, with the unit boundary retained -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticHighCorrectionTotal (B N Q : ℕ) (P : ℕ → ℕ → Prop)
    (v w : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange (2 * B),
    if B ≤ b ∧ P d b then (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) *
      quadraticGaussDivisorBilinear (2 * N) (2 * N) d
        v w b else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticWholeLowGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete low-divisor correction, with the unit boundary retained -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticLowCorrectionTotal (B N Q : ℕ) (P : ℕ → ℕ → Prop)
    (v w : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange (2 * B),
    if B ≤ b ∧ P d b then (ArithmeticFunction.moebius d : ℂ) *
      quadraticGaussDivisorBilinear (2 * N) (2 * N) d
        (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) b else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticUnitMiddleGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized middle correction at the divisor-one boundary -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

noncomputable def quadraticMiddleCorrectionUnit (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    (M : ℝ) (e B N L : ℕ) (P : ℕ → Prop) (v w : ℕ → ℂ) : ℂ :=
  ∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P b then
    (1 / (Real.sqrt b : ℂ)) * quadraticMiddleWindow ρ a ha M e N 1 v w b L else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticWholeMiddleGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete middle-divisor correction, with the unit boundary retained -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

noncomputable def quadraticMiddleCorrectionTotal (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    (M : ℝ) (e B N Q L : ℕ) (P : ℕ → ℕ → Prop)
    (v w : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange (2 * B),
    if B ≤ b ∧ P d b then (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) *
      quadraticMiddleWindow ρ a ha M e N d v w b L else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFullHighGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The entire original high correction at the current sieve exponent -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticFullHighCorrection (M H J : ℝ) (e N Q K : ℕ)
    (R : ℕ → ℕ → Prop) (v w : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange K,
    if R d b ∧ quadraticSecondUpper (quadraticCorrectionBase M H e b) J < (d : ℝ) then
      (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) * quadraticGaussDivisorBilinear (2 * N) (2 * N) d
        v w b else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFullLowGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The entire original low correction at the current sieve exponent -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticFullLowCorrection (M H J : ℝ) (e N Q K : ℕ)
    (R : ℕ → ℕ → Prop) (v w : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange K,
    if R d b ∧ (d : ℝ) ≤ quadraticSecondUpper (quadraticCorrectionBase M H e b) J then
      (ArithmeticFunction.moebius d : ℂ) * quadraticGaussDivisorBilinear (2 * N) (2 * N) d
        (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) b else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticWholeSmallHighGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete small-kernel high-divisor correction, with the unit boundary retained -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticSmallHighTotal (E B N Q : ℕ) (P : ℕ → ℕ → Prop)
    (v w : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange (2 * B),
    if B ≤ b ∧ P d b then (((ArithmeticFunction.moebius (E * d) : ℂ) / (E * d : ℕ)) / (Real.sqrt b : ℂ)) *
      quadraticDivisorBilinear (2 * N) (2 * N) d
        v w b else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticWholeSmallMiddleGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete small-kernel middle-divisor correction, with the unit boundary retained -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

noncomputable def quadraticSmallMiddleTotal (ρ : 𝓢(ℝ, ℂ)) (M : ℝ) (E B N Q L : ℕ) (P : ℕ → ℕ → Prop)
    (v w : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange (2 * B),
    if B ≤ b ∧ P d b then ((((ArithmeticFunction.moebius (E * d) : ℂ) / (E * d : ℕ)) / (Real.sqrt b : ℂ)) *
        quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest ρ))
          (quadraticSmallScale M b / (E * d : ℕ)) L) *
      quadraticDivisorBilinear (2 * N) (2 * N) d
        v w b else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFullMiddleGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The entire original middle correction at the current sieve exponent -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

noncomputable def quadraticFullMiddleCorrection (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    (M H J : ℝ) (e N Q K L : ℕ)
    (R : ℕ → ℕ → Prop) (v w : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange K,
    if R d b ∧ quadraticSecondLower (quadraticCorrectionBase M H e b) J < (d : ℝ) ∧
        (d : ℝ) ≤ quadraticSecondUpper (quadraticCorrectionBase M H e b) J then
      (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) *
        quadraticMiddleWindow ρ a ha M e N d v w b L else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCorrectionEnvelope
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One explicit envelope for the three original second-Poisson corrections -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators SchwartzMap FourierTransform

noncomputable def quadraticCorrectionEnvelope (C ε ξ M J : ℝ) (N Q K L : ℕ)
    (v w : ℕ → ℂ) : ℝ :=
  (2 * L + 1) * (J * ((Nat.log 2 K + 1 : ℕ) : ℝ) *
    ((Nat.log 2 Q + 2 : ℕ) : ℝ) * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
      (C * (4 * (K : ℝ) * N) ^ ε * (M + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)) *
        (Real.sqrt (quadraticDivisorMoment (2 * N) v) *
          Real.sqrt (quadraticDivisorMoment (2 * N) w))))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed nonnegative smoothing weight in Heath-Brown's argument -/

namespace Ostmann

open scoped SchwartzMap BigOperators

noncomputable def quadraticSieveWeight : 𝓢(ℝ, ℂ) :=
  (quadraticSieveBump.hasCompactSupport.comp_left
    (show Complex.ofReal 0 = 0 by simp)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp quadraticSieveBump.contDiff)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGcdRemainder
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing uniform pair remainders against the actual coefficients -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

noncomputable def quadraticGcdRemainder (N : ℕ) (v : ℕ → ℂ)
    (E : ℕ → ℕ × ℕ → ℂ) : ℂ :=
  ∑ D ∈ Finset.Icc 1 N, ∑ z ∈ quadraticGcdPairs N D,
    v z.1 * conj (v z.2) * E D z

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFirstMomentTransform
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact first transform of the full smoothed moment -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate FourierTransform

noncomputable def quadraticFirstKernelTransform (M D q : ℕ) : ℂ :=
  quadraticGaussMultiplier q * ∑ e ∈ (2 * D).divisors,
    (ArithmeticFunction.moebius e : ℂ) *
      (((M : ℝ) / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
      ∑' h : ℤ, (jacobiSym ((e : ℤ) * h) q : ℂ) *
        𝓕 quadraticSieveWeight ((h : ℝ) * M / ((e : ℝ) * q))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSignedInfiniteSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact infinite signed-frequency coordinates for the first transform -/

namespace Ostmann

open scoped Classical BigOperators

def quadraticFrequencyValue (z : QuadraticFrequencyIndex) : ℤ :=
  (z.1 : ℤ) * (z.2.2 : ℕ) ^ 2 * (z.2.1.val : ℕ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFirstFrequencyCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite second-Poisson family and its proved first-transform tail -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

noncomputable def quadraticFirstFiniteFrequency (ψ : 𝓢(ℝ, ℂ))
    (M : ℝ) (e q K : ℕ) : ℂ :=
  ∑ a ∈ ({1, -1, 2, -2} : Finset ℤ), ∑ b ∈ oddSquarefreeRange K,
    ((jacobiSym ((e : ℤ) * a) q : ℂ) * (jacobiSym b q : ℂ)) *
      ∑' c : ℕ+, (1 : DirichletCharacter ℂ q) (c : ZMod q) *
        𝓕 ψ ((a : ℝ) * b * (c : ℝ) ^ 2 / ((e : ℝ) * q / M))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFirstKernelError
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The whole first-transform tail, with the actual pair and divisor weights -/

namespace Ostmann

open scoped Classical BigOperators FourierTransform

noncomputable def quadraticFirstKernelFinite (M D q K : ℕ) : ℂ :=
  quadraticGaussMultiplier q * ∑ e ∈ (2 * D).divisors,
    (ArithmeticFunction.moebius e : ℂ) *
      (((M : ℝ) / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
        quadraticFirstFiniteFrequency quadraticSieveWeight M e q K

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticMainCoefficients
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual integer coefficients in the quadratic main-term comparison -/

namespace Ostmann

open scoped Classical BigOperators
open MonoidAlgebra

noncomputable def quadraticMainAlpha (D K w : ℕ) : ℤ :=
  ∑ e ∈ D.divisors, ∑ b ∈ oddSquarefreeRange K,
    if e * b = w then ArithmeticFunction.moebius e else 0

noncomputable def quadraticMainBeta (D K w : ℕ) : ℤ :=
  ∑ u ∈ D.divisors, ∑ v ∈ (oddSquarefreeRange K).filter (D.Coprime ·),
    if u ^ 2 * v = w then ArithmeticFunction.moebius u else 0

noncomputable def quadraticMainGamma (D K w : ℕ) : ℤ :=
  quadraticMainAlpha D K w - quadraticMainBeta D K w

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticTotientKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact totient-weighted kernel after removal of the common divisor -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

noncomputable def quadraticTotientKernelSum (N D : ℕ) (b : ℕ → ℂ) (m : ℤ) : ℂ :=
  ∑ z ∈ quadraticGcdPairs N D, b z.1 * conj (b z.2) *
    ((Nat.totient (quadraticPairKernel z.1 z.2) : ℂ) / quadraticPairKernel z.1 z.2) *
    (jacobiSym m (quadraticPairKernel z.1 z.2) : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticMainComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The main-term comparison in Heath-Brown's quadratic-sieve recursion -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticMainDifference (N D K : ℕ) (b : ℕ → ℂ) : ℂ :=
  ∑ w ∈ Finset.Icc 1 (K * D ^ 2), (quadraticMainGamma D K w : ℂ) *
    (quadraticTotientKernelSum N D b w / (Real.sqrt (w : ℝ) : ℂ))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSecondSignedCore
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full signed second Poisson core, at the original first-transform weights -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

noncomputable def quadraticSignedSecondCore (ρ : 𝓢(ℝ, ℂ)) (M H J : ℝ)
    (e q K : ℕ) : ℂ :=
  ∑ a : quadraticPoissonSigns, ∑ b ∈ oddSquarefreeRange K,
    ((jacobiSym ((e : ℤ) * a) q : ℂ) * (jacobiSym b q : ℂ)) *
      quadraticSecondDyadicCore ρ (a : ℤ) (quadraticPoissonSigns_abs a.property) M b H J e q b

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFirstSecondKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original finite first transform after the complete second Poisson step -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

noncomputable def quadraticFirstSecondKernel (M D q K : ℕ) (H J : ℝ) : ℂ :=
  quadraticGaussMultiplier q * ∑ e ∈ (2 * D).divisors,
    (ArithmeticFunction.moebius e : ℂ) *
      (((M : ℝ) / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
        quadraticSignedSecondCore quadraticSieveWeight M H J e q K

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticOriginalMainTerms
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two original Poisson main terms and their proved comparison

The common real factor (sqrt M / 2 times the fixed smoothing integral) is omitted
from both terms. All character, totient and gcd factors are retained.
-/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

noncomputable def quadraticFirstMain (N D K : ℕ) (b : ℕ → ℂ) : ℂ :=
  ∑ z ∈ quadraticGcdPairs N D,
    b z.1 * conj (b z.2) *
      ((Nat.totient (quadraticPairKernel z.1 z.2) : ℂ) / quadraticPairKernel z.1 z.2) *
      ((∑ e ∈ D.divisors, (ArithmeticFunction.moebius e : ℂ) *
        quadraticRootCharacter (quadraticPairKernel z.1 z.2) e) *
        ∑ v ∈ oddSquarefreeRange K, quadraticRootCharacter (quadraticPairKernel z.1 z.2) v)

noncomputable def quadraticSecondMain (N D K : ℕ) (b : ℕ → ℂ) : ℂ :=
  ∑ z ∈ quadraticGcdPairs N D,
    b z.1 * conj (b z.2) *
      ((Nat.totient (quadraticPairKernel z.1 z.2 * D) : ℂ) / (quadraticPairKernel z.1 z.2 * D)) *
        ∑ v ∈ (oddSquarefreeRange K).filter (D.Coprime ·),
          quadraticRootCharacter (quadraticPairKernel z.1 z.2) v

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticTransformedMain
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The transformed first main term is the original comparison term -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators ComplexConjugate SchwartzMap

noncomputable def quadraticTransformedFirstMain (M : ℝ) (N D K : ℕ)
    (ρ : 𝓢(ℝ, ℂ)) (b : ℕ → ℂ) : ℂ :=
  ((∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) / 2) *
    ∑ z ∈ quadraticGcdPairs N D, b z.1 * conj (b z.2) *
      ((Nat.totient (quadraticPairKernel z.1 z.2) : ℂ) / quadraticPairKernel z.1 z.2) *
        ∑ v ∈ oddSquarefreeRange K, (jacobiSym (v : ℤ) (quadraticPairKernel z.1 z.2) : ℂ) *
          quadraticDualMainCoefficient M D (quadraticPairKernel z.1 z.2) v

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFirstSecondMain
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The second Poisson core has exactly the original main term and corrections -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators SchwartzMap FourierTransform

noncomputable def quadraticFirstSecondMainKernel (M D q K : ℕ) : ℂ :=
  quadraticGaussMultiplier q * ∑ e ∈ (2 * D).divisors,
    (ArithmeticFunction.moebius e : ℂ) *
      (((M : ℝ) / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
        ∑ a : quadraticPoissonSigns, ∑ b ∈ oddSquarefreeRange K,
          ((jacobiSym ((e : ℤ) * a) q : ℂ) * (jacobiSym b q : ℂ)) *
          (((quadraticSecondScale M e q b : ℂ) * q.totient / q) *
            ((quadraticFresnelPhase (a : ℤ) / (Real.sqrt |((a : ℤ) : ℝ)| : ℂ)) *
              ∫ x in Ioi (0 : ℝ), quadraticSieveWeight (x ^ 2)) / 2)

noncomputable def quadraticFirstSecondCorrections (M D q K : ℕ) (H J : ℝ) : ℂ :=
  quadraticGaussMultiplier q * ∑ e ∈ (2 * D).divisors,
    (ArithmeticFunction.moebius e : ℂ) *
      (((M : ℝ) / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
        ∑ a : quadraticPoissonSigns, ∑ b ∈ oddSquarefreeRange K,
          ((jacobiSym ((e : ℤ) * a) q : ℂ) * (jacobiSym b q : ℂ)) *
            quadraticSecondDyadicCorrection quadraticSieveWeight (a : ℤ)
              (quadraticPoissonSigns_abs a.property) M H J e q b

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFullSmallHighGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The entire original small-kernel high correction at the current sieve exponent -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticFullSmallHighCorrection (M J : ℝ) (E N Q K : ℕ)
    (R : ℕ → ℕ → Prop) (v w : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange K,
    if R d b ∧ quadraticSecondUpper (quadraticSmallScale M b) J < (E * d : ℕ) then
      (((ArithmeticFunction.moebius (E * d) : ℂ) / (E * d : ℕ)) / (Real.sqrt b : ℂ)) * quadraticDivisorBilinear (2 * N) (2 * N) d
        v w b else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFullSmallMiddleGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The entire original small-kernel middle correction at the current sieve exponent -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

noncomputable def quadraticFullSmallMiddleCorrection (ρ : 𝓢(ℝ, ℂ)) (M J : ℝ) (E N Q K L : ℕ)
    (R : ℕ → ℕ → Prop) (v w : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange K,
    if R d b ∧ quadraticSecondLower (quadraticSmallScale M b) J < (E * d : ℕ) ∧
        (E * d : ℕ) ≤ quadraticSecondUpper (quadraticSmallScale M b) J then
      ((((ArithmeticFunction.moebius (E * d) : ℂ) / (E * d : ℕ)) / (Real.sqrt b : ℂ)) *
        quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest ρ)) (quadraticSmallScale M b / (E * d : ℕ)) L) * quadraticDivisorBilinear (2 * N) (2 * N) d
        v w b else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallKernelMain
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact identification of the small-kernel main term -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators ComplexConjugate SchwartzMap

noncomputable def quadraticSmallTransformedMain (M : ℝ) (N D K : ℕ)
    (ρ : 𝓢(ℝ, ℂ)) (v : ℕ → ℂ) : ℂ :=
  ∑ z ∈ quadraticGcdPairs N D, v z.1 * conj (v z.2) *
    ∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·),
      (quadraticSmallScale M b : ℂ) *
        (((2 * (quadraticPairKernel z.1 z.2 * D)).totient : ℂ) /
          (2 * (quadraticPairKernel z.1 z.2 * D) : ℕ)) *
        (∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) * (jacobiSym b (quadraticPairKernel z.1 z.2) : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallMomentMain
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal small-kernel moment: original main term and two corrections -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators ComplexConjugate FourierTransform

noncomputable def quadraticSmallPairCorrection (M J : ℝ) (q b : ℕ) : ℂ :=
  let X := quadraticSmallScale M b
  let U := quadraticSecondLower X J
  let V := quadraticSecondUpper X J
  show ℂ from
  -(X : ℂ) * (∫ x in Ioi (0 : ℝ), quadraticSieveWeight (x ^ 2)) *
    (∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)), (ArithmeticFunction.moebius d : ℂ) / d) +
  (X : ℂ) / 2 *
    (∑ d ∈ q.divisors.filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
      ((ArithmeticFunction.moebius d : ℂ) / d) *
        quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest quadraticSieveWeight))
          (X / d) (quadraticSecondWindow J))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticOffDiagonalPairSums
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original off-diagonal pairs in the two Poisson transforms -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

noncomputable def quadraticSmallPairSum (M K D q : ℕ) : ℂ :=
  ∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·),
    (jacobiSym b q : ℂ) * ∑' c : ℕ+,
      (1 : DirichletCharacter ℂ (2 * (q * D))) (c : ZMod (2 * (q * D))) *
        quadraticSieveWeight ((c : ℝ) ^ 2 * b / M)

noncomputable def quadraticSmallPairCore (M K D q : ℕ) (J : ℝ) : ℂ :=
  ∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·),
    (jacobiSym b q : ℂ) * quadraticSmallDyadicCore quadraticSieveWeight M b J (2 * (q * D)) b

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGcdSecondFrequency
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal second-Poisson correction at one signed frequency -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators ComplexConjugate SchwartzMap FourierTransform

noncomputable def quadraticGcdSecondFrequency (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    (M H J : ℝ) (R D e b : ℕ) (u : ℤ) (v w : ℕ → ℂ) : ℂ :=
  ∑ z ∈ quadraticGcdPairs (2 * R) D,
    v z.1 * conj (w z.2) *
      (quadraticGaussMultiplier (quadraticPairKernel z.1 z.2) *
        (jacobiSym (u * b) (quadraticPairKernel z.1 z.2) : ℂ) *
        (((M / ((e : ℝ) * Real.sqrt (quadraticPairKernel z.1 z.2)) : ℝ) : ℂ) *
          quadraticSecondDyadicCorrection ρ a ha M H J e (quadraticPairKernel z.1 z.2) b))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGcdSecondTotal
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full signed second correction is exactly the three bounded sums -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators ComplexConjugate SchwartzMap FourierTransform

noncomputable def quadraticGcdSecondTotal (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    (M H J : ℝ) (R D e K : ℕ) (u : ℤ) (v w : ℕ → ℂ) : ℂ :=
  ∑ b ∈ oddSquarefreeRange K, quadraticGcdSecondFrequency ρ a ha M H J R D e b u v w

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticMomentMainComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual two transformed main terms, summed over the original pairs -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators ComplexConjugate

noncomputable def quadraticSmallPairMain (M D q K : ℕ) : ℂ :=
  ∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·),
    (quadraticSmallScale M b : ℂ) * (((2 * (q * D)).totient : ℂ) / (2 * (q * D) : ℕ)) *
      (∫ x in Ioi (0 : ℝ), quadraticSieveWeight (x ^ 2)) * (jacobiSym b q : ℂ)

noncomputable def quadraticPairMainDifference (M D q K : ℕ) : ℂ :=
  quadraticFirstSecondMainKernel M D q K - quadraticSmallPairMain M D q K

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticRoughBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restriction and divisor descent for the actual rough moment -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

noncomputable def quadraticRoughGcdMoment (M N K D : ℕ) (v : ℕ → ℂ) : ℂ :=
  ∑ m ∈ quadraticRoughKernelRange (3 * M) K,
    quadraticSieveWeight ((m : ℝ) / M) *
      (if (m : ℤ).gcd D = 1 then (1 : ℂ) else 0) * quadraticGcdKernelSum N D v m

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticRoughDyadic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Disjoint coefficient blocks for the actual rough moment -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticDyadicCoeff (N j : ℕ) (v : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ∈ quadraticDyadicDivisors N j then v n else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticRowNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The least constant for an actual finite set of quadratic rows -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticRowNorm (S : Finset ℕ) (N : ℕ) : ℝ :=
  sSup (Set.range fun v : ℕ → ℂ => quadraticRowEnergy S N v / quadraticSieveEnergy N v)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallGcdTransform
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual small-gcd moment in the Poisson comparison -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

noncomputable def quadraticGcdMomentCorrections (M R K D : ℕ) (J : ℝ)
    (v : ℕ → ℂ) : ℂ :=
  ∑ z ∈ quadraticGcdPairs (2 * R) D, v z.1 * conj (v z.2) *
    (quadraticFirstSecondCorrections M D (quadraticPairKernel z.1 z.2) K ((R : ℝ) / D) J -
      ∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·),
        (jacobiSym b (quadraticPairKernel z.1 z.2) : ℂ) *
          quadraticSmallPairCorrection M J (2 * (quadraticPairKernel z.1 z.2 * D)) b)

noncomputable def quadraticGcdMomentError (M R K D : ℕ) (J : ℝ) (v : ℕ → ℂ) : ℂ :=
  ∑ z ∈ quadraticGcdPairs (2 * R) D, v z.1 * conj (v z.2) *
    ((quadraticFirstKernelTransform M D (quadraticPairKernel z.1 z.2) -
      quadraticFirstKernelFinite M D (quadraticPairKernel z.1 z.2) K) +
     (quadraticFirstKernelFinite M D (quadraticPairKernel z.1 z.2) K -
      quadraticFirstSecondKernel M D (quadraticPairKernel z.1 z.2) K ((R : ℝ) / D) J) -
     (quadraticSmallPairSum M K D (quadraticPairKernel z.1 z.2) -
      quadraticSmallPairCore M K D (quadraticPairKernel z.1 z.2) J))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallTotalIdentity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full frequency assembly of the original small-kernel term -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators ComplexConjugate SchwartzMap FourierTransform

noncomputable def quadraticGcdSmallTotal (M J : ℝ) (R D K : ℕ) (v w : ℕ → ℂ) : ℂ :=
  ∑ z ∈ quadraticGcdPairs (2 * R) D, v z.1 * conj (w z.2) *
    ∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·),
      (jacobiSym b (quadraticPairKernel z.1 z.2) : ℂ) *
        quadraticSmallPairCorrection M J (2 * (quadraticPairKernel z.1 z.2 * D)) b

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticWideRows
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Adjacent dyadic intervals and the actual prime-dilation image -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticWideRows (M : ℕ) : Finset ℕ :=
  (oddSquarefreeRange (4 * M)).filter (M ≤ ·)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SparsePrincipalMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The principal coefficient is the exact unit-residue mean -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def unitNonzeroResidueEquiv (p : ℕ) [Fact p.Prime] :
    (ZMod p)ˣ ≃ NonzeroResidue p where
  toFun u := ⟨u, Finset.mem_erase.mpr ⟨Units.ne_zero u, Finset.mem_univ _⟩⟩
  invFun x := Units.mk0 x.val (Finset.mem_erase.mp x.property).1
  left_inv u := by apply Units.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

end Ostmann

end OAI
end


