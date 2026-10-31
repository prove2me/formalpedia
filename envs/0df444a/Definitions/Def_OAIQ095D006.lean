-- Prove2me | Definitions.Def_OAIQ095D006
-- name    : OAIQ095D006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:08:04.286009+00:00
-- url     : https://prove2.me/theorems/83698187-caa1-41fe-8b42-cf645f2b4d6d
-- title:
--   Definitions bundle OAIQ095D006 of the split of OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 111 declarations of OpenAI's Lean: 35 definitions, 1 instance and 75 theorems. The definitions and types are `OAI.Ostmann.actualProgressionInput`, `OAI.Ostmann.actualPublishedRealZeroInput`, `OAI.Ostmann.actualSmoothExplicitFormula`, `OAI.Ostmann.bulkFrequencyPageMean`, `OAI.Ostmann.bulkLogKernelPairIntegrand`, `OAI.Ostmann.bulkPrimeErrorFactor`, `OAI.Ostmann.correctedMixedPairAverage`, `OAI.Ostmann.densityCharacterFamily`, `OAI.Ostmann.densityZeroBin`, `OAI.Ostmann.densityZeroIndices`, `OAI.Ostmann.frozenBulkFrequencyFactor`, `OAI.Ostmann.frozenMixedUnitArithmeticMean`, `OAI.Ostmann.movingArithmeticPageFactor`, `OAI.Ostmann.movingFourierPolynomialFactors`, `OAI.Ostmann.movingFrequencyCorePageAverage`, `OAI.Ostmann.movingFrequencyPageAverage`, `OAI.Ostmann.movingFullSupport`, `OAI.Ostmann.movingGiantOffDiagonal`, `OAI.Ostmann.movingIndexedLine`, `OAI.Ostmann.movingInternalBaseFactor`, `OAI.Ostmann.movingInternalHaarAverage`, `OAI.Ostmann.movingInternalLineProbability`, `OAI.Ostmann.movingMaskedTemplateEnergy`, `OAI.Ostmann.movingMaskedTemplateKernel`, `OAI.Ostmann.movingNaturalGiantUnits`, `OAI.Ostmann.movingOriginalGiantWeight`, `OAI.Ostmann.movingPrimeOccurrenceLine`, `OAI.Ostmann.movingWindowLeaf`, `OAI.Ostmann.pageGiantWeight`, `OAI.Ostmann.primeGiantMeasure`, `OAI.Ostmann.progressionInput_of_actual_theta`, `OAI.Ostmann.selectedPageZero`, `OAI.Ostmann.selectedPrimeLogDensity`, `OAI.Ostmann.smoothExplicitFormula_of_individual`, `OAI.Ostmann.smoothExplicitFormula_of_multiplicity`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `Ostmann_Arithmetic_BulkFourierFactors`, `Ostmann_Arithmetic_BulkLogContinuity`, `Ostmann_Arithmetic_BulkLogSliceComparison`, `Ostmann_Arithmetic_BulkNodeFactors`, `Ostmann_Arithmetic_BulkResiduePageBound`, `Ostmann_Arithmetic_BulkSmoothFactors`, `Ostmann_Arithmetic_FrozenFrequencyAverage`, `Ostmann_Arithmetic_FrozenSupportedArithmetic`, `Ostmann_Arithmetic_MovingFourierPolynomials`, `Ostmann_Arithmetic_MovingFourierSupported`, `Ostmann_Arithmetic_MovingIndexedLineSystem`, `Ostmann_Arithmetic_MovingInternalBaseAverage`, `Ostmann_Arithmetic_MovingInternalProductError`, `Ostmann_Arithmetic_MovingMaskedTemplateEnergy`, `Ostmann_Arithmetic_MovingOriginalGiantWeight`, `Ostmann_Arithmetic_MovingPatternMixedNormalizedNorm`, `Ostmann_Arithmetic_MovingPrimeArithmeticTransfer`, `Ostmann_Arithmetic_MovingPrimeOccurrences`, `Ostmann_Arithmetic_MovingSeparatedAverages`, `Ostmann_Arithmetic_MovingSeparatedPageCRT`, `Ostmann_Arithmetic_MovingSignedUnits`, `Ostmann_Arithmetic_MovingSupportedWeight`, `Ostmann_Arithmetic_PrimeIntervalVariation`, `Ostmann_Arithmetic_RealBulkKernel`, `Ostmann_Arithmetic_RealBulkKernelPair`, `Ostmann_Characters_CharacterDiskGrowth`, `Ostmann_Characters_CharacterEnumerationCount`, `Ostmann_Characters_CharacterHorizontalGrowth`, `Ostmann_Characters_CharacterLeftGrowth`, `Ostmann_Characters_CharacterLogDerivativeGrowth`, `Ostmann_Characters_CharacterLogDerivativeLeft`, `Ostmann_Characters_CharacterPageComparison`, `Ostmann_Characters_CharacterSeparatedHeights`, `Ostmann_Construction_GiantLogMeasures`, `Ostmann_Construction_ScheduledHistoryEmbedding`, `Ostmann_MainWithoutProgression`, `Ostmann_ZeroDensity_ActualProgressionInput`, `Ostmann_ZeroDensity_ActualRealZeroExpansion`, `Ostmann_ZeroDensity_ActualThetaEstimate`, `Ostmann_ZeroDensity_ArithmeticRieszMean`, `Ostmann_ZeroDensity_CanonicalRieszKernelBound`, `Ostmann_ZeroDensity_CharacterCanonicalRieszComparison`, `Ostmann_ZeroDensity_CharacterCanonicalRieszDecay`, `Ostmann_ZeroDensity_CharacterContourDiskZeros`, `Ostmann_ZeroDensity_CharacterContourGrowth`, `Ostmann_ZeroDensity_CharacterContourLogGrowth`, `Ostmann_ZeroDensity_CharacterGammaContour`, `Ostmann_ZeroDensity_CharacterRieszLocalBound`, `Ostmann_ZeroDensity_CharacterRieszZeroSelection`, `Ostmann_ZeroDensity_DensityCharacterFamily`, `Ostmann_ZeroDensity_DensityZeroBins`, `Ostmann_ZeroDensity_GiantHaarDensity`, `Ostmann_ZeroDensity_InducedCharacterRieszDecay`, `Ostmann_ZeroDensity_PageSelection`, `Ostmann_ZeroDensity_PrimitiveCharacterCard`, `Ostmann_ZeroDensity_PrimitiveRieszComparison`, `Ostmann_ZeroDensity_PrincipalRieszDecay`, `Ostmann_ZeroDensity_PrincipalRieszSupply`, `Ostmann_ZeroDensity_ResiduePsiEstimate`, `Ostmann_ZeroDensity_ResiduePsiSmallModulus`, `Ostmann_ZeroDensity_ResidueRieszFinite`, `Ostmann_ZeroDensity_RieszCanonicalResidueMain`, `Ostmann_ZeroDensity_RieszResidueError`, `Ostmann_ZeroDensity_SmoothActualExplicitFormula`, `Ostmann_ZeroDensity_SmoothActualZeroSum`, `Ostmann_ZeroDensity_SmoothContourLimit`, `Ostmann_ZeroDensity_SmoothContourRegularPart`, `Ostmann_ZeroDensity_SmoothExplicitIdentity`, `Ostmann_ZeroDensity_SmoothFiniteRegularization`, `Ostmann_ZeroDensity_SmoothHorizontalBound`, `Ostmann_ZeroDensity_SmoothHorizontalLimit`, `Ostmann_ZeroDensity_SmoothLeftContourBound`, `Ostmann_ZeroDensity_SmoothLeftContourWeight`, `Ostmann_ZeroDensity_SmoothOriginResidue`, `Ostmann_ZeroDensity_SmoothRectangleResidues`, `Ostmann_ZeroDensity_SmoothTruncatedContour`, `Ostmann_ZeroDensity_SmoothZeroCountFamily`, `Ostmann_ZeroDensity_ZetaLocalFactorBound`, `Ostmann_ZeroDensity_ZetaLocalSeparation`, `Ostmann_ZeroDensity_ZetaNearZeroBound`, `Ostmann_ZeroDensity_ZetaTrigonometric`, `Ostmann_ZeroDensity_ZetaZeroFreeLogDerivative`, `Ostmann_ZeroDensity_ZetaZeroFreeRegion`.
--
--   **Imports.** It imports the bundles `OAIQ095D003`, `OAIQ095D004` and `OAIQ095D005` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ095D008`; the statement `OAI.Ostmann.PublishedProgressionInput.moving_outer_coprime_mixed_haar_rate`; the proofs of `OAI.Ostmann.EventuallyPrimeSumset.constructed_initial_amplitude`, `OAI.Ostmann.EventuallyPrimeSumset.sparse_tail_coverage`, `OAI_Ostmann_PublishedProgressionInput_concrete_character_band_contradiction`, `OAI_Ostmann_PublishedProgressionInput_moving_selected_initial_full_energy`, `OAI.Ostmann.densitySmoothedSquare_mean`, `OAI.Ostmann.density_packed_product_fourth`, `OAI.Ostmann.density_polynomial_alternative_balanced`, `OAI.Ostmann.eventual_character_anchor_decay`, `OAI_Ostmann_eventual_character_diagonal_decay`, `OAI_Ostmann_eventual_original_large_first_moment`, `OAI.Ostmann.eventual_selected_final_natural_energy_comparison`, `OAI_Ostmann_eventual_uniform_character_iteration_contradiction`, `OAI.Ostmann.inverseGoldbach_without_summand_size`, `OAI.Ostmann.publishedComplexZeroDensity`, `OAI.Ostmann.publishedQuadraticLargeSieve`, `OAI.Ostmann.publishedSummandSizeBound` and `OAI.Ostmann.twoInfiniteSummandsImpossible_without_summand_size`.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ095D003
import Definitions.Def_OAIQ095D004
import Definitions.Def_OAIQ095D005

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PageSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single exceptional character for every modulus in a row

Only zeros in Page's common region are retained. Local exceptional zeros
outside that region will be bounded as an error, rather than identified
with a character belonging to a different modulus.
-/

namespace Ostmann

open Classical

noncomputable def selectedPageZero (P : PublishedProgressionInput) (Q : ℕ) :
    Option PrimitiveRealZero :=
  if h : ∃ e : PrimitiveRealZero, e.modulus ≤ Q ∧
      1 - P.kappa / Real.log (4 * (Q : ℝ)) ≤ e.beta then some h.choose else none

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_PrimeIntervalVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted short prime intervals from the published progression input -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators

/-- The reference density is the actual selected Page-corrected density.
It stays inside the integral throughout weighted summation. -/
noncomputable def selectedPrimeLogDensity (P : PublishedProgressionInput) (Q q a : ℕ) : ℝ → ℝ :=
  primeLogDensity (Nat.totient q)
    (pageCoefficient (pageAtModulus q (selectedPageZero P Q)) a)
    (pageBeta (pageAtModulus q (selectedPageZero P Q)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFourierPolynomials
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete polynomial factors in the moving Fourier history -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate SchwartzMap

/-- Exactly one clipped Fourier polynomial per terminal leaf, with the
conjugation imposed by its actual left/right path. -/
noncomputable def movingFourierPolynomialFactors {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) : Fin (2 ^ n) → ClippedPolynomialFactor :=
  fun j =>
    let i := (movingLeafIndexEquiv n).symm j
    let f := fourierPolynomialFactor (movingLeafNormalizedPolynomial value T L R X i)
      ψ (T.leafFrequencies i) lo hi hlo hhi
    if treeLeafTupleEquiv Bool n (transferConjugations n false) i then f.conjugate else f

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFourierSupported
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The supported original coefficient is the constructed polynomial weight -/

namespace Ostmann
open scoped Classical SchwartzMap

noncomputable def movingWindowLeaf {σ : Type*} (value : σ → ℕ)
    (X lo hi : ℝ) (F : MovingSlotState σ → ℤ → ℂ) (x : MovingSlotState σ) (s : ℤ) : ℂ :=
  if (movingSlotModulus value x : ℝ) / X ∈ Set.Icc lo hi then F x s else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSignedUnits
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The giant unit tests on signed residue representatives -/

namespace Ostmann
open scoped Classical

def movingNaturalGiantUnits {σ : Type*} (value : σ → ℕ) (outside : List ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℕ → ℕ → Prop
  | _, T@(.leaf _ _), XL, XR => movingLocalGiantUnits value outside T XL XR
  | _, T@(.node s CL CR U left right), XL, XR =>
      let p := (MovingSlotData.step s CL CR U left right false).naturalPivot value XL XR
      movingLocalGiantUnits value outside T XL XR ∧
        movingNaturalGiantUnits value outside left p XL ∧
        movingNaturalGiantUnits value outside right p XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkFourierFactors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Clipped Fourier factors along an original bulk-prime coordinate -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap ComplexConjugate

theorem bulkFourierFactors_value {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (hT : T.CompensationAbsent i)
    (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (p : ℝ) :
    smoothPolynomialWeight (bulkFourierFactors value i T L R ψ X lo hi hlo hhi) (p : ℝ) =
      realValueFourierWeight (Function.update value i p) T ψ X lo hi hlo hhi
        (L.eval (p : ℝ)) (R.eval (p : ℝ)) := by
  unfold smoothPolynomialWeight realValueFourierWeight
  rw [← (movingLeafIndexEquiv n).prod_comp]
  apply Finset.prod_congr rfl
  intro leaf _
  have hm := T.bulkLeafPolynomials_eval value i hT L R p leaf
  have he : (Polynomial.C X⁻¹ * T.bulkLeafPolynomials value i L R leaf).eval (p : ℝ) =
      T.realValueLeafModuli (Function.update value i p) (L.eval (p : ℝ)) (R.eval (p : ℝ)) leaf / X := by
    rw [Polynomial.eval_mul, Polynomial.eval_C, hm]
    ring
  simp only [bulkFourierFactors, Equiv.symm_apply_apply]
  split_ifs <;> simp only [ClippedPolynomialFactor.conjugate, ClippedPolynomialFactor.value,
    fourierPolynomialFactor, he, Polynomial.eval_X]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkNodeFactors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original node cutoffs with one free bulk coordinate -/

namespace Ostmann
open scoped Classical BigOperators

theorem bulkNodeFactors_value {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (hT : T.CompensationAbsent i)
    (L R : Polynomial ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (p : ℝ) :
    smoothPolynomialWeight (bulkNodeFactors value i T L R φ G B D hB hD hφ hlip) (p : ℝ) =
      realValueNodeCutoff (Function.update value i p) φ G T (L.eval (p : ℝ)) (R.eval (p : ℝ)) := by
  unfold smoothPolynomialWeight
  simp only [bulkNodeFactors, logCutoffPolynomialFactor_value _ _ _ _ _ _ _ hφ hlip hout]
  rw [← T.bulkNodePolynomials_value value i φ G hT L R p]
  exact (Fin.prod_ofFn _).symm.trans (congrArg List.prod
    (List.ofFn_getElem_eq_map (T.bulkNodePolynomials value i L R)
      (fun f => (positiveLogCutoff φ (G f.1) (f.2.eval (p : ℝ)) : ℂ))))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkSmoothFactors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full smooth bulk-coordinate factor and its finite variation budget -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem bulkSmoothFactors_value {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (hT : T.CompensationAbsent i)
    (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (p : ℝ) :
    smoothPolynomialWeight (bulkSmoothFactors value i T L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip)
      (p : ℝ) = realValueSmoothWeight (Function.update value i p) T ψ X lo hi hlo hhi φ G
        (L.eval (p : ℝ)) (R.eval (p : ℝ)) := by
  simp only [smoothPolynomialWeight, bulkSmoothFactors, Fin.prod_univ_add,
    Fin.append_left, Fin.append_right]
  exact congrArg₂ (· * ·) (bulkFourierFactors_value value i T hT L R ψ X lo hi hlo hhi p)
    (bulkNodeFactors_value value i T hT L R φ G B D hB hD hφ hlip hout p)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkLogContinuity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The smooth tree as a continuous function of the bulk logarithms -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap ComplexConjugate BoundedContinuousFunction

theorem continuous_bulkLogFourierWeight {σ : Type*} (base : σ → ℝ) (S : Finset σ)
    {n : ℕ} (T : MovingSlotData σ n) (hT : ∀ i ∈ S, T.CompensationAbsent i)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (L R : (σ → ℝ) → ℝ) (hL : Continuous L) (hR : Continuous R) :
    Continuous (fun x => realValueFourierWeight (bulkLogValues base S x) T ψ X lo hi hlo hhi
      (L x) (R x)) := by
  apply continuous_finsetProd
  intro j _
  have hc := (fourierPolynomialFactor Polynomial.X ψ (T.leafFrequencies j) lo hi hlo hhi).continuous_value.comp
    ((T.continuous_bulkLogLeafModuli base S hT L R hL hR j).div_const X)
  dsimp only
  split_ifs
  · exact Complex.continuous_conj.comp hc
  · exact hc

theorem continuous_bulkLogNodeCutoff {σ : Type*} (base : σ → ℝ) (S : Finset σ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    {n : ℕ} (T : MovingSlotData σ n) (hT : ∀ i ∈ S, T.CompensationAbsent i)
    (L R : (σ → ℝ) → ℝ) (hL : Continuous L) (hR : Continuous R) :
    Continuous (fun x => realValueNodeCutoff (bulkLogValues base S x) φ G T (L x) (R x)) := by
  have hp (g : ℝ) : Continuous (fun x => (positiveLogCutoff φ g x : ℂ)) := by
    have he (x : ℝ) := logCutoffPolynomialFactor_value Polynomial.X φ g B D hB hD hφ hlip hout x
    simp only [Polynomial.eval_X] at he
    exact ((logCutoffPolynomialFactor Polynomial.X φ g B D hB hD hφ hlip).continuous_value).congr he
  induction T generalizing L R with
  | leaf => exact continuous_const
  | @node n s CL CR u left right ihL ihR =>
    have hc := (MovingSlotData.step s CL CR u left right false).continuous_bulkLogPivot
      base S (fun i hi => (hT i hi).1) L R hL hR
    exact (((hp (G (n + 1))).comp hc).mul
      (ihL (fun i hi => (hT i hi).2.1) _ L hc hL)).mul
      (ihR (fun i hi => (hT i hi).2.2) _ R hc hR)

theorem continuous_bulkLogSmoothWeight {σ : Type*} (base : σ → ℝ) (S : Finset σ)
    {n : ℕ} (T : MovingSlotData σ n) (hT : ∀ i ∈ S, T.CompensationAbsent i)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (L R : (σ → ℝ) → ℝ) (hL : Continuous L) (hR : Continuous R) :
    Continuous (fun x => realValueSmoothWeight (bulkLogValues base S x) T ψ X lo hi hlo hhi
      φ G (L x) (R x)) :=
  (continuous_bulkLogFourierWeight base S T hT ψ X lo hi hlo hhi L R hL hR).mul
    (continuous_bulkLogNodeCutoff base S φ G B D hB hD hφ hlip hout T hT L R hL hR)

/-- The bound is uniform in all real bulk variables and both giant arguments. -/
theorem realValueSmoothWeight_norm {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (hT : T.CompensationAbsent i)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : T.Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (L R : ℝ) :
    ‖realValueSmoothWeight value T ψ X lo hi hlo hhi φ G L R‖ ≤
      movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1) := by
  have he := bulkSmoothFactors_value value i T hT (Polynomial.C L) (Polynomial.C R)
    ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout (value i)
  simp only [Function.update_eq_self, Polynomial.eval_C] at he
  rw [← he]
  exact (smoothPolynomialWeight_norm _ _).trans
    (bulkSmoothFactors_budget value i T _ _ ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantLogMeasures
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual ideal giant measures, including the retained Page density -/

namespace Ostmann
open MeasureTheory
open scoped ENNReal

theorem selectedPrimeLogDensity_nonneg (P : PublishedProgressionInput) (Q q a : ℕ)
    (u v : ℝ) (hu : 0 ≤ u) (x : ℝ) (hx : x ∈ Set.Ioc u v) :
    0 ≤ selectedPrimeLogDensity P Q q a x :=
  (primeLogDensity_bounds _ _ _ (Nat.cast_nonneg _) (pageCoefficient_abs_le_one _ _)
    (pageBeta_le_one _) (hu.trans hx.1.le)).1

theorem selectedPrimeLogDensity_integrable (P : PublishedProgressionInput) (Q q a : ℕ)
    (u v : ℝ) (hu : 0 < u) : IntegrableOn (selectedPrimeLogDensity P Q q a) (Set.Ioc u v) :=
  (continuousOn_primeLogDensity _ _ _ hu).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self

noncomputable def primeGiantMeasure (P : PublishedProgressionInput) (Q q a : ℕ)
    (u v : ℝ) : Measure ℝ := intervalDensityMeasure u v (selectedPrimeLogDensity P Q q a)

theorem finite_primeGiantMeasure (P : PublishedProgressionInput) (Q q a : ℕ)
    (u v : ℝ) (hu : 0 < u) : IsFiniteMeasure (primeGiantMeasure P Q q a u v) :=
  finite_intervalDensityMeasure u v _ (selectedPrimeLogDensity_integrable P Q q a u v hu)
    (selectedPrimeLogDensity_nonneg P Q q a u v hu.le)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkLogSliceComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual prime and Page averages of a bulk coordinate -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap BoundedContinuousFunction

noncomputable def bulkPrimeErrorFactor (P : PublishedProgressionInput) (Q : ℕ) (u : ℝ) : ℝ :=
  18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
    Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ))) + 2 * Real.exp (-u)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOriginalGiantWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A name for the literal original recursive giant coefficient -/

namespace Ostmann
open scoped BigOperators Classical SchwartzMap

noncomputable def movingOriginalGiantWeight {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (XL XR : ℕ) : ℂ :=
  recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
    (fun x s => (movingWindowLeaf value X lo hi (movingDataLeaf F) x s *
      movingFourierLeaf value ψ X x s) *
        ∏ i ∈ S, spectatorHistoryLeaf (movingSlotModulus value) (g i) (Dq i) x s)
    (movingSlotCutoff value childBound pivotBound
      (movingPhiExtra value childBound pivotBound (movingDataExtra E) φ G)) n ⟨n, T, XL, XR⟩ t

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

noncomputable def movingFullSupport {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) : Prop :=
  movingFullOutsidePairwise value outside T XL XR ∧ movingNaturalGiantUnits value outside T XL XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_GiantHaarDensity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact Haar residue factors inside the real giant integral -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def pageGiantWeight (P : PublishedProgressionInput) (Q q a : ℕ) (x : ℝ) : ℂ :=
  (pageMultiplier (fun a => pageCoefficient (pageAtModulus q (selectedPageZero P Q)) a)
    (pageBeta (pageAtModulus q (selectedPageZero P Q))) x a : ℝ)

noncomputable def correctedMixedPairAverage (P : PublishedProgressionInput) (Q q : ℕ) [NeZero q]
    (c : ℕ → ℕ → ℂ) (y : ℝ) : ℂ :=
  (Fintype.card (ZMod q × (ZMod q)ˣ) : ℂ)⁻¹ *
    ∑ z : ZMod q × (ZMod q)ˣ,
      c z.1.val (z.2 : ZMod q).val * pageGiantWeight P Q q (z.2 : ZMod q).val y

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkResiduePageBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Norm bound after exact bulk CRT separation -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def bulkFrequencyPageMean {J : Type*} [Fintype J]
    (P : PublishedProgressionInput) (Q r : ℕ) [NeZero r]
    (y : J → ℝ) (F : (J → (ZMod r)ˣ) → ℂ) : ℂ :=
  (Fintype.card (J → (ZMod r)ˣ) : ℂ)⁻¹ *
    ∑ a, F a * ∏ j, pageGiantWeight P Q r (a j).val.val (y j)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPrimeOccurrences
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous occurrences of one actual internal prime in both histories -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingPrimeOccurrenceLine {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ)
    (j : MovingPrimeOccurrences value T p) : PolynomialGiantLine σ :=
  let o := movingPrimeOccurrence value T p j
  movingSlotLine o.path o.current

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingInternalBaseAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual internal-prime averages after removing their square exclusions -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingInternalBaseFactor {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ)
    (x y : ZMod p) : ℂ :=
  if ∀ j : MovingPrimeOccurrences value T p,
    let φ := MovingSlotReversal.naturalReduction p value
    let L := movingPrimeOccurrenceLine value T p j
    φ L.a * x + φ L.b * y = 0 then 1 else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingInternalProductError
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous square removal with the full internal-prime scale -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingInternalHaarAverage {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ) [Fact p.Prime] : ℂ :=
  (Fintype.card (ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ) : ℂ)⁻¹ *
    ∑ z : ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ, movingInternalPairFactor value T p z.1 z.2

noncomputable def movingInternalLineProbability {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ) [Fact p.Prime] : ℝ :=
  internalLineProbability true
    (fun j => MovingSlotReversal.naturalReduction p value
      (movingPrimeOccurrenceLine value T p j).a)
    (fun j => MovingSlotReversal.naturalReduction p value
      (movingPrimeOccurrenceLine value T p j).b)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSeparatedPageCRT
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining the Page correction in the frequency block -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingArithmeticPageFactor {I : Type*}
    (r : ℕ) (q : I → ℕ) (P : Finset ℕ) (S : Finset I)
    (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ)
    (f : ∀ b, ZMod (movingArithmeticModuli r q P S b) ×
      (ZMod (movingArithmeticModuli r q P S b))ˣ → ℂ) :
    ∀ b, ZMod (movingArithmeticModuli r q P S b) ×
      (ZMod (movingArithmeticModuli r q P S b))ˣ → ℂ
  | .inl u, z => f (.inl u) z *
      pageGiantWeight input Q r (show (ZMod r)ˣ from z.2).val.val y
  | .inr b, z => f (.inr b) z

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

noncomputable def movingFrequencyPageAverage {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ) : ℂ :=
  (Fintype.card (ZMod r × (ZMod r)ˣ) : ℂ)⁻¹ *
    ∑ z : ZMod r × (ZMod r)ˣ,
      movingFrequencyPairFactor value outside F E T nodes R z.1.val z.2.val.val *
        pageGiantWeight input Q r z.2.val.val y

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrozenFrequencyAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The frequency/Page average on the fixed bulk residue representative -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def movingFrequencyCorePageAverage {σ : Type*} (value : σ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (R : ℤ)
    (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ) : ℂ :=
  (Fintype.card (ZMod r × (ZMod r)ˣ) : ℂ)⁻¹ *
    ∑ z : ZMod r × (ZMod r)ˣ,
      movingFrequencyCore value F E T R z.1.val z.2.val.val *
        pageGiantWeight input Q r z.2.val.val y

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrozenSupportedArithmetic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped Classical BigOperators

noncomputable def frozenBulkFrequencyFactor {σ J : Type*}
    (base : σ → ℕ) (slot : J ↪ σ) (outside : List ℕ)
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (E : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (childBound : ℕ → ℕ)
    (R : ℤ) (r : ℕ) [NeZero r] (input : PublishedProgressionInput)
    (Q : ℕ) (y : ℝ) (a : J → (ZMod r)ˣ) : ℂ :=
  (if ∀ b, movingNonbulkOutsidePairwise base (bulkIndexPredicate slot) outside (T b) ∧
      (T b).FrequencyBounds childBound then (1 : ℂ) else 0) *
    movingFrequencyCorePageAverage (Function.extend slot (fun j => (a j).val.val) base)
      F E T R r input Q y

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

noncomputable def movingIndexedLine {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) (rep : σ) (base : MovingPairRepresentativeOccurrences T rep)
    (o : MovingPairOccurrenceIndex T) : PolynomialGiantLine σ :=
  movingSlotLine (movingIndexedOccurrence T rep base o).path
    (movingIndexedOccurrence T rep base o).current

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

noncomputable instance nonzeroScheduledHistoryFintype (V : ℕ → ℕ) (n : ℕ) :
    Fintype (NonzeroScheduledHistory V n) := by
  infer_instance

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPrimeArithmeticTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The weighted giant-only integer substitution of Section 7.5 -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- The inserted giant is `N / (s * U)`. The compensation product `U` is
retained, so the reconstructed integer is the giant and not the whole pivot. -/
noncomputable def movingGiantOffDiagonal {A : Type*} [Fintype A]
    (I : Finset ℕ) (V U : ℕ) (L : A → ℕ) (v : A → ℤ)
    (w : ℕ → ℝ) (c : ℕ → A → ℂ) : ℂ :=
  ∑ s ∈ transferFrequencyRange V, ∑ a, ∑ b,
    if validTransferredPivot I (v a * L b - v b * L a) (s * U) then
      let p := reconstructedPivot (v a * L b - v b * L a) (s * U)
      (w p : ℂ) * c p a * conj (c p b)
    else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RealBulkKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full original kernel on real bulk coordinates -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap ComplexConjugate

theorem isClosed_bulkLogNodeSupport {σ : Type*} (base : σ → ℝ) (S : Finset σ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hT : ∀ i ∈ S, T.CompensationAbsent i) (L R : (σ → ℝ) → ℝ)
    (hL : Continuous L) (hR : Continuous R) :
    IsClosed {x | realValueNodeSupport (bulkLogValues base S x) childBound pivotBound T (L x) (R x)} := by
  induction T generalizing L R with
  | leaf => simpa only [realValueNodeSupport, Set.ofPred_true] using isClosed_univ
  | @node n s CL CR u left right ihL ihR =>
    let step := MovingSlotData.step s CL CR u left right false
    have hQ := step.continuous_bulkLogComposite base S L R hL hR
    have hp := step.continuous_bulkLogPivot base S (fun i hi => (hT i hi).1) L R hL hR
    have hgap := hR.mul (continuous_realSlotProduct _ (continuous_bulkLogValues base S) CR)
    exact (isClosed_le continuous_const hQ).inter
      ((isClosed_le hQ continuous_const).inter ((isClosed_le continuous_const hgap).inter
        ((ihL (fun i hi => (hT i hi).2.1) _ L hp hL).inter
          (ihR (fun i hi => (hT i hi).2.2) _ R hp hR))))

theorem isClosed_bulkLogFullSupport {σ : Type*} (base : σ → ℝ) (S : Finset σ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hT : ∀ i ∈ S, T.CompensationAbsent i) (X lo hi : ℝ) (L R : (σ → ℝ) → ℝ)
    (hL : Continuous L) (hR : Continuous R) :
    IsClosed {x | realValueFullSupport (bulkLogValues base S x) childBound pivotBound T X lo hi (L x) (R x)} := by
  have hw : IsClosed {x | ∀ j, T.realValueLeafModuli (bulkLogValues base S x) (L x) (R x) j / X ∈ Set.Icc lo hi} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro j
    exact isClosed_Icc.preimage ((T.continuous_bulkLogLeafModuli base S hT L R hL hR j).div_const X)
  exact (isClosed_bulkLogNodeSupport base S childBound pivotBound T hT L R hL hR).inter hw

theorem measurable_bulkLogKernel {σ : Type*} [Fintype σ] (base : σ → ℝ) (S : Finset σ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hT : ∀ i ∈ S, T.CompensationAbsent i) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (L R : ℝ) : Measurable (fun x => realValueKernel (bulkLogValues base S x)
      childBound pivotBound T ψ X lo hi hlo hhi φ G L R) := by
  have hg : Measurable (fun x => realValueSupportFlag (bulkLogValues base S x)
      childBound pivotBound T X lo hi L R) := by
    unfold realValueSupportFlag
    exact Measurable.ite
      (isClosed_bulkLogFullSupport base S childBound pivotBound T hT X lo hi
        (fun _ => L) (fun _ => R) continuous_const continuous_const).measurableSet
      measurable_const measurable_const
  exact hg.mul (continuous_bulkLogSmoothWeight base S T hT ψ X lo hi hlo hhi φ G B D hB hD
    hφ hlip hout (fun _ => L) (fun _ => R) continuous_const continuous_const).measurable

theorem realValueKernel_norm {σ : Type*} (value : σ → ℝ) (i : σ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n) (hT : T.CompensationAbsent i)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : T.Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (L R : ℝ) :
    ‖realValueKernel value childBound pivotBound T ψ X lo hi hlo hhi φ G L R‖ ≤
      movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1) := by
  rw [realValueKernel, norm_mul]
  have hb := realValueSmoothWeight_norm value i T hT ψ X lo hi V hlo hhi hV
    φ G B D hB hD hφ hlip hout L R
  exact (mul_le_mul_of_nonneg_right (realValueSupportFlag_norm _ _ _ _ _ _ _ _ _) (norm_nonneg _)).trans
    (by simpa only [one_mul] using hb)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RealBulkKernelPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original paired kernel as a bounded measurable bulk integrand -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap ComplexConjugate

noncomputable def bulkLogKernelPairIntegrand {σ : Type*} [Fintype σ]
    (base : σ → ℝ) (S : Finset σ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hT : ∀ b i, i ∈ S → (T b).CompensationAbsent i)
    (i : σ) (hiS : i ∈ S) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (hV : ∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (L R : ℝ) : BulkIntegrand σ where
  toFun x := realValueKernelPair (bulkLogValues base S x) childBound pivotBound T ψ X lo hi hlo hhi φ G L R
  measurable := (measurable_bulkLogKernel base S childBound pivotBound (T false) (hT false)
    ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout L R).mul
    (Complex.continuous_conj.measurable.comp (measurable_bulkLogKernel base S childBound pivotBound
      (T true) (hT true) ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout L R))
  bounded := by
    let W := movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)
    have hb (b : Bool) (x : σ → ℝ) := realValueKernel_norm (bulkLogValues base S x) i childBound pivotBound
      (T b) (hT b i hiS) ψ X lo hi V hlo hhi (hV b) φ G B D hB hD hφ hlip hout L R
    have hW : 0 ≤ W := (norm_nonneg _).trans (hb false base)
    refine ⟨W ^ 2, sq_nonneg _, fun x => ?_⟩
    rw [realValueKernelPair, norm_mul, Complex.norm_conj, pow_two]
    exact mul_le_mul (hb false x) (hb true x) (norm_nonneg _) hW

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingMaskedTemplateEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The one-branch energy with its actual compensation mask -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingMaskedTemplateKernel
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ)
    (x : MovingRegularSlot n (4 + r) m → P) (p X : ℕ) (s : ℤ) : ℝ :=
  let q := fun i => (x i : ℕ)
  let _ : ∀ i, Fact (q i).Prime := fun i => ⟨hP _ (x i).property⟩
  ‖movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
      n (4 + r) m s x p X‖ ^ 2 *
    naturalRegularMultiplier q (movingRestoredActive n r m) s
      (fun i => ((outside.prod * tupleCofactor q i : ℕ) : ZMod (q i)))
      (fun i => greg (q i)) p X

noncomputable def movingMaskedTemplateEnergy
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
            movingMaskedTemplateKernel P hP outside μ childBound pivotBound V F φ G n r m
              greg x p X s.val)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternMixedNormalizedNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mixed arithmetic norm with distinct giant and bulk Page cutoffs -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def frozenMixedUnitArithmeticMean {σ I : Type*} [Fintype I]
    (base : σ → ℕ) (n m R : ℕ) [NeZero (R ^ (n - 1 + 2))]
    (ts : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List σ) n)
    (a : Bool → MovingSampleSlots σ n) (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (outside : List ℕ) (childBound : ℕ → ℕ) (input : PublishedProgressionInput) (Qfreq Qbulk : ℕ)
    (Y : ℝ) (p : I → ℕ) [∀ i, Fact (p i).Prime]
    [NeZero (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli (R ^ (n - 1 + 2)) p i).Coprime
      (bulkResidueModuli (R ^ (n - 1 + 2)) p j)))
    (g : ∀ i, ZMod (p i) → ℂ) (twist : ∀ i, Bool → (ZMod (p i))ˣ)
    (Ybulk : TreeLeafIndex n × Fin m → ℝ) : ℝ :=
  let T := fun b => buildMovingSlotData n (ts b) (small b) (bulkSlotLeaves n m slot) (a b)
  let Freq := frozenBulkFrequencyFactor base slot outside F (fun _ _ _ _ _ => 1) T childBound R
    (R ^ (n - 1 + 2)) input Qfreq Y
  let Spec := fun i => frozenBulkSpectatorHaar base n m ts small a (twist i) (Equiv.refl _) (g i)
  (Fintype.card (TreeLeafIndex n × Fin m →
    (ZMod (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i))ˣ) : ℝ)⁻¹ *
    ∑ x : TreeLeafIndex n × Fin m → (ZMod (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i))ˣ,
      ‖(Freq (bulkResidueEquiv (R ^ (n - 1 + 2)) p hc x).1 *
        ∏ j, pageGiantWeight input Qbulk (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i)
          (x j).val.val (Ybulk j)) *
        ∏ i, Spec i ((bulkResidueEquiv (R ^ (n - 1 + 2)) p hc x).2 i)‖

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterGammaContour
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual character Gamma factors on both vertical contour lines -/

namespace Ostmann

open Complex
open scoped Classical

theorem characterGammaInverse_contour_bound : ∃ B : ℝ, 0 < B ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ),
      (s.re = -(1 / 2 : ℝ) ∨ s.re = 3 / 2) →
      ‖logDeriv χ.gammaInverse s‖ ≤ B * (1 + |s.im|) := by
  obtain ⟨B, hB, hbound⟩ := characterGamma_contour_bound
  refine ⟨B, hB, ?_⟩
  intro χ s hs
  have he := logDeriv_fun_zpow (χ.gammaFactor_differentiableAt s hs) (-1 : ℤ)
  have hi : logDeriv χ.gammaInverse s = -logDeriv (DirichletCharacter.gammaFactor χ.character) s := by
    rw [show χ.gammaInverse = (fun x => (DirichletCharacter.gammaFactor χ.character x)⁻¹) from rfl]
    simpa only [zpow_neg_one, Int.cast_neg, Int.cast_one, neg_one_mul] using he
  rw [hi, norm_neg]
  exact hbound χ s hs

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterLeftGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential-type growth of the actual character L-function on the left strip -/

namespace Ostmann

open Complex

theorem character_L_left_growth : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ), -(3 / 4 : ℝ) ≤ s.re → s.re ≤ 1 / 2 →
      ‖χ.L s‖ ≤ C * (χ.modulus : ℝ) ^ 4 * (2 + |s.im|) * Real.exp (Real.pi * |s.im|) := by
  obtain ⟨G, hG, hGamma, hGammaInv⟩ := characterGamma_growth_bounds
  refine ⟨4 * G ^ 2, by positivity, ?_⟩
  intro χ s hs hs'
  have hq : 1 ≤ (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  have hqpos : 0 < (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  have hr : (1 / 2 : ℝ) ≤ (1 - s).re := by simp; linarith
  have hr' : (1 - s).re ≤ (7 / 4 : ℝ) := by simp; linarith
  have hn : ‖1 - s‖ ≤ 2 + |s.im| := by
    calc
      _ ≤ |(1 - s).re| + |(1 - s).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ _ := by
        rw [abs_of_nonneg (by linarith : 0 ≤ (1 - s).re)]
        simp only [sub_re, one_re, sub_im, one_im, zero_sub, abs_neg]
        linarith
  have hLi0 := χ.inverse.L_norm_bound_positive (1 - s) (by linarith)
  simp only [PrimitiveComplexCharacter.inverse_modulus] at hLi0
  have hLi : ‖χ.inverse.L (1 - s)‖ ≤ 4 * (χ.modulus : ℝ) * (2 + |s.im|) := by
    apply hLi0.trans
    apply (div_le_iff₀ (by linarith : 0 < (1 - s).re)).mpr
    have hmul : ‖1 - s‖ * ((χ.modulus : ℝ) + 1) ≤
        (2 + |s.im|) * (2 * (χ.modulus : ℝ)) :=
      mul_le_mul hn (by linarith) (by positivity) (by positivity)
    nlinarith [mul_nonneg (by positivity : 0 ≤ (χ.modulus : ℝ) * (2 + |s.im|))
      (sub_nonneg.mpr hr)]
  have hp : ‖(χ.modulus : ℂ) ^ (1 / 2 - s)‖ ≤ (χ.modulus : ℝ) ^ 2 := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hqpos]
    calc
      _ ≤ (χ.modulus : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hq (by simp; linarith)
      _ = _ := Real.rpow_two _
  have hGa := hGamma χ.inverse (1 - s) hr hr'
  have hGi := hGammaInv χ s hs hs'
  rw [χ.L_reflection_product s (by linarith)]
  simp only [norm_mul]
  calc
    _ ≤ (χ.modulus : ℝ) ^ 2 * (χ.modulus : ℝ) *
        (4 * (χ.modulus : ℝ) * (2 + |s.im|)) * G * (G * Real.exp (Real.pi * |s.im|)) := by
      gcongr
      exact χ.rootNumber_norm_le
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterContourGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual L-function growth on the fixed strip around the contour -/

namespace Ostmann

open Complex

theorem character_L_contour_strip_growth : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ), -(3 / 4 : ℝ) ≤ s.re → s.re ≤ 5 →
      ‖χ.L s‖ ≤ C * (χ.modulus : ℝ) ^ 4 * (6 + |s.im|) * Real.exp (Real.pi * |s.im|) := by
  obtain ⟨A, hA, hleft⟩ := character_L_left_growth
  refine ⟨max A 4, lt_of_lt_of_le hA (le_max_left _ _), ?_⟩
  intro χ s hs hs'
  have hq : 1 ≤ (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  have hqpos : 0 < (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  by_cases hl : s.re ≤ 1 / 2
  · apply (hleft χ s hs hl).trans
    gcongr
    · exact le_max_left _ _
    · norm_num
  · have hpos : 0 < s.re := by linarith
    have hn : ‖s‖ ≤ 5 + |s.im| := by
      apply (Complex.norm_le_abs_re_add_abs_im s).trans
      rw [abs_of_pos hpos]
      linarith
    have hb : ‖χ.L s‖ ≤ 4 * (χ.modulus : ℝ) * (5 + |s.im|) := by
      apply (χ.L_norm_bound_positive s hpos).trans
      apply (div_le_iff₀ hpos).mpr
      have hp : ‖s‖ * ((χ.modulus : ℝ) + 1) ≤ (5 + |s.im|) * (2 * (χ.modulus : ℝ)) :=
        mul_le_mul hn (by linarith) (by positivity) (by positivity)
      nlinarith [mul_nonneg (by positivity : 0 ≤ (χ.modulus : ℝ) * (5 + |s.im|))
        (by linarith : 0 ≤ s.re - 1 / 2)]
    calc
      _ ≤ 4 * (χ.modulus : ℝ) * (5 + |s.im|) := hb
      _ ≤ 4 * (χ.modulus : ℝ) ^ 4 * (6 + |s.im|) := by
        gcongr
        · exact le_self_pow₀ hq (by norm_num)
        · norm_num
      _ ≤ max A 4 * (χ.modulus : ℝ) ^ 4 * (6 + |s.im|) := by
        gcongr
        exact le_max_right _ _
      _ ≤ _ := le_mul_of_one_le_right (by positivity)
        (Real.one_le_exp (by positivity))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterDiskGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Growth on the fixed disks used for horizontal contour edges -/

namespace Ostmann

open Complex Metric

theorem character_L_contour_disk_growth : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (t : ℝ) (z : ℂ),
      z ∈ closedBall (characterZeroCenter t) (11 / 4 : ℝ) →
      ‖χ.L z‖ ≤ C * (χ.modulus : ℝ) ^ 4 * (9 + |t|) *
        Real.exp (Real.pi * (|t| + 3)) := by
  obtain ⟨C, hC, hbound⟩ := character_L_contour_strip_growth
  refine ⟨C, hC, ?_⟩
  intro χ t z hz
  have hn : ‖z - characterZeroCenter t‖ ≤ 11 / 4 := by
    simpa only [mem_closedBall, dist_eq_norm] using hz
  have hr := (abs_re_le_norm (z - characterZeroCenter t)).trans hn
  have hi := (abs_im_le_norm (z - characterZeroCenter t)).trans hn
  simp only [sub_re, sub_im, characterZeroCenter] at hr hi
  simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im,
    mul_one, mul_zero, add_zero, sub_zero] at hr hi
  norm_num at hr hi
  have hre : -(3 / 4 : ℝ) ≤ z.re ∧ z.re ≤ 5 := by
    have hh := abs_le.mp hr
    constructor <;> linarith
  have him : |z.im| ≤ |t| + 3 := by
    calc
      |z.im| = |(z.im - t) + t| := by congr 1; ring
      _ ≤ |z.im - t| + |t| := abs_add_le _ _
      _ ≤ |t| + 3 := by linarith
  apply (hbound χ z hre.1 hre.2).trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left him (by positivity))
  · positivity
  · positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrimitiveCharacterCard
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The elementary conductor-family cardinality bound -/
namespace Ostmann
open scoped Classical BigOperators

theorem primitive_character_fiber_card (F : Finset PrimitiveComplexCharacter)
    (q : ℕ) (hq : 0 < q) : (F.filter (fun χ => χ.modulus = q)).card ≤ q := by
  let S := F.filter (fun χ => χ.modulus = q)
  let f : S → DirichletCharacter ℂ q := fun χ =>
    χ.val.atModulus q (Finset.mem_filter.mp χ.property).2
  have hf : Function.Injective f := by
    intro χ ψ he
    apply Subtype.ext
    have hχ := (Finset.mem_filter.mp χ.property).2
    have hψ := (Finset.mem_filter.mp ψ.property).2
    obtain ⟨⟨m, hm, c, hc, hn⟩, hmem⟩ := χ
    obtain ⟨⟨n, hp, d, hd, hd'⟩, hmem'⟩ := ψ
    dsimp at hχ hψ
    subst m
    subst n
    dsimp [f, PrimitiveComplexCharacter.atModulus] at he
    cases he
    rfl
  have : NeZero q := ⟨hq.ne'⟩
  calc
    _ = Fintype.card S := (Fintype.card_coe S).symm
    _ ≤ Fintype.card (DirichletCharacter ℂ q) := Fintype.card_le_of_injective f hf
    _ = q.totient := by
      rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
    _ ≤ q := Nat.totient_le q

theorem primitive_character_family_card (F : Finset PrimitiveComplexCharacter)
    (Q : ℕ) (hF : ∀ χ ∈ F, χ.modulus ≤ Q) : F.card ≤ Q ^ 2 := by
  have hmap : (F : Set PrimitiveComplexCharacter).MapsTo
      PrimitiveComplexCharacter.modulus (Finset.Icc 1 Q) := by
    intro χ hχ
    exact Finset.mem_Icc.mpr ⟨χ.positive, hF χ hχ⟩
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, Q := by
      apply Finset.sum_le_sum
      intro q hq
      exact (primitive_character_fiber_card F q (Finset.mem_Icc.mp hq).1).trans
        (Finset.mem_Icc.mp hq).2
    _ = Q ^ 2 := by simp [Nat.card_Icc, pow_two]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothZeroCountFamily
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The ordinary individual zero count supplies the family count -/

namespace Ostmann

open Finset
open scoped Classical BigOperators

theorem family_zero_count_of_individual {Z : ∀ χ, ComplexZeroEnumeration χ}
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ χ : PrimitiveComplexCharacter, ∀ T : ℝ, 0 ≤ T →
      ((Z χ).count 0 T : ℝ) ≤ C * (T + 1) * Real.log ((χ.modulus : ℝ) * (T + 2)))
    (Q : ℕ) (hQ : 1 ≤ Q) (T : ℝ) (hT : 0 ≤ T)
    (F : Finset PrimitiveComplexCharacter) (hF : ∀ χ ∈ F, χ.modulus ≤ Q) :
    (∑ χ ∈ F, ((Z χ).count 0 T : ℝ)) ≤
      C * (Q : ℝ) ^ 2 * (T + 1) * Real.log ((Q : ℝ) * (T + 2)) := by
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hlog : 0 ≤ Real.log ((Q : ℝ) * (T + 2)) :=
    Real.log_nonneg (by nlinarith)
  have hB : 0 ≤ C * (T + 1) * Real.log ((Q : ℝ) * (T + 2)) := by positivity
  calc
    _ ≤ ∑ χ ∈ F, C * (T + 1) * Real.log ((Q : ℝ) * (T + 2)) := by
      apply sum_le_sum
      intro χ hχ
      apply (hcount χ T hT).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.log_le_log (mul_pos (by exact_mod_cast χ.positive) (by linarith))
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hF χ hχ) (by linarith)
    _ = (F.card : ℝ) * (C * (T + 1) * Real.log ((Q : ℝ) * (T + 2))) := by simp
    _ ≤ (Q : ℝ) ^ 2 * (C * (T + 1) * Real.log ((Q : ℝ) * (T + 2))) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast primitive_character_family_card F Q hF) hB
    _ = _ := by ring

/-- Only the ordinary individual count and the explicit formula are needed.
The family count, Mellin decay and absolute convergence are already proved. -/
noncomputable def smoothExplicitFormula_of_individual {Z : ∀ χ, ComplexZeroEnumeration χ}
    (E C : ℝ) (hE : 0 < E) (hC : 0 < C)
    (hcount : ∀ χ : PrimitiveComplexCharacter, ∀ T : ℝ, 0 ≤ T →
      ((Z χ).count 0 T : ℝ) ≤ C * (T + 1) * Real.log ((χ.modulus : ℝ) * (T + 2)))
    (hformula : ∀ χ : PrimitiveComplexCharacter, ∀ X : ℝ, 2 ≤ X →
      ‖smoothMangoldtMean χ.modulus χ.character X +
        (∑' i, smoothZeroTerm Z χ X i) + smoothTrivialZeroTerm χ‖ ≤
          E / Real.sqrt X * Real.log (2 * (χ.modulus : ℝ))) :
    PublishedSmoothExplicitFormula Z :=
  SmoothExplicitFormulaCore.toPublished {
    errorConstant := E
    errorConstant_pos := hE
    zeroCountConstant := C
    zeroCountConstant_pos := hC
    zero_count := family_zero_count_of_individual C hC.le hcount
    explicit_formula := hformula
  }

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterEnumerationCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Connecting zero enumerations to actual analytic multiplicities

This is a representation condition: an enumeration may list a zero no more
times than its analytic multiplicity. The numerical zero bound itself is
proved in `CharacterFullZeroCount`, not assumed here.
-/

namespace Ostmann

open scoped Classical BigOperators

/-- For multiplicity-respecting enumerations, only the actual explicit formula
remains in this analytic package. The zero count, Mellin decay and absolute
convergence are all derived. -/
noncomputable def smoothExplicitFormula_of_multiplicity {Z : ∀ χ, ComplexZeroEnumeration χ}
    (hZ : ∀ χ, (Z χ).RespectsMultiplicity) (E : ℝ) (hE : 0 < E)
    (hformula : ∀ χ : PrimitiveComplexCharacter, ∀ X : ℝ, 2 ≤ X →
      ‖smoothMangoldtMean χ.modulus χ.character X +
        (∑' i, smoothZeroTerm Z χ X i) + smoothTrivialZeroTerm χ‖ ≤
          E / Real.sqrt X * Real.log (2 * (χ.modulus : ℝ))) :
    PublishedSmoothExplicitFormula Z :=
  smoothExplicitFormula_of_individual E (32 / Real.log (14 / 13)) hE
    (div_pos (by norm_num) (Real.log_pos (by norm_num)))
    (fun χ T hT => (Z χ).count_bound_of_multiplicity (hZ χ) T hT) hformula

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterContourLogGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial logarithmic growth along the contour disks -/

namespace Ostmann

open Complex Metric

theorem character_contour_log_growth (χ : PrimitiveComplexCharacter) :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ, ∃ M : ℝ, 1 ≤ M ∧
      (∀ z ∈ closedBall (characterZeroCenter t) (11 / 4 : ℝ), ‖χ.L z‖ ≤ M) ∧
      Real.log (3 * M) ≤ B * (1 + |t|) := by
  obtain ⟨C, hC, hbound⟩ := character_L_contour_disk_growth
  let D := max C 1
  let Q := 3 * D * (χ.modulus : ℝ) ^ 4
  let B := |Real.log Q| + 20 + 4 * Real.pi
  have hD : 1 ≤ D := le_max_right _ _
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have hq : 1 ≤ (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  have hqpos : 0 < (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro t
  let M := D * (χ.modulus : ℝ) ^ 4 * (9 + |t|) * Real.exp (Real.pi * (|t| + 3))
  have hM : 1 ≤ M := by
    dsimp [M]
    have hpow : 1 ≤ (χ.modulus : ℝ) ^ 4 := one_le_pow₀ hq
    have he : 1 ≤ Real.exp (Real.pi * (|t| + 3)) := Real.one_le_exp (by positivity)
    have hmul : 1 ≤ D * (χ.modulus : ℝ) ^ 4 := one_le_mul_of_one_le_of_one_le hD hpow
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hmul (by linarith [abs_nonneg t])) he
  refine ⟨M, hM, ?_, ?_⟩
  · intro z hz
    apply (hbound χ t z hz).trans
    dsimp [M, D]
    gcongr
    exact le_max_left _ _
  · have hMprod : 3 * M = Q * (9 + |t|) * Real.exp (Real.pi * (|t| + 3)) := by
      dsimp [M, Q]
      ring
    rw [hMprod, Real.log_mul (by positivity) (by positivity),
      Real.log_mul hQ.ne' (by positivity), Real.log_exp]
    have hlog : Real.log (9 + |t|) ≤ 8 + |t| := by
      have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < 9 + |t|)
      linarith
    have hb : 1 + Real.pi ≤ B := by
      dsimp [B]
      nlinarith [Real.pi_pos, abs_nonneg (Real.log Q)]
    have hc : Real.log Q + 8 + 3 * Real.pi ≤ B := by
      dsimp [B]
      nlinarith [le_abs_self (Real.log Q), Real.pi_pos]
    have hh := mul_le_mul_of_nonneg_right hb (abs_nonneg t)
    nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterLogDerivativeGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform polynomial control of L'/L away from the local zero set -/

namespace Ostmann

open Complex Metric
open scoped BigOperators

theorem character_logDeriv_growth (χ : PrimitiveComplexCharacter) :
    ∃ K : ℝ, 0 < K ∧ ∀ (t δ : ℝ), 0 < δ → ∀ s : ℂ,
      ‖s - characterZeroCenter t‖ ≤ 5 / 2 →
      (∀ z ∈ characterContourZeros χ t, δ ≤ ‖s - z‖) →
      ‖logDeriv χ.L s‖ ≤ K * (1 + |t|) * (1 + δ⁻¹) := by
  obtain ⟨B, hB, hBgrowth⟩ := character_contour_log_growth χ
  let D := B / Real.log (22 / 21 : ℝ)
  let E := 1312 * (B + D * Real.log 21 + 1)
  have hl : 0 < Real.log (22 / 21 : ℝ) := Real.log_pos (by norm_num)
  have hD : 0 < D := div_pos hB hl
  have hG : 0 < Real.log 21 := Real.log_pos (by norm_num)
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨E + D, by positivity, ?_⟩
  intro t δ hδ s hs hsep
  obtain ⟨M, hM, hbound, hlog⟩ := hBgrowth t
  let N := ∑ z ∈ characterContourZeros χ t, (analyticOrderNatAt χ.L z : ℝ)
  have hN : N ≤ D * (1 + |t|) := by
    apply (characterContourZeros_mass_bound χ t M hM hbound).trans
    exact (div_le_div_of_nonneg_right hlog hl.le).trans_eq (by dsimp [D]; ring)
  have hh := character_logDeriv_separated_bound χ t M δ hM hδ hbound s hs hsep
  have he : 1312 * (Real.log (3 * M) + N * Real.log 21 + 1) ≤ E * (1 + |t|) := by
    have hn := mul_le_mul_of_nonneg_right hN hG.le
    dsimp [E]
    nlinarith [abs_nonneg t]
  have hn : N / δ ≤ D * (1 + |t|) * δ⁻¹ := by
    simpa only [div_eq_mul_inv] using div_le_div_of_nonneg_right hN hδ.le
  apply hh.trans
  change 1312 * (Real.log (3 * M) + N * Real.log 21 + 1) + N / δ ≤ _
  apply (add_le_add he hn).trans
  have h1 : 0 ≤ E * (1 + |t|) * δ⁻¹ := by positivity
  have h2 : 0 ≤ D * (1 + |t|) := by positivity
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterContourDiskZeros
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Zeros in the enlarged contour disk still lie in the critical strip -/

namespace Ostmann

open Complex Metric

theorem characterContourZeros_critical (χ : PrimitiveComplexCharacter) (t : ℝ)
    (ht : 3 ≤ |t|) (z : ℂ) (hz : z ∈ characterContourZeros χ t) :
    z ∈ complexCharacterZeros χ ∧ |z.im| ≤ |t| + 3 := by
  obtain ⟨hzball, hzero⟩ := (mem_characterContourZeros χ t z).mp hz
  have hn : ‖z - characterZeroCenter t‖ ≤ 21 / 8 := by
    simpa only [mem_closedBall, dist_eq_norm] using hzball
  have hre := (abs_re_le_norm (z - characterZeroCenter t)).trans hn
  have him := (abs_im_le_norm (z - characterZeroCenter t)).trans hn
  simp only [sub_re, sub_im, characterZeroCenter_re, characterZeroCenter_im] at hre him
  have hz0 : z ≠ 0 := by
    intro he
    rw [he] at him
    simp only [zero_im, zero_sub, abs_neg] at him
    linarith
  have hpos : 0 < z.re := by
    by_contra he
    exact χ.L_ne_zero_negative_small z (by linarith [(abs_le.mp hre).1]) (not_lt.mp he) hz0 hzero
  have hlt : z.re < 1 := by
    by_contra he
    exact χ.L_ne_zero_one_le_re z (not_lt.mp he) hzero
  refine ⟨⟨hpos, hlt, hzero⟩, ?_⟩
  calc
    |z.im| = |(z.im - t) + t| := by congr 1; ring
    _ ≤ |z.im - t| + |t| := abs_add_le _ _
    _ ≤ |t| + 3 := by linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothOriginResidue
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identification of the literal even-character residue at zero -/

namespace Ostmann

open Filter
open scoped Topology Classical

theorem smoothContour_origin_residue_value (χ : PrimitiveComplexCharacter)
    (X : ℝ) :
    -(analyticOrderNatAt χ.L 0 : ℂ) * smoothContourWeight X 0 = -smoothTrivialZeroTerm χ := by
  rw [χ.L_multiplicity_at_zero]
  by_cases hχ : χ.character (-1) = 1
  · simp [hχ, smoothContourWeight, smoothTrivialZeroTerm]
  · simp [hχ, smoothTrivialZeroTerm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothContourRegularPart
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing each actual simple logarithmic-derivative pole

After adding back the zero's exact principal part, the smooth contour
integrand agrees locally with an analytic function.
-/

namespace Ostmann

open Filter
open scoped Topology

theorem smoothContour_regular_part (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) (z : ℂ) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R z ∧
      (fun s => (-deriv χ.L s / χ.L s) * smoothContourWeight X s +
        (analyticOrderNatAt χ.L z : ℂ) * smoothContourWeight X z / (s - z)) =ᶠ[𝓝[≠] z] R := by
  obtain ⟨g, hg, hgne, hsplit⟩ := χ.logDeriv_local_split z
  let W := smoothContourWeight X
  have hW : AnalyticAt ℂ W z := (smoothContourWeight_differentiable X hX).analyticAt z
  have hds : AnalyticAt ℂ (dslope W z) z := by
    obtain ⟨p, hp⟩ := hW
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  have hlog : AnalyticAt ℂ (logDeriv g) z := hg.deriv.div hg hgne
  let R : ℂ → ℂ := fun s => -(analyticOrderNatAt χ.L z : ℂ) * dslope W z s - logDeriv g s * W s
  refine ⟨R, (analyticAt_const.mul hds).sub (hlog.mul hW), ?_⟩
  filter_upwards [hsplit, self_mem_nhdsWithin] with s hs hsz
  have hneg : -deriv χ.L s / χ.L s = -logDeriv χ.L s := by
    rw [logDeriv_apply, neg_div]
  rw [hneg, hs]
  dsimp only [R]
  rw [dslope_of_ne W hsz]
  simp only [slope, smul_eq_mul]
  change -((analyticOrderNatAt χ.L z : ℂ) / (s - z) + logDeriv g s) * W s +
    (analyticOrderNatAt χ.L z : ℂ) * W z / (s - z) =
    -(analyticOrderNatAt χ.L z : ℂ) * ((s - z)⁻¹ * (W s - W z)) - logDeriv g s * W s
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothFiniteRegularization
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing finitely many actual character poles simultaneously -/

namespace Ostmann

open Filter Set
open scoped Topology BigOperators Classical

/-- Fill in the removable values after subtracting the principal parts of all
zeros in a prescribed region. The pole set is the actual zero set in that region. -/
theorem smoothContour_finite_regularization (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) (K : Set ℂ) (S : Finset ℂ)
    (hzeros : ∀ z ∈ K, χ.L z = 0 → z ∈ S) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F K ∧
      ∀ z ∉ S, F z = (-deriv χ.L z / χ.L z) * smoothContourWeight X z +
        ∑ w ∈ S, (analyticOrderNatAt χ.L w : ℂ) * smoothContourWeight X w / (z - w) := by
  choose R hR heR using fun z => smoothContour_regular_part χ X hX z
  let f : ℂ → ℂ := fun z => (-deriv χ.L z / χ.L z) * smoothContourWeight X z
  let C : ℂ → ℂ := fun w => (analyticOrderNatAt χ.L w : ℂ) * smoothContourWeight X w
  let F : ℂ → ℂ := fun z => if z ∈ S then
    R z z + ∑ w ∈ S.erase z, C w / (z - w)
    else f z + ∑ w ∈ S, C w / (z - w)
  refine ⟨F, ?_, fun z hz => by simp [F, hz, f, C]⟩
  intro z hzK
  by_cases hz : z ∈ S
  · have hsum : AnalyticAt ℂ (fun s => ∑ w ∈ S.erase z, C w / (s - w)) z := by
      apply (S.erase z).analyticAt_fun_sum
      intro w hw
      exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.mpr (Finset.ne_of_mem_erase hw).symm)
    apply ((hR z).add hsum).congr
    have hav : ∀ᶠ s in 𝓝 z, s ∉ S.erase z :=
      (S.erase z).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
    have he : ∀ᶠ s in 𝓝 z, s ≠ z → f s + C z / (s - z) = R z s := by
      simpa only [mem_compl_iff, mem_singleton_iff, f, C] using
        (eventually_nhdsWithin_iff.mp (heR z))
    filter_upwards [hav, he] with s hs hreg
    by_cases hsz : s = z
    · subst s
      simp [F, hz]
    · have hsS : s ∉ S := fun hsS => hs (Finset.mem_erase.mpr ⟨hsz, hsS⟩)
      simp only [F, ite_eq_right hsS]
      rw [← Finset.sum_erase_add _ _ hz]
      simp only [Pi.add_apply]
      rw [← hreg hsz]
      ring
  · have hnz : χ.L z ≠ 0 := fun he => hz (hzeros z hzK he)
    have hf : AnalyticAt ℂ f z :=
      (((χ.L_analytic z).deriv.neg.div (χ.L_analytic z) hnz).mul
        ((smoothContourWeight_differentiable X hX).analyticAt z))
    have hsum : AnalyticAt ℂ (fun s => ∑ w ∈ S, C w / (s - w)) z := by
      apply S.analyticAt_fun_sum
      intro w hw
      exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.mpr (fun he => hz (he ▸ hw)))
    apply (hf.add hsum).congr
    have hav : ∀ᶠ s in 𝓝 z, s ∉ S := S.finite_toSet.isClosed.isOpen_compl.mem_nhds hz
    filter_upwards [hav] with s hs
    simp [F, hs]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothRectangleResidues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite rectangle identity for the actual smooth character integrand -/

namespace Ostmann

open Complex Set
open scoped Interval BigOperators Classical

/-- The finite contour-shift identity, with the genuine analytic zero orders.
The hypotheses specify only which finite set contains the rectangle's zeros
and that its points are interior; no residue or integral identity is assumed. -/
theorem smoothContour_rectangle_residues (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) (a b c d : ℝ) (S : Finset ℂ)
    (hinside : ∀ z ∈ S, a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d)
    (hzeros : ∀ z ∈ uIcc a b ×ℂ uIcc c d, χ.L z = 0 → z ∈ S) :
    rectangleBoundaryIntegral
      (fun z => (-deriv χ.L z / χ.L z) * smoothContourWeight X z) a b c d =
      -(2 * (Real.pi : ℂ) * I) *
        ∑ z ∈ S, (analyticOrderNatAt χ.L z : ℂ) * smoothContourWeight X z := by
  let f : ℂ → ℂ := fun z => (-deriv χ.L z / χ.L z) * smoothContourWeight X z
  let C : ℂ → ℂ := fun z => (analyticOrderNatAt χ.L z : ℂ) * smoothContourWeight X z
  let g : ℂ → ℂ := fun s => ∑ z ∈ S, C z * (s - z)⁻¹
  obtain ⟨F, hF, heF⟩ := smoothContour_finite_regularization χ X hX
    (uIcc a b ×ℂ uIcc c d) S hzeros
  have hnot (w : ℂ) (hw : w ∈ contourRectangleBoundary a b c d) : w ∉ S := by
    intro hmem
    exact contourBoundary_ne_interior (hinside w hmem) hw rfl
  have hnonzero (w : ℂ) (hw : w ∈ contourRectangleBoundary a b c d) : χ.L w ≠ 0 := by
    intro hzero
    exact hnot w hw (hzeros w ⟨hw.1, hw.2.1⟩ hzero)
  have hf : RectangleIntegrable f a b c d := by
    apply rectangleIntegrable_of_continuousOn
    intro w hw
    exact (((χ.L_analytic w).deriv.neg.div (χ.L_analytic w) (hnonzero w hw)).mul
      ((smoothContourWeight_differentiable X hX).analyticAt w)).continuousAt.continuousWithinAt
  have hterm (z : ℂ) (hz : z ∈ S) :
      RectangleIntegrable (fun s => C z * (s - z)⁻¹) a b c d :=
    (rectangleIntegrable_sub_inv (hinside z hz)).const_mul (C z)
  have hg : RectangleIntegrable g a b c d := RectangleIntegrable.sum S hterm
  have hfg : rectangleBoundaryIntegral F a b c d =
      rectangleBoundaryIntegral (fun z => f z + g z) a b c d := by
    apply rectangleBoundaryIntegral_congr
    intro z hz
    simpa only [f, g, C, div_eq_mul_inv] using heF z (hnot z hz)
  have hgvalue : rectangleBoundaryIntegral g a b c d =
      (2 * (Real.pi : ℂ) * I) * ∑ z ∈ S, C z := by
    rw [show g = (fun s => ∑ z ∈ S, C z * (s - z)⁻¹) from rfl,
      rectangleBoundaryIntegral_sum S hterm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    rw [rectangleBoundaryIntegral_const_mul,
      rectangleBoundaryIntegral_sub_inv z a b c d (hinside z hz).1
        (hinside z hz).2.1 (hinside z hz).2.2.1 (hinside z hz).2.2.2]
    ring
  have hzero := rectangleBoundaryIntegral_eq_zero hF
  rw [hfg, rectangleBoundaryIntegral_add hf hg, hgvalue] at hzero
  change rectangleBoundaryIntegral f a b c d = -(2 * (Real.pi : ℂ) * I) * ∑ z ∈ S, C z
  linear_combination hzero

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothTruncatedContour
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact truncated smooth explicit formula

The contour encloses all actual critical zeros of bounded height and the
origin. Its zero sum is a finite sum with analytic multiplicities.
-/

namespace Ostmann

open Complex Set
open scoped BigOperators Classical Interval

theorem smoothContour_truncated (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) (T : ℝ) (hT : 0 < T)
    (hheight : ∀ z ∈ complexCharacterZeros χ, |z.im| ≠ T) :
    rectangleBoundaryIntegral
      (fun z => (-deriv χ.L z / χ.L z) * smoothContourWeight X z)
      (-(1 / 2)) 2 (-T) T =
      -(2 * (Real.pi : ℂ) * I) *
        ((∑ z ∈ criticalZerosUpTo χ T,
          (analyticOrderNatAt χ.L z : ℂ) * smoothContourWeight X z) + smoothTrivialZeroTerm χ) := by
  let S := insert (0 : ℂ) (criticalZerosUpTo χ T)
  have hinside : ∀ z ∈ S, -(1 / 2 : ℝ) < z.re ∧ z.re < 2 ∧ -T < z.im ∧ z.im < T := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · change -(1 / 2 : ℝ) < 0 ∧ (0 : ℝ) < 2 ∧ -T < 0 ∧ 0 < T
      exact ⟨by norm_num, by norm_num, by linarith, hT⟩
    · obtain ⟨hz, hi⟩ := mem_criticalZerosUpTo.mp hz
      have hi' := lt_of_le_of_ne hi (hheight z hz)
      have hab := abs_lt.mp hi'
      exact ⟨by linarith [hz.1], by linarith [hz.2.1], hab.1, hab.2⟩
  have hzeros : ∀ z ∈ uIcc (-(1 / 2 : ℝ)) 2 ×ℂ uIcc (-T) T, χ.L z = 0 → z ∈ S := by
    intro z hz hzero
    have hr : -(1 / 2 : ℝ) ≤ z.re := (show z.re ∈ Icc (-(1 / 2 : ℝ)) 2 by
      simpa only [uIcc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 2), mem_preimage] using hz.1).1
    rcases χ.contour_zero_location z hr hzero with rfl | hcrit
    · exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      apply mem_criticalZerosUpTo.mpr
      refine ⟨hcrit, abs_le.mpr ?_⟩
      simpa only [uIcc_of_le (by linarith : -T ≤ T), mem_preimage, mem_Icc] using hz.2
  have hzero : (0 : ℂ) ∉ criticalZerosUpTo χ T := by
    simp [complexCharacterZeros]
  have hmain := smoothContour_rectangle_residues χ X hX (-(1 / 2)) 2 (-T) T S hinside hzeros
  have horigin : (analyticOrderNatAt χ.L 0 : ℂ) * smoothContourWeight X 0 = smoothTrivialZeroTerm χ := by
    have hh := smoothContour_origin_residue_value χ X
    linear_combination -hh
  simpa only [S, Finset.sum_insert hzero, horigin, add_comm] using hmain

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterSeparatedHeights
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Paired contour heights with polynomially controlled separation from zeros -/

namespace Ostmann

open Complex Set
open scoped BigOperators Classical

theorem exists_character_separated_height (χ : PrimitiveComplexCharacter) :
    ∃ D : ℝ, 0 < D ∧ ∀ T : ℝ, 3 ≤ T → ∃ t δ : ℝ,
      T < t ∧ t < T + 1 ∧ 0 < δ ∧ δ⁻¹ ≤ D * (T + 5) ^ 2 ∧
      (∀ z ∈ complexCharacterZeros χ, |z.im| ≠ t) ∧
      ∀ y : ℝ, y = t ∨ y = -t →
        ∀ z ∈ characterContourZeros χ y, δ ≤ |y - z.im| := by
  obtain ⟨C, hC, hcount⟩ := criticalZerosUpTo_card_polynomial χ
  refine ⟨4 * (C + 1), by positivity, ?_⟩
  intro T hT
  let S := (criticalZerosUpTo χ (T + 4)).image (fun z : ℂ => |z.im|)
  let δ := (4 * ((S.card : ℝ) + 1))⁻¹
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsize : 2 * δ * (S.card : ℝ) < 1 := by
    dsimp [δ]
    have hr : (2 * (S.card : ℝ)) / (4 * ((S.card : ℝ) + 1)) < 1 := by
      apply (div_lt_iff₀ (by positivity)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) S.card]
    convert hr using 1 <;> first | rfl | ring
  obtain ⟨t, ht, hsep⟩ := exists_height_separated S T δ hδ hsize
  have htpos : 0 < t := by linarith [ht.1]
  have hcard : (S.card : ℝ) ≤ C * (T + 5) ^ 2 := by
    apply le_trans (show (S.card : ℝ) ≤ ((criticalZerosUpTo χ (T + 4)).card : ℝ) from
      by exact_mod_cast Finset.card_image_le)
    exact hcount T (by linarith)
  have hδbound : δ⁻¹ ≤ 4 * (C + 1) * (T + 5) ^ 2 := by
    dsimp [δ]
    rw [inv_inv]
    have hsq : 1 ≤ (T + 5) ^ 2 := by nlinarith
    nlinarith
  refine ⟨t, δ, ht.1, ht.2, hδ, hδbound, ?_, ?_⟩
  · intro z hz he
    have hzS : |z.im| ∈ S := Finset.mem_image.mpr
      ⟨z, mem_criticalZerosUpTo.mpr ⟨hz, by rw [he]; linarith [ht.2]⟩, rfl⟩
    have hh := hsep _ hzS
    rw [he, sub_self, abs_zero] at hh
    linarith
  · intro y hy z hz
    have hyabs : |y| = t := by rcases hy with rfl | rfl <;> simp [abs_of_pos htpos]
    obtain ⟨hzcrit, hzim⟩ := characterContourZeros_critical χ y (by rw [hyabs]; linarith [ht.1]) z hz
    have hzS : |z.im| ∈ S := Finset.mem_image.mpr
      ⟨z, mem_criticalZerosUpTo.mpr ⟨hzcrit, by rw [hyabs] at hzim; linarith [ht.2]⟩, rfl⟩
    have hh := hsep _ hzS
    have hab := abs_abs_sub_abs_le_abs_sub y z.im
    rw [hyabs] at hab
    exact hh.trans hab

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterHorizontalGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial logarithmic-derivative bounds along both horizontal edges -/

namespace Ostmann

open Complex Metric Set

/-- One height controls both horizontal edges of the actual rectangular contour. -/
theorem exists_character_horizontal_bound (χ : PrimitiveComplexCharacter) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℝ, 3 ≤ T → ∃ t : ℝ,
      T < t ∧ t < T + 1 ∧ (∀ z ∈ complexCharacterZeros χ, |z.im| ≠ t) ∧
      ∀ y : ℝ, y = t ∨ y = -t → ∀ σ ∈ Icc (-(1 / 2 : ℝ)) 2,
        ‖logDeriv χ.L ((σ : ℂ) + (y : ℂ) * I)‖ ≤ K * (T + 5) ^ 3 := by
  obtain ⟨K, hK, hgrowth⟩ := character_logDeriv_growth χ
  obtain ⟨D, hD, hheight⟩ := exists_character_separated_height χ
  refine ⟨K * (D + 1), by positivity, ?_⟩
  intro T hT
  obtain ⟨t, δ, ht, ht', hδ, hδbound, hzero, hsep⟩ := hheight T hT
  refine ⟨t, ht, ht', hzero, ?_⟩
  intro y hy σ hσ
  have htpos : 0 < t := by linarith
  have hyabs : |y| = t := by rcases hy with rfl | rfl <;> simp [abs_of_pos htpos]
  let s : ℂ := (σ : ℂ) + (y : ℂ) * I
  have hs : ‖s - characterZeroCenter y‖ ≤ 5 / 2 := by
    have he : s - characterZeroCenter y = ((σ - 2 : ℝ) : ℂ) := by
      dsimp [s, characterZeroCenter]
      push_cast
      ring
    rw [he, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have hsd : ∀ z ∈ characterContourZeros χ y, δ ≤ ‖s - z‖ := by
    intro z hz
    apply (hsep y hy z hz).trans
    have hh := abs_im_le_norm (s - z)
    simpa [s] using hh
  have hh := hgrowth y δ hδ s hs hsd
  rw [hyabs] at hh
  have hp : 1 + δ⁻¹ ≤ (D + 1) * (T + 5) ^ 2 := by
    have hsq : 1 ≤ (T + 5) ^ 2 := by nlinarith
    nlinarith
  calc
    _ ≤ K * (1 + t) * (1 + δ⁻¹) := hh
    _ ≤ K * (T + 5) * ((D + 1) * (T + 5) ^ 2) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (by linarith) hK.le
      · exact hp
      · positivity
      · positivity
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterLogDerivativeLeft
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The logarithmic derivative on the left side of the explicit-formula contour -/

namespace Ostmann

open Complex

/-- A uniform polynomial bound, derived from the functional equation and the
absolutely convergent right-hand line. -/
theorem character_logDeriv_left_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ), s.re = -(1 / 2 : ℝ) →
      ‖logDeriv χ.L s‖ ≤ C * (1 + Real.log (χ.modulus : ℝ) + |s.im|) := by
  obtain ⟨A, hA, hright⟩ := character_logDeriv_right_bound
  obtain ⟨B, hB, hgamma⟩ := characterGammaInverse_contour_bound
  refine ⟨1 + A + 2 * B, by positivity, ?_⟩
  intro χ s hs
  have hr : (1 - s).re = (3 / 2 : ℝ) := by simp; linarith
  have hne : s ≠ 0 := by intro he; subst s; norm_num at hs
  have hL := χ.logDeriv_L_eq_completed_add s
    (χ.L_ne_zero_left_ne_origin s hs.ge (by linarith) hne)
  have hLi := χ.inverse.logDeriv_L_eq_completed_add (1 - s)
    (χ.inverse.L_ne_zero_one_le_re _ (by rw [hr]; norm_num))
  have hCi : logDeriv χ.inverse.completed (1 - s) =
      logDeriv χ.inverse.L (1 - s) - logDeriv χ.inverse.gammaInverse (1 - s) := by
    linear_combination -hLi
  have hR := χ.completed_logDeriv_reflection (1 - s) (by rw [hr]; norm_num)
  have hcomp : 1 - (1 - s) = s := by ring
  rw [hcomp] at hR
  rw [hL, hR, hCi]
  have hq : 1 ≤ (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  have hlogq : 0 ≤ Real.log (χ.modulus : ℝ) := Real.log_nonneg hq
  have hnlog : ‖Complex.log (χ.modulus : ℂ)‖ = Real.log (χ.modulus : ℝ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (by positivity), norm_real,
      Real.norm_eq_abs, abs_of_nonneg hlogq]
  have hri := hright χ.inverse (1 - s) hr
  have hgi := hgamma χ.inverse (1 - s) (.inr hr)
  have hgc := hgamma χ s (.inl hs)
  simp only [sub_im, one_im, zero_sub, abs_neg] at hgi
  calc
    _ ≤ ‖-Complex.log (χ.modulus : ℂ)‖ +
        ‖logDeriv χ.inverse.L (1 - s) - logDeriv χ.inverse.gammaInverse (1 - s)‖ +
          ‖logDeriv χ.gammaInverse s‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) (le_refl _))
    _ ≤ Real.log (χ.modulus : ℝ) + (A + B * (1 + |s.im|)) + B * (1 + |s.im|) := by
      rw [norm_neg, hnlog]
      exact add_le_add (add_le_add (le_refl _) ((norm_sub_le _ _).trans (add_le_add hri hgi))) hgc
    _ ≤ _ := by
      nlinarith [abs_nonneg s.im, mul_nonneg hA.le hlogq,
        mul_nonneg hA.le (abs_nonneg s.im), mul_nonneg hB.le hlogq]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothLeftContourWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An integrable majorant for the left vertical contour -/

namespace Ostmann

open Complex MeasureTheory Filter
open scoped Topology

theorem leftContourIntegrand_continuous (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) : Continuous (leftContourIntegrand χ X) := by
  have hcL : Continuous χ.L := continuous_iff_continuousAt.mpr (fun z => (χ.L_analytic z).continuousAt)
  have hcd : Continuous (deriv χ.L) := continuous_iff_continuousAt.mpr (fun z => (χ.L_analytic z).deriv.continuousAt)
  have hn (t : ℝ) : χ.L (leftContourLine t) ≠ 0 := by
    apply χ.L_ne_zero_left_ne_origin _ (by simp) (by simp)
    intro he
    have hh := congrArg Complex.re he
    norm_num at hh
  exact ((hcd.comp leftContourLine_continuous).neg.div (hcL.comp leftContourLine_continuous) hn).mul
    ((smoothContourWeight_differentiable X hX).continuous.comp leftContourLine_continuous)

theorem leftContourIntegrand_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (X : ℝ), 0 < X → ∀ t : ℝ,
      ‖leftContourIntegrand χ X t‖ ≤
        (C * (1 + Real.log (χ.modulus : ℝ)) / Real.sqrt X) * leftContourMajorant t := by
  obtain ⟨A, hA, hbound⟩ := character_logDeriv_left_bound
  obtain ⟨M, hM, hmellin⟩ := primeMeanMellin_decay
  refine ⟨A * M, mul_pos hA hM, ?_⟩
  intro χ X hX t
  have hq : 0 ≤ Real.log (χ.modulus : ℝ) := Real.log_nonneg (by exact_mod_cast χ.positive)
  have hl := hbound χ (leftContourLine t) (by simp)
  have hm := hmellin (leftContourLine t) (by norm_num) (by norm_num)
  simp only [leftContourLine_im] at hl hm
  have hscalar : 1 + Real.log (χ.modulus : ℝ) + |t| ≤
      (1 + Real.log (χ.modulus : ℝ)) * (1 + |t|) := by nlinarith [abs_nonneg t]
  have hexp : (1 + |t|) * Real.exp (-8 * Real.log (1 + |t|)) = leftContourMajorant t := by
    rw [leftContourMajorant, Real.rpow_def_of_pos (by positivity)]
    conv_lhs => arg 1; rw [← Real.exp_log (by positivity : 0 < 1 + |t|)]
    rw [← Real.exp_add]
    congr 1
    ring
  have hnorm : ‖leftContourIntegrand χ X t‖ =
      ‖logDeriv χ.L (leftContourLine t)‖ *
        (‖primeMeanMellin (leftContourLine t)‖ / Real.sqrt X) := by
    rw [leftContourIntegrand, norm_mul, leftContourWeight_norm X t hX]
    simp [logDeriv_apply, neg_div]
  rw [hnorm]
  calc
    _ ≤ (A * ((1 + Real.log (χ.modulus : ℝ)) * (1 + |t|))) *
        (M * Real.exp (-8 * Real.log (1 + |t|)) / Real.sqrt X) := by
      gcongr
      exact hl.trans (mul_le_mul_of_nonneg_left hscalar hA.le)
    _ = (A * M * (1 + Real.log (χ.modulus : ℝ)) / Real.sqrt X) * leftContourMajorant t := by
      rw [← hexp]
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothLeftContourBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The uniform error from the left vertical contour -/

namespace Ostmann

open Complex MeasureTheory Filter

theorem leftContourIntegrand_integrable (χ : PrimitiveComplexCharacter) (X : ℝ) (hX : 0 < X) :
    Integrable (leftContourIntegrand χ X) := by
  obtain ⟨C, hC, hbound⟩ := leftContourIntegrand_bound
  have hm := leftContourMajorant_integrable.const_mul
    (C * (1 + Real.log (χ.modulus : ℝ)) / Real.sqrt X)
  apply hm.mono' (leftContourIntegrand_continuous χ X hX).aestronglyMeasurable
  exact Eventually.of_forall (hbound χ X hX)

theorem leftContour_integral_bound : ∃ E : ℝ, 0 < E ∧
    ∀ (χ : PrimitiveComplexCharacter) (X : ℝ), 0 < X →
      ‖∫ t : ℝ, leftContourIntegrand χ X t‖ ≤
        E / Real.sqrt X * Real.log (2 * (χ.modulus : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := leftContourIntegrand_bound
  let R : ℝ := |∫ t : ℝ, leftContourMajorant t| + 1
  let A : ℝ := 1 + 1 / Real.log 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hA : 0 < A := by dsimp [A]; have hh : 0 < Real.log 2 := Real.log_pos (by norm_num); positivity
  refine ⟨C * R * A, by positivity, ?_⟩
  intro χ X hX
  have hq : 1 ≤ (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  have hlogq : 0 ≤ Real.log (χ.modulus : ℝ) := Real.log_nonneg hq
  let D := C * (1 + Real.log (χ.modulus : ℝ)) / Real.sqrt X
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hi := leftContourIntegrand_integrable χ X hX
  calc
    _ ≤ ∫ t : ℝ, ‖leftContourIntegrand χ X t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, D * leftContourMajorant t :=
      integral_mono_ae hi.norm (leftContourMajorant_integrable.const_mul D)
        (Eventually.of_forall (hbound χ X hX))
    _ = D * ∫ t : ℝ, leftContourMajorant t := integral_const_mul _ _
    _ ≤ D * R := mul_le_mul_of_nonneg_left (by dsimp [R]; linarith [le_abs_self (∫ t : ℝ, leftContourMajorant t)]) hD
    _ = (C * R / Real.sqrt X) * (1 + Real.log (χ.modulus : ℝ)) := by dsimp [D]; ring
    _ ≤ (C * R / Real.sqrt X) * (A * Real.log (2 * (χ.modulus : ℝ))) :=
      mul_le_mul_of_nonneg_left (one_add_log_le_log_twice _ hq) (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ActualRealZeroExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual real-character Hadamard expansion -/

namespace Ostmann

open Complex

noncomputable def actualPublishedRealZeroInput (P : PublishedProgressionInput)
    (hregion : ActualRealLowHeightRegion P) : PublishedRealZeroInput P where
  errorConstant := actualRealZeroErrorConstant
  errorConstant_nonneg := actualRealZeroErrorConstant_pos.le
  expansion := actualRealCharacterZeroExpansion
  region := hregion

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterRieszZeroSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unique actual zero contribution selected by a Riesz rectangle -/

namespace Ostmann

open Complex Set
open scoped Interval

theorem character_riesz_zero_selection (χ : PrimitiveComplexCharacter) (a T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hT : 0 < T)
    (hleft : ∀ s : ℂ, s.re = a → |s.im| ≤ T → χ.L s ≠ 0)
    (hreal : ∀ i : ℕ, a ≤ ((actualCharacterZeros χ).zeros i).re →
      |((actualCharacterZeros χ).zeros i).im| ≤ T →
      χ.character ^ 2 = 1 ∧ ((actualCharacterZeros χ).zeros i).im = 0 ∧
        analyticOrderNatAt χ.L ((actualCharacterZeros χ).zeros i) = 1)
    (hunique : ∀ i j : ℕ, a ≤ ((actualCharacterZeros χ).zeros i).re →
      a ≤ ((actualCharacterZeros χ).zeros j).re →
      |((actualCharacterZeros χ).zeros i).im| ≤ T →
      |((actualCharacterZeros χ).zeros j).im| ≤ T → i = j) :
    ∃ e : Option ℕ,
      (∀ i : ℕ, e = some i → a < ((actualCharacterZeros χ).zeros i).re ∧
        χ.character ^ 2 = 1 ∧ ((actualCharacterZeros χ).zeros i).im = 0) ∧
      (∀ i : ℕ, a ≤ ((actualCharacterZeros χ).zeros i).re →
        |((actualCharacterZeros χ).zeros i).im| ≤ T → e = some i) ∧
      ∀ X b : ℝ, 0 < X → 1 < b →
        rectangleBoundaryIntegral (fun s => -logDeriv χ.L s * rieszContourWeight X s)
          a b (-T) T = I * (((2 * Real.pi : ℝ) : ℂ) * characterRieszZeroTerm χ X e) := by
  classical
  let Z := actualCharacterZeros χ
  by_cases hex : ∃ i : ℕ, a ≤ (Z.zeros i).re ∧ |(Z.zeros i).im| ≤ T
  · obtain ⟨i, hi, hit⟩ := hex
    obtain ⟨hsq, him, hm⟩ := hreal i hi hit
    change (Z.zeros i).im = 0 at him
    have hai : a < (Z.zeros i).re := by
      apply lt_of_le_of_ne hi
      intro he
      exact hleft (Z.zeros i) he.symm hit (Z.actual_zero i)
    refine ⟨some i, ?_, ?_, ?_⟩
    · intro j hj
      cases Option.some.inj hj
      exact ⟨hai, hsq, him⟩
    · intro j hj hjt
      rw [hunique j i hj hi hjt hit]
    · intro X b hX hb
      have hzeros (s : ℂ) (hs : s ∈ uIcc a b ×ℂ uIcc (-T) T) (hz : χ.L s = 0) :
          s = Z.zeros i := by
        have hab : a ≤ b := ha1.le.trans hb.le
        have hsr : a ≤ s.re := ((uIcc_of_le hab) ▸ hs.1).1
        have hst : |s.im| ≤ T := by
          apply abs_le.mpr
          simpa only [uIcc_of_le (by linarith : -T ≤ T), mem_preimage, mem_Icc] using hs.2
        obtain ⟨j, hj⟩ := character_zero_enumerated_of_re_pos χ s (ha.trans_le hsr) hz
        have hji := hunique j i (by simpa only [hj] using hsr) hi
          (by simpa only [hj] using hst) hit
        change Z.zeros j = s at hj
        simpa only [hji] using hj.symm
      have hr := rieszContour_single_zero_rectangle χ X hX a b (-T) T (Z.zeros i)
        ha hai ((Z.in_strip i).2.trans hb) (by simpa only [him] using neg_neg_of_pos hT)
        (by simpa only [him] using hT) hzeros
      rw [hm] at hr
      simp only [Nat.cast_one, one_mul] at hr
      rw [hr]
      simp only [characterRieszZeroTerm]
      push_cast
      ring
  · refine ⟨none, by simp, ?_, ?_⟩
    · intro i hi hit
      exact (hex ⟨i, hi, hit⟩).elim
    · intro X b hX hb
      have hab : a ≤ b := ha1.le.trans hb.le
      have hzero := rieszContour_rectangle_zero χ X hX a b (-T) T ha hab
      have hn (s : ℂ) (hs : s ∈ uIcc a b ×ℂ uIcc (-T) T) : χ.L s ≠ 0 := by
        intro hz
        have hsr : a ≤ s.re := ((uIcc_of_le hab) ▸ hs.1).1
        have hst : |s.im| ≤ T := by
          apply abs_le.mpr
          simpa only [uIcc_of_le (by linarith : -T ≤ T), mem_preimage, mem_Icc] using hs.2
        obtain ⟨i, hi⟩ := character_zero_enumerated_of_re_pos χ s (ha.trans_le hsr) hz
        change Z.zeros i = s at hi
        exact hex ⟨i, by simpa only [hi] using hsr, by simpa only [hi] using hst⟩
      rw [hzero hn]
      simp [characterRieszZeroTerm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterRieszLocalBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform Riesz estimate with its actual possible real-zero term -/

namespace Ostmann

open Complex

theorem character_riesz_local_bound : ∃ c A B E : ℝ,
    0 < c ∧ c ≤ 1 / 4 ∧ c ≤ actualPageConstant / 10 ∧ 0 < A ∧ 0 < B ∧ 0 < E ∧
    ∀ (χ : PrimitiveComplexCharacter) (T : ℝ), 2 ≤ T →
      let H := Real.log χ.modulus + Real.log (T + 4) + 1
      ∃ e : Option ℕ,
        (∀ i, e = some i → 1 - 2 * c / H < ((actualCharacterZeros χ).zeros i).re ∧
          χ.character ^ 2 = 1 ∧ ((actualCharacterZeros χ).zeros i).im = 0) ∧
        (∀ i, 1 - c / H ≤ ((actualCharacterZeros χ).zeros i).re →
          |((actualCharacterZeros χ).zeros i).im| ≤ T → e = some i) ∧
        ∀ X b : ℝ, 1 ≤ X → 1 < b → b ≤ 2 →
          ‖characterRieszMean χ X - characterRieszZeroTerm χ X e‖ ≤
            A * H ^ 2 * X ^ (1 - c / H) + B * H ^ 2 * X ^ b / T ^ 2 +
              2 * (1 / (b - 1) + E) * X ^ b / T := by
  obtain ⟨c, C, hc, hc4, hcp, hC, hdata⟩ := character_riesz_boundary_data
  obtain ⟨K, E, hK, hE, hrect⟩ := characterRieszMean_residue_rectangle_bound
  refine ⟨c, K * C, 4 * C, E, hc, hc4, hcp, by positivity, by positivity, hE, ?_⟩
  intro χ T hT
  dsimp only
  let H := Real.log χ.modulus + Real.log (T + 4) + 1
  have hq : 0 ≤ Real.log χ.modulus := Real.log_nonneg (by exact_mod_cast χ.positive)
  have htlog : 0 ≤ Real.log (T + 4) := Real.log_nonneg (by linarith)
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hHp : 0 < H := by linarith
  have hδ : 0 < c / H := div_pos hc hHp
  have hδ4 : c / H ≤ 1 / 4 := calc
    c / H ≤ c / 1 := div_le_div_of_nonneg_left hc.le (by norm_num) hH
    _ ≤ 1 / 4 := by simpa using hc4
  obtain ⟨hr, hu, a, ha, ha', hedge⟩ := hdata χ T hT
  change 1 - 2 * c / H ≤ a at ha
  change a ≤ 1 - c / H at ha'
  have ha0 : 1 / 2 ≤ a := by rw [mul_div_assoc] at ha; linarith
  have ha1 : a < 1 := by linarith
  have hreal (i : ℕ) (hi : a ≤ ((actualCharacterZeros χ).zeros i).re)
      (hit : |((actualCharacterZeros χ).zeros i).im| ≤ T) :
      χ.character ^ 2 = 1 ∧ ((actualCharacterZeros χ).zeros i).im = 0 ∧
        analyticOrderNatAt χ.L ((actualCharacterZeros χ).zeros i) = 1 := by
    apply hr i (by linarith)
    change 1 - 4 * c / H ≤ _
    have hh : 0 ≤ c / H := hδ.le
    rw [mul_div_assoc] at ha ⊢
    linarith
  have huniq (i j : ℕ) (hi : a ≤ ((actualCharacterZeros χ).zeros i).re)
      (hj : a ≤ ((actualCharacterZeros χ).zeros j).re)
      (hit : |((actualCharacterZeros χ).zeros i).im| ≤ T)
      (hjt : |((actualCharacterZeros χ).zeros j).im| ≤ T) : i = j := by
    apply hu i j (by linarith) (by linarith)
    · change 1 - 4 * c / H ≤ _
      rw [mul_div_assoc] at ha ⊢
      linarith
    · change 1 - 4 * c / H ≤ _
      rw [mul_div_assoc] at ha ⊢
      linarith
  obtain ⟨e, he, hecomplete, heres⟩ := character_riesz_zero_selection χ a T
    (by linarith) ha1 (by linarith) (fun s hs ht => (hedge s (.inl ⟨hs, ht⟩)).1)
    hreal huniq
  refine ⟨e, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨hai, hsq, him⟩ := he i hi
    exact ⟨ha.trans_lt hai, hsq, him⟩
  · intro i hi hit
    exact hecomplete i (ha'.trans hi) hit
  · intro X b hX hb hb2
    have hab : a ≤ b := ha1.le.trans hb.le
    have hbound (s : ℂ) (hs : (s.re = a ∧ |s.im| ≤ T) ∨
        (a ≤ s.re ∧ s.re ≤ b ∧ |s.im| = T)) : ‖logDeriv χ.L s‖ ≤ C * H ^ 2 := by
      apply (hedge s _).2
      rcases hs with hs | hs
      · exact .inl hs
      · exact .inr ⟨hs.1, hs.2.1.trans hb2, hs.2.2⟩
    have hh := hrect χ X a b T (C * H ^ 2) (characterRieszZeroTerm χ X e)
      hX ha0 hab hb hb2 (by linarith) (by positivity)
      (heres X b (by linarith) hb) hbound
    have hx : X ^ a ≤ X ^ (1 - c / H) := Real.rpow_le_rpow_of_exponent_le hX ha'
    have hfirst := mul_le_mul_of_nonneg_left hx (show 0 ≤ K * (C * H ^ 2) by positivity)
    have hlen : b - a ≤ 2 := by linarith
    have hsecond := mul_le_mul_of_nonneg_left hlen
      (show 0 ≤ 2 * (C * H ^ 2 * X ^ b / T ^ 2) by positivity)
    calc
      _ ≤ K * (C * H ^ 2) * X ^ a +
          2 * (C * H ^ 2 * X ^ b / T ^ 2) * (b - a) +
          2 * (1 / (b - 1) + E) * X ^ b / T := hh
      _ ≤ K * (C * H ^ 2) * X ^ (1 - c / H) +
          2 * (C * H ^ 2 * X ^ b / T ^ 2) * 2 +
          2 * (1 / (b - 1) + E) * X ^ b / T := by linarith
      _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterPageComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Comparing the selected actual Riesz zero with the canonical Page zero -/

namespace Ostmann

open Complex

theorem local_page_fraction (χ : PrimitiveComplexCharacter) (q : ℕ) (T c : ℝ)
    (hq : 1 ≤ q) (hqT : (q : ℝ) ≤ T) (hT : 2 ≤ T)
    (hc : 0 < c) (hcp : c ≤ actualPageConstant / 10) :
    2 * c / (Real.log χ.modulus + Real.log (T + 4) + 1) ≤
      actualPageConstant / Real.log (4 * (q : ℝ)) := by
  let H := Real.log χ.modulus + Real.log (T + 4) + 1
  let L := Real.log (4 * (q : ℝ))
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqp : (0 : ℝ) < q := by linarith
  have hlogq : 0 ≤ Real.log χ.modulus := Real.log_nonneg (by exact_mod_cast χ.positive)
  have hlogT : 0 ≤ Real.log (T + 4) := Real.log_nonneg (by linarith)
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hHp : 0 < H := by linarith
  have hLp : 0 < L := Real.log_pos (by linarith)
  have hlog : Real.log (q : ℝ) ≤ Real.log (T + 4) := Real.log_le_log hqp (by linarith)
  have hL : L ≤ 4 * H := by
    have he : L = Real.log 4 + Real.log (q : ℝ) := by
      dsimp [L]
      rw [Real.log_mul (by norm_num) hqp.ne']
    rw [he]
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    dsimp [H] at hH ⊢
    linarith
  change 2 * c / H ≤ actualPageConstant / L
  apply (div_le_div_iff₀ hHp hLp).mpr
  have hm := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ 2 * c)
  have hc8 : 8 * c ≤ actualPageConstant := by linarith [actualPageConstant_pos]
  have hh := mul_le_mul_of_nonneg_right hc8 hHp.le
  nlinarith

theorem selected_riesz_zero_canonical (χ : PrimitiveComplexCharacter) (q i : ℕ)
    (T c : ℝ) (hq : 1 ≤ q) (hdvd : χ.modulus ∣ q) (hqT : (q : ℝ) ≤ T)
    (hT : 2 ≤ T) (hc : 0 < c) (hcp : c ≤ actualPageConstant / 10)
    (hsq : χ.character ^ 2 = 1) (him : ((actualCharacterZeros χ).zeros i).im = 0)
    (hbeta : 1 - 2 * c / (Real.log χ.modulus + Real.log (T + 4) + 1) <
      ((actualCharacterZeros χ).zeros i).re) :
    actualLocalZero q = some (indexedRealZero χ i hsq him) := by
  apply indexedRealZero_canonical χ i hsq him q hq hdvd
  have hh := local_page_fraction χ q T c hq hqT hT hc hcp
  linarith

theorem selected_riesz_term_eq_canonical (χ : PrimitiveComplexCharacter) (q i : ℕ)
    (T c X : ℝ) (hq : 1 ≤ q) (hdvd : χ.modulus ∣ q) (hqT : (q : ℝ) ≤ T)
    (hT : 2 ≤ T) (hc : 0 < c) (hcp : c ≤ actualPageConstant / 10)
    (hsq : χ.character ^ 2 = 1) (him : ((actualCharacterZeros χ).zeros i).im = 0)
    (hbeta : 1 - 2 * c / (Real.log χ.modulus + Real.log (T + 4) + 1) <
      ((actualCharacterZeros χ).zeros i).re) :
    characterRieszZeroTerm χ X (some i) = canonicalCharacterRieszTerm χ q X := by
  have he := selected_riesz_zero_canonical χ q i T c hq hdvd hqT hT hc hcp hsq him hbeta
  have hz : (((actualCharacterZeros χ).zeros i).re : ℂ) = (actualCharacterZeros χ).zeros i := by
    apply Complex.ext <;> simp [him]
  simp only [canonicalCharacterRieszTerm, he, indexedRealZero_character, ↓reduceIte,
    indexedRealZero_beta, hz, characterRieszZeroTerm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothActualZeroSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Convergence of the actual contour zero sum -/

namespace Ostmann

open Filter Finset
open scoped Topology BigOperators Classical

theorem smoothZeroTerm_summable_of_multiplicity {Z : ∀ χ, ComplexZeroEnumeration χ}
    (χ : PrimitiveComplexCharacter) (hZ : (Z χ).RespectsMultiplicity)
    (X : ℝ) (hX : 2 ≤ X) : Summable (fun i => ‖smoothZeroTerm Z χ X i‖) := by
  obtain ⟨C, hC, hM⟩ := primeMeanMellin_decay
  let D : ℝ := 32 / Real.log (14 / 13)
  have hD : 0 ≤ D := le_of_lt (div_pos (by norm_num) (Real.log_pos (by norm_num)))
  have hq : (1 : ℝ) ≤ χ.modulus := by exact_mod_cast χ.positive
  have hcount (S : Finset ℕ) (T : ℝ) (hT : 0 ≤ T) :
      ((S.filter (fun i => |((Z χ).zeros i).im| ≤ T)).card : ℝ) ≤
        D * (T + 1) * Real.log ((χ.modulus : ℝ) * (T + 2)) := by
    have hsub : (S.filter fun i => |((Z χ).zeros i).im| ≤ T) ⊆ (Z χ).heightIndices T := by
      intro i hi
      exact ((Z χ).mem_heightIndices T i).mpr (mem_filter.mp hi).2
    calc
      _ ≤ ((Z χ).count 0 T : ℝ) := by
        rw [(Z χ).count_zero_eq_card]
        exact_mod_cast card_le_card hsub
      _ ≤ _ := (Z χ).count_bound_of_multiplicity hZ T hT
  apply summable_of_sum_le (fun i => norm_nonneg _)
    (c := (X * C) * (2 * (2 * D * (Real.log χ.modulus + 3)) ^ 2))
  intro S
  have hh := finite_high_zero_tail_bound S (fun i => |((Z χ).zeros i).im|)
    (χ.modulus : ℝ) D 0 hq hD le_rfl (fun _ _ => abs_nonneg _) (hcount S)
  simp only [add_zero, Real.log_one, mul_zero, Real.exp_zero, mul_one] at hh
  calc
    _ ≤ ∑ i ∈ S, (X * C) * Real.exp (-8 * Real.log (1 + |((Z χ).zeros i).im|)) :=
      sum_le_sum (fun i _ => smoothZeroTerm_bound_of_mellin C hM χ X (by linarith) i)
    _ = (X * C) * ∑ i ∈ S, Real.exp (-8 * Real.log (1 + |((Z χ).zeros i).im|)) :=
      (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (by positivity)

theorem smoothContourWeight_eq_zeroTerm (Z : ∀ χ, ComplexZeroEnumeration χ)
    (χ : PrimitiveComplexCharacter) (X : ℝ) (hX : 0 < X) (i : ℕ) :
    smoothContourWeight X ((Z χ).zeros i) = smoothZeroTerm Z χ X i := by
  rw [smoothContourWeight, smoothZeroTerm, Complex.cpow_def_of_ne_zero (by exact_mod_cast hX.ne')]
  rw [← Complex.ofReal_log hX.le]
  congr 2
  ring

theorem smoothActualZeroSum_tendsto (e : ∀ χ, ℕ ≃ CharacterZeroCopy χ)
    (χ : PrimitiveComplexCharacter) (X : ℝ) (hX : 2 ≤ X) :
    Tendsto (fun T : ℝ => ∑ z ∈ criticalZerosUpTo χ T,
      (analyticOrderNatAt χ.L z : ℂ) * smoothContourWeight X z) atTop
      (𝓝 (∑' i, smoothZeroTerm (fun ψ => characterZeroEnumeration ψ (e ψ)) χ X i)) := by
  let Z := fun ψ => characterZeroEnumeration ψ (e ψ)
  have hs := (smoothZeroTerm_summable_of_multiplicity (Z := Z) χ
    (characterZeroEnumeration_respectsMultiplicity χ (e χ)) X hX).of_norm
  have ht := (Z χ).tendsto_height_sum (fun i => smoothZeroTerm Z χ X i) hs
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext T
  rw [characterZeroEnumeration_height_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact smoothContourWeight_eq_zeroTerm Z χ X (by linarith) i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothHorizontalBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fifth-order decay of the actual horizontal contour integrals -/

namespace Ostmann

open Complex Set MeasureTheory
open scoped Interval

/-- The local logarithmic derivative is at most cubic, while the fixed test
has eighth-order Mellin decay. The resulting horizontal integrals decay to zero. -/
theorem exists_smooth_horizontal_bound (χ : PrimitiveComplexCharacter) (X : ℝ) (hX : 2 ≤ X) :
    ∃ D : ℝ, 0 < D ∧ ∀ T : ℝ, 3 ≤ T → ∃ t : ℝ,
      T < t ∧ t < T + 1 ∧ (∀ z ∈ complexCharacterZeros χ, |z.im| ≠ t) ∧
      ∀ y : ℝ, y = t ∨ y = -t →
        ‖smoothHorizontalIntegral χ X y‖ ≤ D / (T + 1) ^ 5 := by
  obtain ⟨K, hK, hheight⟩ := exists_character_horizontal_bound χ
  obtain ⟨C, hC, hmellin⟩ := primeMeanMellin_decay_pow
  refine ⟨20 * K * X ^ 2 * C, by positivity, ?_⟩
  intro T hT
  obtain ⟨t, ht, ht', hzero, hlog⟩ := hheight T hT
  refine ⟨t, ht, ht', hzero, ?_⟩
  intro y hy
  have hTpos : 0 < T + 1 := by linarith
  have htpos : 0 < t := by linarith
  have hyabs : |y| = t := by rcases hy with rfl | rfl <;> simp [abs_of_pos htpos]
  have hpoint (σ : ℝ) (hσ : σ ∈ uIcc (-(1 / 2 : ℝ)) 2) :
      ‖(-deriv χ.L ((σ : ℂ) + y * I) / χ.L ((σ : ℂ) + y * I)) *
        smoothContourWeight X ((σ : ℂ) + y * I)‖ ≤
          8 * K * X ^ 2 * C / (T + 1) ^ 5 := by
    rw [uIcc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 2)] at hσ
    let s : ℂ := (σ : ℂ) + y * I
    have hsre : s.re = σ := by simp [s]
    have hsim : s.im = y := by simp [s]
    have hcp : ‖(X : ℂ) ^ s‖ ≤ X ^ 2 := by
      rw [norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < X), hsre]
      exact (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ X) hσ.2).trans_eq
        (Real.rpow_two X)
    have hm : ‖primeMeanMellin s‖ ≤ C / (T + 1) ^ 8 := by
      apply (hmellin s (by rw [hsre]; exact hσ.1) (by rw [hsre]; exact hσ.2)).trans
      rw [hsim, hyabs]
      exact div_le_div_of_nonneg_left hC.le (pow_pos hTpos 8)
        (pow_le_pow_left₀ hTpos.le (by linarith) 8)
    have hl : ‖logDeriv χ.L s‖ ≤ 8 * K * (T + 1) ^ 3 := by
      apply (hlog y hy σ hσ).trans
      have hp : (T + 5) ^ 3 ≤ 8 * (T + 1) ^ 3 := by
        calc
          _ ≤ (2 * (T + 1)) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
          _ = _ := by ring
      nlinarith
    change ‖(-deriv χ.L s / χ.L s) * smoothContourWeight X s‖ ≤ _
    rw [norm_mul, smoothContourWeight, norm_mul]
    have hn : ‖-deriv χ.L s / χ.L s‖ = ‖logDeriv χ.L s‖ := by
      simp [logDeriv_apply, neg_div]
    rw [hn]
    calc
      _ ≤ (8 * K * (T + 1) ^ 3) * (X ^ 2 * (C / (T + 1) ^ 8)) :=
        mul_le_mul hl (mul_le_mul hcp hm (norm_nonneg _) (by positivity)) (by positivity) (by positivity)
      _ = _ := by field_simp
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -(1 / 2 : ℝ)) (b := 2)
    (C := 8 * K * X ^ 2 * C / (T + 1) ^ 5)
    (f := fun σ : ℝ => (-deriv χ.L ((σ : ℂ) + y * I) / χ.L ((σ : ℂ) + y * I)) *
      smoothContourWeight X ((σ : ℂ) + y * I))
    (fun σ hσ => hpoint σ (uIoc_subset_uIcc hσ))
  change ‖smoothHorizontalIntegral χ X y‖ ≤ _ at hi
  norm_num at hi
  convert hi using 1 <;> first | rfl | ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothHorizontalLimit
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A zero-avoiding sequence along which both horizontal integrals vanish -/

namespace Ostmann

open Filter
open scoped Topology

theorem smooth_horizontal_integrals_tendsto (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 2 ≤ X) : ∃ t : ℕ → ℝ,
      (∀ n, 0 < t n) ∧ Tendsto t atTop atTop ∧
      (∀ n, ∀ z ∈ complexCharacterZeros χ, |z.im| ≠ t n) ∧
      Tendsto (fun n => smoothHorizontalIntegral χ X (t n)) atTop (𝓝 0) ∧
      Tendsto (fun n => smoothHorizontalIntegral χ X (-t n)) atTop (𝓝 0) := by
  obtain ⟨D, hD, hheight⟩ := exists_smooth_horizontal_bound χ X hX
  choose t ht ht' hzero hbound using fun n : ℕ =>
    hheight ((n : ℝ) + 3) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) + 3) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have htlim : Tendsto t atTop atTop := tendsto_atTop_mono (fun n => (ht n).le) hbase
  have hpower : Tendsto (fun n : ℕ => ((n : ℝ) + 3 + 1) ^ 5) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (5 : ℕ) ≠ 0)).comp
      (tendsto_atTop_add_const_right _ _ hbase)
  have hdecay : Tendsto (fun n : ℕ => D / ((n : ℝ) + 3 + 1) ^ 5) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hpower
  refine ⟨t, fun n => by linarith [ht n, Nat.cast_nonneg (α := ℝ) n], htlim, hzero, ?_, ?_⟩
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => hbound n (t n) (.inl rfl)) hdecay
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => hbound n (-t n) (.inr rfl)) hdecay

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothContourLimit
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing the actual finite contour identity to infinite height -/

namespace Ostmann

open Complex Filter MeasureTheory
open scoped Topology BigOperators Interval

theorem smooth_contour_limit (e : ∀ χ, ℕ ≃ CharacterZeroCopy χ)
    (χ : PrimitiveComplexCharacter) (X : ℝ) (hX : 2 ≤ X) :
    I * (∫ y : ℝ, rightContourIntegrand χ X y) -
      I * (∫ y : ℝ, leftContourIntegrand χ X y) =
    -(2 * (Real.pi : ℂ) * I) *
      ((∑' i, smoothZeroTerm (fun ψ => characterZeroEnumeration ψ (e ψ)) χ X i) +
        smoothTrivialZeroTerm χ) := by
  obtain ⟨t, htpos, htlim, hzero, htop, hbot⟩ := smooth_horizontal_integrals_tendsto χ X hX
  have htneg : Tendsto (fun n => -t n) atTop atBot := tendsto_neg_atTop_atBot.comp htlim
  have hr := intervalIntegral_tendsto_integral
    (rightContourIntegrand_integrable χ X (by linarith)) htneg htlim
  have hl := intervalIntegral_tendsto_integral
    (leftContourIntegrand_integrable χ X (by linarith)) htneg htlim
  let f : ℂ → ℂ := fun z => (-deriv χ.L z / χ.L z) * smoothContourWeight X z
  have hbd : Tendsto (fun n => rectangleBoundaryIntegral f (-(1 / 2)) 2 (-t n) (t n))
      atTop (𝓝 (I * (∫ y : ℝ, rightContourIntegrand χ X y) -
        I * (∫ y : ℝ, leftContourIntegrand χ X y))) := by
    have hh := ((hbot.sub htop).add (hr.const_mul I)).sub (hl.const_mul I)
    simpa [rectangleBoundaryIntegral, f, smoothHorizontalIntegral,
      rightContourIntegrand, leftContourIntegrand, primeMellinLine, primeVerticalWeight,
      leftContourLine, smoothContourWeight] using hh
  have hs := (smoothActualZeroSum_tendsto e χ X hX).comp htlim
  have hres : Tendsto (fun n => -(2 * (Real.pi : ℂ) * I) *
      ((∑ z ∈ criticalZerosUpTo χ (t n), (analyticOrderNatAt χ.L z : ℂ) * smoothContourWeight X z) +
        smoothTrivialZeroTerm χ)) atTop
      (𝓝 (-(2 * (Real.pi : ℂ) * I) *
        ((∑' i, smoothZeroTerm (fun ψ => characterZeroEnumeration ψ (e ψ)) χ X i) +
          smoothTrivialZeroTerm χ))) :=
    tendsto_const_nhds.mul (hs.add_const (smoothTrivialZeroTerm χ))
  apply tendsto_nhds_unique hbd
  apply hres.congr
  intro n
  exact (smoothContour_truncated χ X (by linarith) (t n) (htpos n) (hzero n)).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothExplicitIdentity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual smooth explicit formula with its left-contour remainder -/

namespace Ostmann

open Complex MeasureTheory
open scoped BigOperators

/-- The exact contour remainder. A faithful numbering of the actual zero
multiplicities is the only enumeration data used in the formula. -/
theorem smooth_explicit_identity (e : ∀ χ, ℕ ≃ CharacterZeroCopy χ)
    (χ : PrimitiveComplexCharacter) (X : ℝ) (hX : 2 ≤ X) :
    smoothMangoldtMean χ.modulus χ.character X +
      (∑' i, smoothZeroTerm (fun ψ => characterZeroEnumeration ψ (e ψ)) χ X i) +
      smoothTrivialZeroTerm χ =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ y : ℝ, leftContourIntegrand χ X y := by
  let R := ∫ y : ℝ, rightContourIntegrand χ X y
  let L := ∫ y : ℝ, leftContourIntegrand χ X y
  let S := ∑' i, smoothZeroTerm (fun ψ => characterZeroEnumeration ψ (e ψ)) χ X i
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hcont := smooth_contour_limit e χ X hX
  change I * R - I * L = -(2 * (Real.pi : ℂ) * I) * (S + smoothTrivialZeroTerm χ) at hcont
  have hrel : R - L = -(2 * (Real.pi : ℂ)) * (S + smoothTrivialZeroTerm χ) := by
    apply mul_left_cancel₀ (show (I : ℂ) ≠ 0 by simp)
    calc
      I * (R - L) = I * R - I * L := mul_sub _ _ _
      _ = _ := hcont
      _ = _ := by ring
  have hc : c * (2 * (Real.pi : ℂ)) = 1 := by
    dsimp [c]
    push_cast
    field_simp
  have hmean : smoothMangoldtMean χ.modulus χ.character X = c * R :=
    smoothMangoldtMean_eq_vertical_logDerivative χ X (by linarith)
  have hsum : R + (2 * (Real.pi : ℂ)) * (S + smoothTrivialZeroTerm χ) = L := by
    linear_combination hrel
  change smoothMangoldtMean χ.modulus χ.character X + S + smoothTrivialZeroTerm χ = c * L
  rw [hmean, ← hsum, mul_add, ← mul_assoc, hc, one_mul]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothActualExplicitFormula
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Discharging the fixed-test smooth explicit-formula input -/

namespace Ostmann

open Complex MeasureTheory
open scoped BigOperators

theorem actual_smooth_explicit_formula (e : ∀ χ, ℕ ≃ CharacterZeroCopy χ) :
    ∃ E : ℝ, 0 < E ∧ ∀ (χ : PrimitiveComplexCharacter) (X : ℝ), 2 ≤ X →
      ‖smoothMangoldtMean χ.modulus χ.character X +
        (∑' i, smoothZeroTerm (fun ψ => characterZeroEnumeration ψ (e ψ)) χ X i) +
          smoothTrivialZeroTerm χ‖ ≤ E / Real.sqrt X * Real.log (2 * (χ.modulus : ℝ)) := by
  obtain ⟨E, hE, hbound⟩ := leftContour_integral_bound
  refine ⟨E, hE, ?_⟩
  intro χ X hX
  rw [smooth_explicit_identity e χ X hX, norm_mul]
  have hc : ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    apply (div_le_one (by positivity)).mpr
    linarith [Real.pi_gt_three]
  exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans (hbound χ X (by linarith))

noncomputable def actualSmoothExplicitFormula (e : ∀ χ, ℕ ≃ CharacterZeroCopy χ) :
    PublishedSmoothExplicitFormula (fun χ => characterZeroEnumeration χ (e χ)) := by
  let E := Classical.choose (actual_smooth_explicit_formula e)
  have hE := (Classical.choose_spec (actual_smooth_explicit_formula e)).1
  have hformula := (Classical.choose_spec (actual_smooth_explicit_formula e)).2
  exact smoothExplicitFormula_of_multiplicity
    (fun χ => characterZeroEnumeration_respectsMultiplicity χ (e χ)) E hE hformula

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ActualProgressionInput
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prime-progression estimate with constructed exceptional zeros

This is the theta estimate of Montgomery–Vaughan, Corollary 11.20. The actual
exceptional-zero family records divisibility, completeness and Page uniqueness.
-/

namespace Ostmann

noncomputable def progressionInput_of_actual_theta (h : ActualProgressionTheta) :
    PublishedProgressionInput := {
  kappa := actualPageConstant
  decay := Classical.choose h
  errorConstant := Classical.choose (Classical.choose_spec h)
  kappa_pos := actualPageConstant_pos
  decay_pos := (Classical.choose_spec (Classical.choose_spec h)).1
  errorConstant_nonneg := (Classical.choose_spec (Classical.choose_spec h)).2.1
  localZero := actualLocalZero
  divides := fun q e he => (actualLocalZero_spec q e he).1
  complete := actualLocalZero_complete
  unique := actualPage_unique
  theta := (Classical.choose_spec (Classical.choose_spec h)).2.2 }

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CanonicalRieszKernelBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform kernel bounds for the canonical exceptional zeros

For large conductors the Page cutoff is to the right of one half. The
remaining finitely many moduli contribute a finite constant.
-/

namespace Ostmann

open Complex

theorem canonicalCharacterRieszTerm_norm_bound (χ : PrimitiveComplexCharacter)
    (q : ℕ) (X C : ℝ) (hX : 0 < X) (hC : 0 ≤ C)
    (hbound : pageRieszKernelNorm q ≤ C) :
    ‖canonicalCharacterRieszTerm χ q X‖ ≤ C * X ^ pageBeta (actualLocalZero q) := by
  classical
  cases he : actualLocalZero q with
  | none => simp only [canonicalCharacterRieszTerm, he, norm_zero, pageBeta]; positivity
  | some e =>
    by_cases hc : e.asRealCharacter.asComplex = χ
    · simp only [canonicalCharacterRieszTerm, he, hc, ↓reduceIte, norm_neg,
        rieszContourWeight, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX,
        Complex.ofReal_re, pageBeta]
      have hh : ‖rieszMellinKernel (e.beta : ℂ)‖ ≤ C := by
        simpa only [pageRieszKernelNorm, he, pageBeta] using hbound
      nlinarith [Real.rpow_pos_of_pos hX e.beta]
    · simp only [canonicalCharacterRieszTerm, he, hc, ↓reduceIte, norm_zero, pageBeta]
      positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterCanonicalRieszComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Replacing the local contour zero by the canonical Page correction -/

namespace Ostmann

open Complex

theorem character_riesz_term_comparison (χ : PrimitiveComplexCharacter) (q : ℕ)
    (T c X C : ℝ) (e : Option ℕ)
    (hq : 1 ≤ q) (hdvd : χ.modulus ∣ q) (hqT : (q : ℝ) ≤ T) (hT : 2 ≤ T)
    (hc : 0 < c) (hcp : c ≤ actualPageConstant / 10) (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hkernel : pageRieszKernelNorm q ≤ C)
    (he : ∀ i, e = some i →
      1 - 2 * c / (Real.log χ.modulus + Real.log (T + 4) + 1) <
        ((actualCharacterZeros χ).zeros i).re ∧
      χ.character ^ 2 = 1 ∧ ((actualCharacterZeros χ).zeros i).im = 0)
    (hec : ∀ i, 1 - c / (Real.log χ.modulus + Real.log (T + 4) + 1) ≤
      ((actualCharacterZeros χ).zeros i).re →
      |((actualCharacterZeros χ).zeros i).im| ≤ T → e = some i) :
    ‖characterRieszZeroTerm χ X e - canonicalCharacterRieszTerm χ q X‖ ≤
      C * X ^ (1 - c / (Real.log χ.modulus + Real.log (T + 4) + 1)) := by
  classical
  have hXp : 0 < X := by linarith
  cases e with
  | some i =>
    obtain ⟨hbeta, hsq, him⟩ := he i rfl
    rw [selected_riesz_term_eq_canonical χ q i T c X hq hdvd hqT hT hc hcp hsq him hbeta,
      sub_self, norm_zero]
    positivity
  | none =>
    simp only [characterRieszZeroTerm, zero_sub, norm_neg]
    cases hpage : actualLocalZero q with
    | none => simp only [canonicalCharacterRieszTerm, hpage, norm_zero]; positivity
    | some r =>
      by_cases hχ : r.asRealCharacter.asComplex = χ
      · have hzero : χ.L (r.beta : ℂ) = 0 := by
          rw [← hχ]
          exact r.zero
        obtain ⟨i, hi⟩ := character_zero_enumerated_of_re_pos χ (r.beta : ℂ)
          (by simpa using r.beta_pos) hzero
        have hβ : r.beta < 1 - c / (Real.log χ.modulus + Real.log (T + 4) + 1) := by
          by_contra hn
          have hh := hec i (by simpa only [hi, Complex.ofReal_re] using not_lt.mp hn)
            (by simp only [hi, Complex.ofReal_im, abs_zero]; linarith)
          cases hh
        have hh := canonicalCharacterRieszTerm_norm_bound χ q X C hXp hC hkernel
        have hp : pageBeta (actualLocalZero q) = r.beta := by simp only [hpage, pageBeta]
        rw [hp] at hh
        exact hh.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hX hβ.le) hC)
      · simp only [canonicalCharacterRieszTerm, hpage, hχ, ↓reduceIte, norm_zero]
        positivity

theorem character_riesz_canonical_bound : ∃ c A B E : ℝ,
    0 < c ∧ c ≤ 1 / 4 ∧ 0 < A ∧ 0 < B ∧ 0 < E ∧
    ∀ (q : ℕ) (χ : PrimitiveComplexCharacter) (T X b : ℝ),
      1 ≤ q → χ.modulus ∣ q → (q : ℝ) ≤ T → 2 ≤ T → 1 ≤ X → 1 < b → b ≤ 2 →
      let H := Real.log χ.modulus + Real.log (T + 4) + 1
      ‖characterRieszMean χ X - canonicalCharacterRieszTerm χ q X‖ ≤
        A * H ^ 2 * X ^ (1 - c / H) + B * H ^ 2 * X ^ b / T ^ 2 +
          2 * (1 / (b - 1) + E) * X ^ b / T := by
  obtain ⟨c, A, B, E, hc, hc4, hcp, hA, hB, hE, hbound⟩ := character_riesz_local_bound
  obtain ⟨C, hC, hkernel⟩ := canonical_riesz_kernel_bound
  refine ⟨c, A + C, B, E, hc, hc4, by positivity, hB, hE, ?_⟩
  intro q χ T X b hq hdvd hqT hT hX hb hb2
  dsimp only
  let H := Real.log χ.modulus + Real.log (T + 4) + 1
  have hqlog : 0 ≤ Real.log χ.modulus := Real.log_nonneg (by exact_mod_cast χ.positive)
  have hTlog : 0 ≤ Real.log (T + 4) := Real.log_nonneg (by linarith)
  have hH : 1 ≤ H := by dsimp [H]; linarith
  obtain ⟨e, he, hec, hr⟩ := hbound χ T hT
  have hlocal := hr X b hX hb hb2
  have hd := character_riesz_term_comparison χ q T c X C e hq hdvd hqT hT hc hcp hX hC.le
    (hkernel q) he hec
  have ht := norm_sub_le_norm_sub_add_norm_sub (characterRieszMean χ X)
    (characterRieszZeroTerm χ X e) (canonicalCharacterRieszTerm χ q X)
  have hsq : 1 ≤ H ^ 2 := by nlinarith
  have hx : 0 ≤ X ^ (1 - c / H) := Real.rpow_nonneg (by linarith) _
  have hcost : C * X ^ (1 - c / H) ≤ C * H ^ 2 * X ^ (1 - c / H) := by
    have hh := mul_le_mul_of_nonneg_left hsq (mul_nonneg hC.le hx)
    first | (convert hh using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))
  change ‖characterRieszMean χ X - canonicalCharacterRieszTerm χ q X‖ ≤
    (A + C) * H ^ 2 * X ^ (1 - c / H) + B * H ^ 2 * X ^ b / T ^ 2 +
      2 * (1 / (b - 1) + E) * X ^ b / T
  change ‖characterRieszMean χ X - characterRieszZeroTerm χ X e‖ ≤
    A * H ^ 2 * X ^ (1 - c / H) + B * H ^ 2 * X ^ b / T ^ 2 +
      2 * (1 / (b - 1) + E) * X ^ b / T at hlocal
  change ‖characterRieszZeroTerm χ X e - canonicalCharacterRieszTerm χ q X‖ ≤
    C * X ^ (1 - c / H) at hd
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterCanonicalRieszDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform character Riesz decay with the canonical Page correction -/

namespace Ostmann

open Filter

theorem character_riesz_canonical_decay : ∃ d : ℝ, 0 < d ∧
    ∀ᶠ y : ℝ in atTop, ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.exp y →
      ∀ χ : PrimitiveComplexCharacter, χ.modulus ∣ q →
        ‖characterRieszMean χ (Real.exp (y ^ 2)) -
            canonicalCharacterRieszTerm χ q (Real.exp (y ^ 2))‖ ≤
          3 * Real.exp (y ^ 2 - d * y) := by
  obtain ⟨c, A, B, E, hc, hc4, hA, hB, hE, hbound⟩ := character_riesz_canonical_bound
  refine ⟨c / 6, by positivity, ?_⟩
  filter_upwards [riesz_exponential_error c A B E hc hc4 hA.le hB.le hE.le,
    eventually_ge_atTop (5 : ℝ)] with y hy hy5
  intro q hq hqy χ hdvd
  have hy0 : 0 < y := by linarith
  have hT : 2 ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  have hb1 : 1 < 1 + 1 / y ^ 2 := by
    have hh : 0 < 1 / y ^ 2 := by positivity
    linarith
  have hb2 : 1 + 1 / y ^ 2 ≤ 2 := by
    have hys : 1 ≤ y ^ 2 := by nlinarith
    have hh : 1 / y ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr hys
    linarith
  have hr := hbound q χ (Real.exp y) (Real.exp (y ^ 2)) (1 + 1 / y ^ 2)
    hq hdvd hqy hT (Real.one_le_exp (sq_nonneg y)) hb1 hb2
  have hχq : (χ.modulus : ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (by omega : 0 < q) hdvd
  have hχ : (χ.modulus : ℝ) ≤ Real.exp y := hχq.trans hqy
  obtain ⟨hH, hHy⟩ := character_riesz_height_log_bound χ y hy5 hχ
  exact hr.trans (hy _ hH hHy)

theorem character_riesz_canonical_sqrt_decay : ∃ d : ℝ, 0 < d ∧
    ∀ᶠ X : ℝ in atTop, ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.exp (Real.sqrt (Real.log X)) →
      ∀ χ : PrimitiveComplexCharacter, χ.modulus ∣ q →
        ‖characterRieszMean χ X - canonicalCharacterRieszTerm χ q X‖ ≤
          3 * X * Real.exp (-d * Real.sqrt (Real.log X)) := by
  obtain ⟨d, hd, h⟩ := character_riesz_canonical_decay
  refine ⟨d, hd, ?_⟩
  have ht := Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually h, eventually_ge_atTop (1 : ℝ)] with X hX hX1
  have hx : 0 < X := by linarith
  have heq : Real.exp ((Real.sqrt (Real.log X)) ^ 2) = X := by
    rw [Real.sq_sqrt (Real.log_nonneg hX1), Real.exp_log hx]
  intro q hq hqX χ hχ
  have hh := hX q hq hqX χ hχ
  dsimp only [Function.comp_apply] at hh
  rw [heq, Real.exp_sub, Real.sq_sqrt (Real.log_nonneg hX1), Real.exp_log hx] at hh
  simpa only [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, neg_mul] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ArithmeticRieszMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal finite Riesz sums and character orthogonality -/

namespace Ostmann

open Complex
open scoped BigOperators

theorem rieszTwistMean_eq_character (χ : PrimitiveComplexCharacter) (X : ℝ) (hX : 0 < X) :
    rieszTwistMean (fun n => χ.character (n : ZMod χ.modulus)) X = characterRieszMean χ X := by
  have hs (n : ℕ) (hn : n ∉ Finset.Ioc 0 ⌊X⌋₊) :
      characterMangoldtCoefficient χ n * rieszPrimeTest (n / X) = 0 := by
    by_cases hn0 : n = 0
    · subst n; simp [characterMangoldtCoefficient]
    · have hnlarge : ⌊X⌋₊ < n := by simp only [Finset.mem_Ioc] at hn; omega
      have hlarge : X < n := Nat.lt_of_floor_lt hnlarge
      have hdiv : 1 < (n : ℝ) / X := (one_lt_div hX).mpr hlarge
      simp only [rieszPrimeTest, max_eq_right (by linarith : 1 - (n : ℝ) / X ≤ 0),
        Complex.ofReal_zero, mul_zero]
  rw [characterRieszMean, tsum_eq_sum hs]
  unfold rieszTwistMean
  apply Finset.sum_congr rfl
  intro n _
  unfold characterMangoldtCoefficient
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrimitiveRieszComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Riesz means after passage to the actual primitive character -/

namespace Ostmann

theorem rieszTwistMean_primitive_comparison {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (X : ℝ) (hX : 1 ≤ X) :
    ‖rieszTwistMean (fun n => χ (n : ZMod q)) X -
        reducedRieszMean (primitiveCharacterReduction χ) X‖ ≤
      2 * q * Real.log X + 4 * Real.sqrt X * Real.log X := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hXp : 0 < X := by linarith
  cases he : primitiveCharacterReduction χ with
  | none =>
    have hχ : χ = 1 := by
      have hh := lift_primitiveCharacterReduction χ
      rw [he] at hh
      exact hh.symm
    simp only [reducedRieszMean]
    rw [← rieszTwistMean_eq_principal X hXp]
    apply rieszTwistMean_coprime_comparison _ _ q X hq hX
      (fun n => χ.norm_le_one _) (by intro n; simp)
    intro n hn
    rw [hχ]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr hn)
  | some ρ =>
    simp only [reducedRieszMean]
    rw [← rieszTwistMean_eq_character ρ X hXp]
    exact rieszTwistMean_coprime_comparison _ _ q X hq hX
      (fun n => χ.norm_le_one _) (fun n => ρ.character.norm_le_one _)
      (primitiveReduction_agrees χ ρ he)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ZetaLocalFactorBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Keeping the actual local zeta factors in the logarithmic-derivative bound -/

namespace Ostmann

open Complex Metric Set
open scoped BigOperators

theorem zeta_local_factor_bound : ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (w : ℂ),
    ‖w‖ ≤ 5 / 4 → zetaAtHeight t w ≠ 0 →
    ‖logDeriv (zetaAtHeight t) w -
      ∑ z ∈ zetaDiskZeros t, (analyticOrderNatAt (zetaAtHeight t) z : ℂ) / (w - z)‖ ≤
        C * Real.log (|t| + 2) := by
  obtain ⟨C, hC, hbudget⟩ := zeta_local_log_budget
  refine ⟨C, hC, ?_⟩
  intro t w hw hfne
  obtain ⟨g, hg, he, hne⟩ := zeta_disk_quotient_exists t
  let M := 32 * (|t| + 2) ^ 2
  let N := ∑ z ∈ zetaDiskZeros t, (analyticOrderNatAt (zetaAtHeight t) z : ℝ)
  let A := Real.log (3 * M) + N * Real.log 6 + 1
  have hA : 0 < A := by
    have hM : 1 ≤ M := by dsimp [M]; nlinarith [abs_nonneg t, sq_nonneg (|t| + 2)]
    have hl : 0 ≤ Real.log (3 * M) := Real.log_nonneg (by linarith)
    have hl6 : 0 ≤ Real.log (6 : ℝ) := Real.log_nonneg (by norm_num)
    have hN : 0 ≤ N := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    dsimp [A]
    positivity
  have hgb := logDeriv_norm_le_five_quarters_disk g A hA (fun z _ => hg z)
    (fun z hz => hne z (ball_subset_closedBall hz)) (fun z hz => ?_) w hw
  · have hwball : w ∈ closedBall 0 (3 / 2 : ℝ) := by
      simpa using hw.trans (by norm_num : (5 / 4 : ℝ) ≤ 3 / 2)
    have hwS : w ∉ zetaDiskZeros t := fun hh => hfne ((mem_zetaDiskZeros t w).mp hh).2
    have hsplit : logDeriv (zetaAtHeight t) w =
        (∑ z ∈ zetaDiskZeros t, (analyticOrderNatAt (zetaAtHeight t) z : ℂ) / (w - z)) +
          logDeriv g w := by
      have hfun := funext he
      conv_lhs => rw [hfun]
      rw [logDeriv_mul w (finiteZeroPolynomial_ne_zero _ _ w hwS) (hne w hwball)
        (finiteZeroPolynomial_analytic _ _ w).differentiableAt (hg w).differentiableAt,
        finiteZeroPolynomial_logDeriv _ _ w hwS]
    rw [hsplit, add_sub_cancel_left]
    have hmass := zetaDiskZeros_mass_bound t
    have hprod := mul_le_mul_of_nonneg_right hmass (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 6))
    have hlog : Real.log (3 * M) = Real.log (96 * (|t| + 2) ^ 2) := by
      congr 1
      dsimp [M]
      ring
    apply hgb.trans
    apply le_trans _ (hbudget t)
    dsimp [A, N]
    rw [hlog]
    linarith
  · exact (zeta_disk_quotient_log_bound t M le_rfl g hg he hne z
      (by simpa using (mem_ball_iff_norm.mp hz).le)).trans (by dsimp [A, N]; linarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ZetaLocalSeparation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative local zeta bounds away from its actual zeros -/

namespace Ostmann

open Complex
open scoped BigOperators

theorem zeta_local_mass_bound : ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ,
    (∑ z ∈ zetaDiskZeros t, (analyticOrderNatAt (zetaAtHeight t) z : ℝ)) ≤
      D * Real.log (|t| + 2) := by
  let D := (Real.log 96 / Real.log 2 + 2) / Real.log (7 / 6)
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h96 : 0 < Real.log (96 : ℝ) := Real.log_pos (by norm_num)
  have h76 : 0 < Real.log (7 / 6 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro t
  have hL : Real.log 2 ≤ Real.log (|t| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hconst : Real.log 96 ≤ (Real.log 96 / Real.log 2) * Real.log (|t| + 2) := by
    have hm := mul_le_mul_of_nonneg_left hL (div_nonneg h96.le h2.le)
    have he : (Real.log 96 / Real.log 2) * Real.log 2 = Real.log 96 := by field_simp
    rwa [he] at hm
  apply (zetaDiskZeros_mass_bound t).trans
  have hlog : Real.log (96 * (|t| + 2) ^ 2) = Real.log 96 + 2 * Real.log (|t| + 2) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    rfl
  rw [hlog]
  dsimp [D]
  apply (div_le_iff₀ h76).mpr
  have he : (Real.log 96 / Real.log 2 + 2) / Real.log (7 / 6) *
      Real.log (|t| + 2) * Real.log (7 / 6) =
      (Real.log 96 / Real.log 2 + 2) * Real.log (|t| + 2) := by field_simp
  rw [he]
  nlinarith

theorem zeta_local_logDeriv_separated : ∃ C : ℝ, 0 < C ∧
    ∀ (t : ℝ) (w : ℂ) (δ : ℝ), ‖w‖ ≤ 5 / 4 → zetaAtHeight t w ≠ 0 → 0 < δ →
      (∀ z ∈ zetaDiskZeros t, δ ≤ ‖w - z‖) →
      ‖logDeriv (zetaAtHeight t) w‖ ≤
        C * Real.log (|t| + 2) * (1 + δ⁻¹) := by
  obtain ⟨A, hA, ha⟩ := zeta_local_factor_bound
  obtain ⟨D, hD, hd⟩ := zeta_local_mass_bound
  refine ⟨A + D, by positivity, ?_⟩
  intro t w δ hw hne hδ hsep
  have hsum : ‖∑ z ∈ zetaDiskZeros t,
      (analyticOrderNatAt (zetaAtHeight t) z : ℂ) / (w - z)‖ ≤
        (∑ z ∈ zetaDiskZeros t, (analyticOrderNatAt (zetaAtHeight t) z : ℝ)) / δ := by
    apply (norm_sum_le _ _).trans
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro z hz
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ (hsep z hz)
  have hmass := div_le_div_of_nonneg_right (hd t) hδ.le
  have he := norm_le_norm_sub_add (logDeriv (zetaAtHeight t) w)
    (∑ z ∈ zetaDiskZeros t, (analyticOrderNatAt (zetaAtHeight t) z : ℂ) / (w - z))
  have herr := ha t w hw hne
  have hlog : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hAlog := mul_nonneg hA.le hlog
  have hDlog := mul_nonneg hD.le hlog
  have hAinv := mul_nonneg hAlog (inv_nonneg.mpr hδ.le)
  simp only [div_eq_mul_inv] at hmass hsum he herr
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ZetaNearZeroBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A near-one zeta zero contributes its full reciprocal gap -/

namespace Ostmann

open Complex Metric Set
open scoped BigOperators

theorem zetaAtHeight_logDeriv_translate (t : ℝ) (w : ℂ) :
    logDeriv (zetaAtHeight t) w = logDeriv regularizedZeta (w + characterZeroCenter t) := by
  change logDeriv (regularizedZeta ∘ (fun z : ℂ => z + characterZeroCenter t)) w = _
  rw [logDeriv_comp (g := fun z : ℂ => z + characterZeroCenter t)
    (regularizedZeta_analytic _).differentiableAt (differentiableAt_id.add_const _)]
  simp

theorem zeta_near_zero_gap_bound : ∃ C : ℝ, 0 < C ∧ ∀ (ρ : ℂ),
    regularizedZeta ρ = 0 → 1 / 2 ≤ ρ.re → ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      1 / (σ - ρ.re) ≤
        (logDeriv regularizedZeta ((σ : ℂ) + (ρ.im : ℂ) * I)).re +
          C * Real.log (|ρ.im| + 2) := by
  obtain ⟨C, hC, hbound⟩ := zeta_local_factor_bound
  refine ⟨C, hC, ?_⟩
  intro ρ hρ hρhalf σ hσ hσ2
  have hρ1 := regularizedZeta_zero_re_lt_one ρ hρ
  let t := ρ.im
  let w : ℂ := ((σ - 2 : ℝ) : ℂ)
  let z : ℂ := ρ - characterZeroCenter t
  have hzval : z = ((ρ.re - 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [z, t, characterZeroCenter]
  have hz : z ∈ zetaDiskZeros t := by
    apply (mem_zetaDiskZeros t z).mpr
    refine ⟨?_, ?_⟩
    · rw [hzval, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      linarith
    · simpa only [zetaAtHeight, z, sub_add_cancel] using hρ
  have hw : ‖w‖ ≤ 5 / 4 := by
    rw [show w = ((σ - 2 : ℝ) : ℂ) from rfl, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    linarith
  have hwne : zetaAtHeight t w ≠ 0 := by
    apply regularizedZeta_ne_zero_right
    simp only [w, Complex.add_re, Complex.ofReal_re, characterZeroCenter_re]
    linarith
  have hb := hbound t w hw hwne
  have hnonneg (v : ℂ) (hv : v ∈ zetaDiskZeros t) :
      0 ≤ ((analyticOrderNatAt (zetaAtHeight t) v : ℂ) / (w - v)).re := by
    have hvre := zetaAtHeight_zero_left t v ((mem_zetaDiskZeros t v).mp hv).2
    rw [div_eq_mul_inv, Complex.mul_re]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    apply mul_nonneg (Nat.cast_nonneg _)
    rw [Complex.inv_re]
    apply div_nonneg _ (Complex.normSq_nonneg _)
    simp only [Complex.sub_re, w, Complex.ofReal_re]
    linarith
  have hsingle := Finset.single_le_sum hnonneg hz
  have hord : 1 ≤ analyticOrderNatAt (zetaAtHeight t) z := by
    have he := (zetaAtHeight_analytic t z).analyticOrderAt_ne_zero.mpr
      ((mem_zetaDiskZeros t z).mp hz).2
    rw [← Nat.cast_analyticOrderNatAt (zetaAtHeight_order_ne_top t z)] at he
    have hn : analyticOrderNatAt (zetaAtHeight t) z ≠ 0 := by simpa using he
    omega
  have hdiff : w - z = ((σ - ρ.re : ℝ) : ℂ) := by
    rw [hzval]
    simp only [w]
    push_cast
    ring
  have hterm : ((analyticOrderNatAt (zetaAtHeight t) z : ℂ) / (w - z)).re =
      (analyticOrderNatAt (zetaAtHeight t) z : ℝ) / (σ - ρ.re) := by
    rw [hdiff]
    exact (Complex.ofReal_div _ _).symm ▸ rfl
  rw [hterm] at hsingle
  have hone : 1 / (σ - ρ.re) ≤ (analyticOrderNatAt (zetaAtHeight t) z : ℝ) / (σ - ρ.re) := by
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact_mod_cast hord
  have herr := Complex.re_le_norm
    (-(logDeriv (zetaAtHeight t) w -
      ∑ v ∈ zetaDiskZeros t, (analyticOrderNatAt (zetaAtHeight t) v : ℂ) / (w - v)))
  rw [norm_neg, Complex.neg_re, Complex.sub_re, Complex.re_sum] at herr
  have htranslate : w + characterZeroCenter t = (σ : ℂ) + (ρ.im : ℂ) * I := by
    apply Complex.ext <;> simp [w, t, characterZeroCenter]
  rw [zetaAtHeight_logDeriv_translate, htranslate] at herr
  rw [zetaAtHeight_logDeriv_translate, htranslate] at hb
  dsimp only [t] at hb herr hsingle
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ZetaTrigonometric
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The zeta 3-4-1 inequality and the reciprocal-gap bound -/

namespace Ostmann

open Complex

theorem zeta_near_zero_trigonometric_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (ρ : ℂ), regularizedZeta ρ = 0 → 1 / 2 ≤ ρ.re →
      ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
        4 / (σ - ρ.re) ≤ 3 / (σ - 1) +
          4 * realZeroKernel (σ - 1) ρ.im +
          realZeroKernel (σ - 1) (2 * ρ.im) + C * (Real.log (|ρ.im| + 2) + 1) := by
  obtain ⟨A, hA, ha⟩ := zeta_near_zero_gap_bound
  obtain ⟨B, hB, hb⟩ := exists_vonMangoldt_logarithmic_upper
  obtain ⟨V, hV, hv⟩ := exists_vonMangoldt_series_bound
  refine ⟨4 * A + 2 * B + 3 * V, by positivity, ?_⟩
  intro ρ hρ hρhalf σ hσ hσ2
  let s : ℂ := (σ : ℂ) + (ρ.im : ℂ) * I
  have ht := zeta_trigonometric_nonneg σ ρ.im hσ
  have hgap := ha ρ hρ hρhalf σ hσ hσ2
  have hright := hb ((σ : ℂ) + ((2 * ρ.im : ℝ) : ℂ) * I)
    (by simpa using hσ) (by simpa using hσ2)
  have hreal := (Complex.re_le_norm _).trans (hv σ hσ hσ2)
  have hformula := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (s := s) (by simpa [s] using hσ)
  change LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s = _ at hformula
  have hreg := regularizedZeta_logDeriv s (by simpa [s] using hσ)
  have hker : ((s - 1)⁻¹).re = realZeroKernel (σ - 1) ρ.im := by
    simpa [s] using realZeroKernel_complex_sub s 1
  have hid : (logDeriv regularizedZeta s).re = realZeroKernel (σ - 1) ρ.im -
      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s).re := by
    rw [hreg, Complex.add_re, hker, hformula, neg_div, Complex.neg_re]
    simp only [logDeriv_apply]
    ring
  change 1 / (σ - ρ.re) ≤ (logDeriv regularizedZeta s).re + _ at hgap
  rw [hid] at hgap
  have hdouble := log_double_abs_height_le ρ.im
  have hlog : 0 ≤ Real.log (|ρ.im| + 2) := Real.log_nonneg (by linarith [abs_nonneg ρ.im])
  have hBdouble := mul_le_mul_of_nonneg_left hdouble hB.le
  have hAlog := mul_nonneg hA.le hlog
  have hBlog := mul_nonneg hB.le hlog
  have hVlog := mul_nonneg hV.le hlog
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, add_zero, zero_add, sub_zero] at hright
  dsimp only [s] at hgap
  simp only [div_eq_mul_inv] at hreal hgap ⊢
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ZetaZeroFreeRegion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A logarithmic zero-free region for the regularized zeta function -/

namespace Ostmann

open Complex Filter Metric
open scoped Topology

theorem regularizedZeta_zero_free_region : ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 4 ∧
    ∀ ρ : ℂ, regularizedZeta ρ = 0 →
      c / (Real.log (|ρ.im| + 2) + 1) ≤ 1 - ρ.re := by
  obtain ⟨r, hr, hr4, hsmall⟩ := regularizedZeta_small_height_gap
  obtain ⟨C, hC, hbound⟩ := zeta_near_zero_trigonometric_bound
  let D := C + 5 / r ^ 2
  have hD : 0 < D := by dsimp [D]; positivity
  let c := min r (1 / (2000 * (D + 1)))
  have hc : 0 < c := lt_min hr (by positivity)
  have hcr : c ≤ r := min_le_left _ _
  have hcc : c ≤ 1 / (2000 * (D + 1)) := min_le_right _ _
  refine ⟨c, hc, hcr.trans hr4, ?_⟩
  intro ρ hρ
  let H := Real.log (|ρ.im| + 2) + 1
  have hH : 1 ≤ H := by
    have hh := Real.log_nonneg (show 1 ≤ |ρ.im| + 2 by linarith [abs_nonneg ρ.im])
    dsimp [H]
    linarith
  have hHp : 0 < H := by linarith
  let δ := 1 / (100 * (D + 1) * H)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hbudget : δ * (D * H) ≤ 1 / 100 := by
    dsimp [δ]
    have he : (1 / (100 * (D + 1) * H)) * (D * H) = D / (100 * (D + 1)) := by
      field_simp
    rw [he]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hcut : c / H ≤ δ / 20 := by
    have hh := div_le_div_of_nonneg_right hcc hHp.le
    apply hh.trans_eq
    dsimp [δ]
    field_simp
    ring
  have hcrH : c / H ≤ r := by
    calc
      c / H ≤ c / 1 := div_le_div_of_nonneg_left hc.le (by norm_num) hH
      _ ≤ r := by simpa using hcr
  by_contra hnot
  have hnear : 1 - δ / 20 ≤ ρ.re := by
    change ¬c / H ≤ 1 - ρ.re at hnot
    linarith [lt_of_not_ge hnot]
  have hnearR : 1 - r ≤ ρ.re := by
    change ¬c / H ≤ 1 - ρ.re at hnot
    linarith [lt_of_not_ge hnot]
  have hhalf : 1 / 2 ≤ ρ.re := by linarith
  have hi := hsmall ρ hρ hnearR
  have hk1 := realZeroKernel_away_bound r δ ρ.im hr hδ hδ1 hi
  have hk2 := realZeroKernel_away_bound r δ (2 * ρ.im) hr hδ hδ1 (by
    rw [abs_mul]
    norm_num
    linarith)
  have hupper := hbound ρ hρ hhalf (1 + δ) (by linarith) (by linarith)
  simp only [add_sub_cancel_left] at hupper
  have hcost : 5 / r ^ 2 ≤ (5 / r ^ 2) * H := by
    exact le_mul_of_one_le_right (by positivity) hH
  have hup : 4 / (1 + δ - ρ.re) ≤ 3 / δ + D * H := by
    dsimp [D, H]
    dsimp [H] at hcost
    simp only [div_eq_mul_inv] at hk1 hk2 hupper hcost ⊢
    nlinarith
  have hρ1 := regularizedZeta_zero_re_lt_one ρ hρ
  have hmass := real_zero_shifted_mass δ (1 + δ - ρ.re) hδ (by linarith) (by linarith)
  have hp := mul_le_mul_of_nonneg_left hup hδ.le
  have he : δ * (3 / δ + D * H) = 3 + δ * (D * H) := by field_simp
  rw [he] at hp
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ZetaZeroFreeLogDerivative
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A logarithmic-squared bound for the regularized zeta function -/

namespace Ostmann

open Complex

theorem zeta_zero_free_logDeriv_data : ∃ c C : ℝ,
    0 < c ∧ c ≤ 1 / 4 ∧ 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      ∀ s : ℂ, 1 - c / (Real.log (T + 4) + 1) ≤ s.re → s.re ≤ 2 → |s.im| ≤ T →
        regularizedZeta s ≠ 0 ∧ ‖logDeriv regularizedZeta s‖ ≤
          C * (Real.log (T + 4) + 1) ^ 2 := by
  obtain ⟨c0, hc0, _, hregion⟩ := regularizedZeta_zero_free_region
  obtain ⟨B, hB, hbound⟩ := zeta_local_logDeriv_separated
  let c := min (c0 / 4) (1 / 4)
  have hc : 0 < c := lt_min (by positivity) (by norm_num)
  have hcc : 4 * c ≤ c0 := by
    have hh := min_le_left (c0 / 4) (1 / 4)
    dsimp [c]
    linarith
  have hc4 : c ≤ 1 / 4 := min_le_right _ _
  refine ⟨c, B * (1 + c⁻¹), hc, hc4, by positivity, ?_⟩
  intro T hT s hs hs2 ht
  let H := Real.log (T + 4) + 1
  have hH : 1 ≤ H := by
    have hh := Real.log_nonneg (show 1 ≤ T + 4 by linarith)
    dsimp [H]
    linarith
  have hHp : 0 < H := by linarith
  let δ := c / H
  have hδ : 0 < δ := div_pos hc hHp
  have hδ4 : δ ≤ 1 / 4 := by
    calc
      c / H ≤ c / 1 := div_le_div_of_nonneg_left hc.le (by norm_num) hH
      _ ≤ 1 / 4 := by simpa using hc4
  change 1 - δ ≤ s.re at hs
  have hgap (ρ : ℂ) (hρ : regularizedZeta ρ = 0) (hρt : |ρ.im| ≤ T + 2) :
      4 * δ ≤ 1 - ρ.re := by
    have hden : 0 < Real.log (|ρ.im| + 2) + 1 := by
      have hh := Real.log_nonneg (show 1 ≤ |ρ.im| + 2 by linarith [abs_nonneg ρ.im])
      linarith
    have hd : Real.log (|ρ.im| + 2) + 1 ≤ H := by
      dsimp [H]
      exact add_le_add (Real.log_le_log (by positivity) (by linarith)) le_rfl
    calc
      4 * δ ≤ c0 / H := by
        dsimp [δ]
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right hcc hHp.le
      _ ≤ c0 / (Real.log (|ρ.im| + 2) + 1) := div_le_div_of_nonneg_left hc0.le hden hd
      _ ≤ 1 - ρ.re := hregion ρ hρ
  have hne : regularizedZeta s ≠ 0 := by
    intro he
    have hh := hgap s he (by linarith)
    linarith
  refine ⟨hne, ?_⟩
  let w : ℂ := s - characterZeroCenter s.im
  have hwval : w = ((s.re - 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [w, characterZeroCenter]
  have hw : ‖w‖ ≤ 5 / 4 := by
    rw [hwval, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hf : zetaAtHeight s.im w ≠ 0 := by
    simpa only [zetaAtHeight, w, sub_add_cancel] using hne
  have hsep (z : ℂ) (hz : z ∈ zetaDiskZeros s.im) : δ ≤ ‖w - z‖ := by
    have hzero : regularizedZeta (z + characterZeroCenter s.im) = 0 :=
      ((mem_zetaDiskZeros s.im z).mp hz).2
    have hzi := Complex.abs_im_le_norm z
    have hzn := ((mem_zetaDiskZeros s.im z).mp hz).1
    have htri := abs_add_le z.im s.im
    have hzt : |(z + characterZeroCenter s.im).im| ≤ T + 2 := by
      simp only [Complex.add_im, characterZeroCenter_im]
      linarith
    have hh := hgap (z + characterZeroCenter s.im) hzero hzt
    have hre : δ ≤ (w - z).re := by
      rw [hwval]
      simp only [Complex.sub_re, Complex.ofReal_re]
      simp only [Complex.add_re, characterZeroCenter_re] at hh
      linarith
    exact hre.trans (Complex.re_le_norm _)
  have hb := hbound s.im w δ hw hf hδ hsep
  rw [zetaAtHeight_logDeriv_translate, show w + characterZeroCenter s.im = s by
    dsimp [w]; abel] at hb
  have hlog : Real.log (|s.im| + 2) ≤ H := by
    have hh : Real.log (|s.im| + 2) ≤ Real.log (T + 4) :=
      Real.log_le_log (by positivity) (by linarith)
    dsimp [H]
    linarith
  have hcost : 1 + δ⁻¹ ≤ H * (1 + c⁻¹) := by
    have he : δ⁻¹ = H * c⁻¹ := by dsimp [δ]; rw [inv_div]; ring
    rw [he]
    nlinarith
  calc
    _ ≤ B * H * (H * (1 + c⁻¹)) := hb.trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hlog hB.le) hcost (by positivity) (by positivity))
    _ = _ := by dsimp [H]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrincipalRieszSupply
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A quantitative principal Riesz estimate with no prime-distribution input -/

namespace Ostmann

open Complex Set
open scoped Interval

theorem principal_riesz_general_bound : ∃ c A B E : ℝ,
    0 < c ∧ c ≤ 1 / 4 ∧ 0 < A ∧ 0 < B ∧ 0 < E ∧
    ∀ T X b : ℝ, 2 ≤ T → 1 ≤ X → 1 < b → b ≤ 2 →
      let H := Real.log (T + 4) + 1
      ‖principalRieszMean X - (X / 2 : ℝ)‖ ≤
        A * H ^ 2 * X ^ (1 - c / H) + B * H ^ 2 * X ^ b / T ^ 2 +
          2 * (1 / (b - 1) + E) * X ^ b / T := by
  obtain ⟨c, M0, hc, hc4, hM0, hdata⟩ := zeta_zero_free_logDeriv_data
  obtain ⟨K, E, hK, hE, hrect⟩ := principalRieszMean_rectangle_bound
  refine ⟨c, K * (M0 + c⁻¹), 4 * (M0 + 1), E, hc, hc4,
    by positivity, by positivity, hE, ?_⟩
  intro T X b hT hX hb hb2
  dsimp only
  let H := Real.log (T + 4) + 1
  let a := 1 - c / H
  have hH : 1 ≤ H := by
    have hh := Real.log_nonneg (show 1 ≤ T + 4 by linarith)
    dsimp [H]
    linarith
  have hHp : 0 < H := by linarith
  have hfrac : 0 < c / H := div_pos hc hHp
  have hfrac4 : c / H ≤ 1 / 4 := by
    calc
      c / H ≤ c / 1 := div_le_div_of_nonneg_left hc.le (by norm_num) hH
      _ ≤ 1 / 4 := by simpa using hc4
  have ha : 1 / 2 ≤ a := by dsimp [a]; linarith
  have ha1 : a < 1 := by dsimp [a]; linarith
  have hab : a ≤ b := by linarith
  have hpoint (s : ℂ) (hs : s ∈ uIcc a b ×ℂ uIcc (-T) T) :
      regularizedZeta s ≠ 0 ∧ ‖logDeriv regularizedZeta s‖ ≤ M0 * H ^ 2 := by
    have hre : a ≤ s.re ∧ s.re ≤ b := by simpa [uIcc_of_le hab] using hs.1
    have him : -T ≤ s.im ∧ s.im ≤ T := by
      simpa [uIcc_of_le (show -T ≤ T by linarith)] using hs.2
    exact hdata T hT s hre.1 (hre.2.trans hb2) (abs_le.mpr him)
  have hh := hrect X a b T (M0 * H ^ 2) hX ha ha1 hb hb2 (by linarith) (by positivity)
    (fun s hs => (hpoint s hs).1) (fun s hs => (hpoint s hs).2)
  have hinv : 1 / (1 - a) = H * c⁻¹ := by
    dsimp [a]
    rw [show 1 - (1 - c / H) = c / H by ring, one_div, inv_div]
    ring
  have hlow : M0 * H ^ 2 + 1 / (1 - a) ≤ (M0 + c⁻¹) * H ^ 2 := by
    rw [hinv]
    have hh := mul_nonneg (inv_nonneg.mpr hc.le) (show 0 ≤ H ^ 2 - H by nlinarith)
    nlinarith
  have hhigh : M0 * H ^ 2 + 1 / T ≤ (M0 + 1) * H ^ 2 := by
    have hi : 1 / T ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    nlinarith
  have hlength : b - a ≤ 2 := by linarith
  have hfirst := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlow hK.le)
    (Real.rpow_nonneg (by linarith : 0 ≤ X) a)
  have hsecond : 2 * ((M0 * H ^ 2 + 1 / T) * X ^ b / T ^ 2) * (b - a) ≤
      4 * (M0 + 1) * H ^ 2 * X ^ b / T ^ 2 := by
    have hmult := mul_le_mul_of_nonneg_right hhigh
      (show 0 ≤ X ^ b / T ^ 2 by positivity)
    have hprod := mul_le_mul hmult hlength (sub_nonneg.mpr hab)
      (show 0 ≤ (M0 + 1) * H ^ 2 * (X ^ b / T ^ 2) by positivity)
    first | (convert mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring) | exact (le_of_eq (by ring)).trans ((mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 2)).trans (le_of_eq (by ring)))
  have hfirst' : K * (M0 * H ^ 2 + 1 / (1 - a)) * X ^ a ≤
      (K * (M0 + c⁻¹)) * H ^ 2 * X ^ a := by
    convert hfirst using 1
    all_goals try with_reducible_and_instances rfl
    ring
  calc
    _ ≤ K * (M0 * H ^ 2 + 1 / (1 - a)) * X ^ a +
        2 * ((M0 * H ^ 2 + 1 / T) * X ^ b / T ^ 2) * (b - a) +
        2 * (1 / (b - 1) + E) * X ^ b / T := hh
    _ ≤ (K * (M0 + c⁻¹)) * H ^ 2 * X ^ a +
        4 * (M0 + 1) * H ^ 2 * X ^ b / T ^ 2 +
        2 * (1 / (b - 1) + E) * X ^ b / T := by linarith
    _ = _ := rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrincipalRieszDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential decay of the principal Riesz error -/

namespace Ostmann

open Filter

theorem principal_riesz_decay : ∃ d : ℝ, 0 < d ∧ ∀ᶠ y : ℝ in atTop,
    ‖principalRieszMean (Real.exp (y ^ 2)) - (Real.exp (y ^ 2) / 2 : ℝ)‖ ≤
      3 * Real.exp (y ^ 2 - d * y) := by
  obtain ⟨c, A, B, E, hc, hc4, hA, hB, hE, hbound⟩ := principal_riesz_general_bound
  refine ⟨c / 6, by positivity, ?_⟩
  filter_upwards [riesz_exponential_error c A B E hc hc4 hA.le hB.le hE.le,
    eventually_ge_atTop (5 : ℝ)] with y hy hy5
  have hy0 : 0 < y := by linarith
  have hT : 2 ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  have hb1 : 1 < 1 + 1 / y ^ 2 := by
    have hh : 0 < 1 / y ^ 2 := by positivity
    linarith
  have hb2 : 1 + 1 / y ^ 2 ≤ 2 := by
    have hys : 1 ≤ y ^ 2 := by nlinarith
    have hh : 1 / y ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr hys
    linarith
  have hh := hbound (Real.exp y) (Real.exp (y ^ 2)) (1 + 1 / y ^ 2) hT
    (Real.one_le_exp (sq_nonneg y)) hb1 hb2
  obtain ⟨hH, hHy⟩ := principal_riesz_height_log_bound y hy5
  exact hh.trans (hy _ hH hHy)

theorem principal_riesz_sqrt_decay : ∃ d : ℝ, 0 < d ∧ ∀ᶠ X : ℝ in atTop,
    ‖principalRieszMean X - (X / 2 : ℝ)‖ ≤
      3 * X * Real.exp (-d * Real.sqrt (Real.log X)) := by
  obtain ⟨d, hd, h⟩ := principal_riesz_decay
  refine ⟨d, hd, ?_⟩
  have ht := Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually h, eventually_ge_atTop (1 : ℝ)] with X hX hX1
  have hx : 0 < X := by linarith
  have heq : Real.exp ((Real.sqrt (Real.log X)) ^ 2) = X := by
    rw [Real.sq_sqrt (Real.log_nonneg hX1), Real.exp_log hx]
  dsimp only [Function.comp_apply] at hX
  rw [heq, Real.exp_sub, Real.sq_sqrt (Real.log_nonneg hX1), Real.exp_log hx] at hX
  simpa only [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, neg_mul] using hX

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_InducedCharacterRieszDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform Riesz estimates for all characters at the ambient modulus -/

namespace Ostmann

open Filter

theorem induced_character_riesz_decay : ∃ d : ℝ, 0 < d ∧
    ∀ᶠ X : ℝ in atTop, ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.exp (Real.sqrt (Real.log X)) →
      ∀ [NeZero q] (χ : DirichletCharacter ℂ q),
        ‖rieszTwistMean (fun n => χ (n : ZMod q)) X -
            reducedRieszMain q (primitiveCharacterReduction χ) X‖ ≤
          4 * X * Real.exp (-d * Real.sqrt (Real.log X)) := by
  obtain ⟨dp, hdp, hp⟩ := principal_riesz_sqrt_decay
  obtain ⟨dc, hdc, hc⟩ := character_riesz_canonical_sqrt_decay
  let d := min dp dc
  have hd : 0 < d := lt_min hdp hdc
  refine ⟨d, hd, ?_⟩
  filter_upwards [hp, hc, primitive_riesz_error_decay d hd,
    eventually_ge_atTop (1 : ℝ)] with X hprincipal hcharacter herror hX
  intro q hq hqX inst χ
  have hXp : 0 < X := by linarith
  have hdec (D : ℝ) (hD : d ≤ D) :
      3 * X * Real.exp (-D * Real.sqrt (Real.log X)) ≤
        3 * X * Real.exp (-d * Real.sqrt (Real.log X)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith [Real.sqrt_nonneg (Real.log X)]
  have hr : ‖reducedRieszMean (primitiveCharacterReduction χ) X -
      reducedRieszMain q (primitiveCharacterReduction χ) X‖ ≤
      3 * X * Real.exp (-d * Real.sqrt (Real.log X)) := by
    cases he : primitiveCharacterReduction χ with
    | none =>
      exact hprincipal.trans (hdec dp (min_le_left _ _))
    | some ρ =>
      exact (hcharacter q hq hqX ρ (primitiveReduction_divides χ ρ he)).trans
        (hdec dc (min_le_right _ _))
  have he := (rieszTwistMean_primitive_comparison χ X hX).trans (herror q hqX)
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (rieszTwistMean (fun n => χ (n : ZMod q)) X)
    (reducedRieszMean (primitiveCharacterReduction χ) X)
    (reducedRieszMain q (primitiveCharacterReduction χ) X)
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszResidueError
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing uniform character errors to a single residue class -/

namespace Ostmann

open Complex Filter
open scoped BigOperators

theorem rieszResidueMean_reduced_error : ∃ d : ℝ, 0 < d ∧
    ∀ᶠ X : ℝ in atTop, ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.exp (Real.sqrt (Real.log X)) →
      ∀ [NeZero q] (a : ZMod q), IsUnit a →
        ‖rieszResidueMean q a X - (q.totient : ℂ)⁻¹ *
            ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ *
              reducedRieszMain q (primitiveCharacterReduction χ) X‖ ≤
          4 * X * Real.exp (-d * Real.sqrt (Real.log X)) := by
  obtain ⟨d, hd, h⟩ := induced_character_riesz_decay
  refine ⟨d, hd, ?_⟩
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with X hX hX1
  intro q hq hqX inst a ha
  exact rieszResidueMean_average_error_bound q a ha X _ (by positivity) _ (hX q hq hqX)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszCanonicalResidueMain
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The canonical Page correction in the actual residue-class Riesz mean -/

namespace Ostmann

open Complex Filter
open scoped BigOperators

theorem canonical_riesz_residue_decay : ∃ d : ℝ, 0 < d ∧
    ∀ᶠ X : ℝ in atTop, ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.exp (Real.sqrt (Real.log X)) →
      ∀ [NeZero q] (a : ℕ), a.Coprime q →
        ‖rieszResidueMean q (a : ZMod q) X - (q.totient : ℂ)⁻¹ *
            ((X / 2 : ℝ) - (pageCoefficient (actualLocalZero q) a : ℂ) *
              rieszContourWeight X (pageBeta (actualLocalZero q) : ℂ))‖ ≤
          4 * X * Real.exp (-d * Real.sqrt (Real.log X)) := by
  obtain ⟨d, hd, h⟩ := rieszResidueMean_reduced_error
  refine ⟨d, hd, ?_⟩
  filter_upwards [h] with X hX
  intro q hq hqX inst a ha
  have hh := hX q hq hqX (a : ZMod q) ((ZMod.isUnit_iff_coprime a q).mpr ha)
  rwa [rieszCharacterMainSum_canonical q a ha X] at hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ResidueRieszFinite
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact real finite sums underlying the residue-class contour -/

namespace Ostmann

open Complex
open scoped BigOperators

theorem residueRieszMean_finite_error (q a N : ℕ) (X : ℝ) (hX : 0 < X) (hXN : X ≤ N) :
    |finiteRieszSum (Finset.range (N + 1)) (residueMangoldtWeight q a) X -
        integratedThetaMain q.totient (pageCoefficient (actualLocalZero q) a)
          (pageBeta (actualLocalZero q)) X| =
      X * ‖rieszResidueMean q (a : ZMod q) X - (q.totient : ℂ)⁻¹ *
        ((X / 2 : ℝ) - (pageCoefficient (actualLocalZero q) a : ℂ) *
          rieszContourWeight X (pageBeta (actualLocalZero q) : ℂ))‖ := by
  have he : ((finiteRieszSum (Finset.range (N + 1)) (residueMangoldtWeight q a) X -
      integratedThetaMain q.totient (pageCoefficient (actualLocalZero q) a)
        (pageBeta (actualLocalZero q)) X : ℝ) : ℂ) =
      (X : ℂ) * (rieszResidueMean q (a : ZMod q) X - (q.totient : ℂ)⁻¹ *
        ((X / 2 : ℝ) - (pageCoefficient (actualLocalZero q) a : ℂ) *
          rieszContourWeight X (pageBeta (actualLocalZero q) : ℂ))) := by
    have hs := riesz_residue_main_scale (q.totient : ℝ)
      (pageCoefficient (actualLocalZero q) a) (pageBeta (actualLocalZero q)) X hX
    simp only [Complex.ofReal_natCast] at hs
    rw [mul_sub, rieszResidueMean_finite q a N X hX hXN, hs, Complex.ofReal_sub]
  rw [← Real.norm_eq_abs, ← Complex.norm_real, he, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hX]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ResiduePsiSmallModulus
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sharp residue-class Mangoldt sums for the small-modulus range -/

namespace Ostmann

open Filter

theorem residuePsi_small_modulus_bound : ∃ c : ℝ, 0 < c ∧
    ∀ᶠ X : ℝ in atTop, ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.exp (Real.sqrt (Real.log X) / 2) →
      ∀ a : ℕ, a.Coprime q →
        |residuePsi q a X - thetaMainTerm q.totient
          (pageCoefficient (actualLocalZero q) a) (pageBeta (actualLocalZero q)) X| ≤
            35 * X * Real.exp (-c * Real.sqrt (Real.log X)) := by
  obtain ⟨d, hd, hdecay⟩ := canonical_riesz_residue_decay
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp hdecay
  refine ⟨d / 4, by positivity, ?_⟩
  have ht := Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  filter_upwards [eventually_ge_atTop (max 4 (2 * X0)),
    ht.eventually (eventually_ge_atTop ((4 / d) * Real.log 2))] with X hXL hscale
  intro q hq hqX a ha
  let : NeZero q := ⟨by omega⟩
  have hX : 4 ≤ X := (le_max_left _ _).trans hXL
  have hXX0 : 2 * X0 ≤ X := (le_max_right _ _).trans hXL
  have hXp : 0 < X := by linarith
  dsimp only [Function.comp_apply] at hscale
  let y := Real.sqrt (Real.log X)
  let h := X * Real.exp (-(d / 4) * y)
  let E := 16 * X ^ 2 * Real.exp (-(d / 2) * y)
  let N := ⌈2 * X⌉₊
  let w := residueMangoldtWeight q a
  let F := integratedThetaMain q.totient (pageCoefficient (actualLocalZero q) a)
    (pageBeta (actualLocalZero q))
  let m := thetaMainTerm q.totient (pageCoefficient (actualLocalZero q) a)
    (pageBeta (actualLocalZero q)) X
  have hN : 2 * X ≤ (N : ℝ) := Nat.le_ceil _
  have hh : 0 < h := by dsimp [h]; positivity
  have hlog : Real.log 2 ≤ (d / 4) * y := by
    have hm := mul_le_mul_of_nonneg_left hscale (show 0 ≤ d / 4 by positivity)
    have he : (d / 4) * ((4 / d) * Real.log 2) = Real.log 2 := by field_simp
    rw [he] at hm
    exact hm
  have hexphalf : Real.exp (-(d / 4) * y) ≤ 1 / 2 := by
    calc
      _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hhalf : h ≤ X / 2 := by
    have hm := mul_le_mul_of_nonneg_left hexphalf hXp.le
    dsimp [h]
    linarith
  have herr (Y : ℝ) (hlo : X / 2 ≤ Y) (hhi : Y ≤ 2 * X) :
      |finiteRieszSum (Finset.range (N + 1)) w Y - F Y| ≤ E := by
    have hYp : 0 < Y := by linarith
    have hroot := sqrt_log_nearby_lower X Y hX hlo
    have hqY : (q : ℝ) ≤ Real.exp (Real.sqrt (Real.log Y)) :=
      hqX.trans (Real.exp_le_exp.mpr hroot)
    have hraw := hX0 Y (by linarith) q hq hqY a ha
    have he : Real.exp (-d * Real.sqrt (Real.log Y)) ≤
        Real.exp (-(d / 2) * y) := Real.exp_le_exp.mpr (by dsimp [y]; nlinarith)
    change |finiteRieszSum (Finset.range (N + 1)) (residueMangoldtWeight q a) Y -
      integratedThetaMain q.totient (pageCoefficient (actualLocalZero q) a)
        (pageBeta (actualLocalZero q)) Y| ≤ E
    rw [residueRieszMean_finite_error q a N Y hYp (hhi.trans hN)]
    calc
      _ ≤ Y * (4 * Y * Real.exp (-d * Real.sqrt (Real.log Y))) :=
        mul_le_mul_of_nonneg_left hraw hYp.le
      _ = 4 * Y ^ 2 * Real.exp (-d * Real.sqrt (Real.log Y)) := by ring
      _ ≤ 16 * X ^ 2 * Real.exp (-(d / 2) * y) := by
        apply mul_le_mul _ he (Real.exp_nonneg _) (by positivity)
        nlinarith
  have hφ : (1 : ℝ) ≤ q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < q by omega)
  have hmain := integratedThetaMain_remainder_pair (q.totient : ℝ)
    (pageCoefficient (actualLocalZero q) a) (pageBeta (actualLocalZero q)) X h
    hφ (pageCoefficient_abs_le_one _ _) (pageBeta_pos _) (pageBeta_le_one _) hh (by linarith)
  have hrec := finiteRieszSum_smooth_recovery (Finset.range (N + 1)) w F X h m E hh
    (fun n _ => residueMangoldtWeight_nonneg q a n)
    (herr X (by linarith) (by linarith))
    (herr (X + h) (by linarith) (by linarith))
    (herr (X - h) (by linarith) (by linarith)) hmain.1 hmain.2
  change |(∑ n ∈ (Finset.range (N + 1)).filter (fun n : ℕ => (n : ℝ) ≤ X),
    residueMangoldtWeight q a n) - m| ≤ _ at hrec
  rw [residue_finite_count q a N X hXp.le (by linarith)] at hrec
  have hexp2 : Real.exp (-(d / 2) * y) = (Real.exp (-(d / 4) * y)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hE : E = 16 * h ^ 2 := by
    dsimp [E, h]
    rw [hexp2]
    ring
  have hratio : 2 * E / h = 32 * h := by
    rw [hE]
    field_simp
    ring
  have hfinal : |residuePsi q a X - m| ≤ 35 * h := by
    rw [hratio] at hrec
    linarith
  simpa only [m, h, y, mul_assoc] using hfinal

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ResiduePsiEstimate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform sharp Mangoldt estimate with the canonical Page term -/

namespace Ostmann

open Filter

theorem residuePsi_eventual_bound : ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
    ∀ᶠ X : ℝ in atTop, ∀ q : ℕ, 1 ≤ q → ∀ a : ℕ, a.Coprime q →
      |residuePsi q a X - thetaMainTerm q.totient
        (pageCoefficient (actualLocalZero q) a) (pageBeta (actualLocalZero q)) X| ≤
          C * X * Real.exp (-c * Real.sqrt (Real.log X)) := by
  obtain ⟨d, hd, hsmall⟩ := residuePsi_small_modulus_bound
  obtain ⟨D, hD, hlarge⟩ := residuePsi_large_modulus_bound
  let c := min d (1 / 4)
  refine ⟨c, 35 + D, lt_min hd (by norm_num), by positivity, ?_⟩
  filter_upwards [hsmall, hlarge, eventually_ge_atTop (1 : ℝ)] with X hs hl hX
  intro q hq a ha
  have hc : 0 ≤ Real.sqrt (Real.log X) := Real.sqrt_nonneg _
  have hexp1 : Real.exp (-d * Real.sqrt (Real.log X)) ≤
      Real.exp (-c * Real.sqrt (Real.log X)) :=
    Real.exp_le_exp.mpr (by dsimp [c]; nlinarith [min_le_left d (1 / 4)])
  have hexp2 : Real.exp (-(1 / 4 : ℝ) * Real.sqrt (Real.log X)) ≤
      Real.exp (-c * Real.sqrt (Real.log X)) :=
    Real.exp_le_exp.mpr (by dsimp [c]; nlinarith [min_le_right d (1 / 4)])
  by_cases hqX : (q : ℝ) ≤ Real.exp (Real.sqrt (Real.log X) / 2)
  · exact (hs q hq hqX a ha).trans (by
      have hm := mul_le_mul_of_nonneg_left hexp1 (show 0 ≤ 35 * X by positivity)
      exact hm.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) (by linarith : 0 ≤ X))
          (Real.exp_nonneg _)))
  · exact (hl q (by omega) (le_of_not_ge hqX) a).trans (by
      have hm := mul_le_mul_of_nonneg_left hexp2 (show 0 ≤ D * X by positivity)
      exact hm.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) (by linarith : 0 ≤ X))
          (Real.exp_nonneg _)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ActualThetaEstimate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual prime-progression estimate, with no analytic input hypotheses -/

namespace Ostmann

open Filter

theorem actual_theta_eventual_bound : ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
    ∀ᶠ X : ℝ in atTop, ∀ q : ℕ, 1 ≤ q → ∀ a : ℕ, a.Coprime q →
      |primeProgressionTheta q a X - thetaMainTerm q.totient
        (pageCoefficient (actualLocalZero q) a) (pageBeta (actualLocalZero q)) X| ≤
          C * X * Real.exp (-c * Real.sqrt (Real.log X)) := by
  obtain ⟨c, C, hc, hC, hbound⟩ := residuePsi_eventual_bound
  refine ⟨c, C + 1, hc, by positivity, ?_⟩
  filter_upwards [hbound, primitive_riesz_error_decay c hc,
    eventually_ge_atTop (1 : ℝ)] with X hmain herr hX
  intro q hq a ha
  have hp := residuePsi_prime_error q a X hX
  have he := herr 0 (by simpa using (Real.exp_nonneg (Real.sqrt (Real.log X))))
  norm_num only [Nat.cast_zero, mul_zero, zero_mul, zero_add] at he
  have hs : 0 ≤ Real.sqrt X * Real.log X :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg hX)
  have htri := abs_sub_le (primeProgressionTheta q a X) (residuePsi q a X)
    (thetaMainTerm q.totient (pageCoefficient (actualLocalZero q) a)
      (pageBeta (actualLocalZero q)) X)
  rw [abs_sub_comm (primeProgressionTheta q a X) (residuePsi q a X)] at htri
  have hm := hmain q hq a ha
  nlinarith

/-- Montgomery--Vaughan's progression estimate specialized to the canonical,
actually constructed exceptional zero. All inputs have been discharged. -/
theorem actualProgressionTheta : ActualProgressionTheta := by
  obtain ⟨c, C, hc, hC, hbound⟩ := actual_theta_eventual_bound
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp hbound
  obtain ⟨D, hD, hsmall⟩ := actual_theta_bounded_range
  let L := max 2 X0
  let K := 2 * Real.log L + D
  let B := C + K * Real.exp (c * Real.sqrt (Real.log L))
  have hL : 2 ≤ L := le_max_left _ _
  have hK : 0 ≤ K := by
    have hl : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
    dsimp [K]
    positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨c, B, hc, hB, ?_⟩
  intro q hq a ha X hX
  have hXp : 0 ≤ X := by linarith
  by_cases hlarge : X0 ≤ X
  · exact (hX0 X hlarge q hq a ha).trans (by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      apply mul_le_mul_of_nonneg_right _ hXp
      exact le_add_of_nonneg_right (mul_nonneg hK (Real.exp_nonneg _)))
  · have hXL : X ≤ L := (le_of_not_ge hlarge).trans (le_max_right _ _)
    have hsmall' := hsmall q a X L hq (by linarith) hXL
    have hy : Real.sqrt (Real.log X) ≤ Real.sqrt (Real.log L) :=
      Real.sqrt_le_sqrt (Real.log_le_log (by linarith) hXL)
    have he : 1 ≤ Real.exp (c * Real.sqrt (Real.log L)) *
        Real.exp (-c * Real.sqrt (Real.log X)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    have hrate : K ≤ B * Real.exp (-c * Real.sqrt (Real.log X)) := by
      calc
        K = K * 1 := (mul_one _).symm
        _ ≤ K * (Real.exp (c * Real.sqrt (Real.log L)) *
            Real.exp (-c * Real.sqrt (Real.log X))) := mul_le_mul_of_nonneg_left he hK
        _ = (K * Real.exp (c * Real.sqrt (Real.log L))) *
            Real.exp (-c * Real.sqrt (Real.log X)) := (mul_assoc _ _ _).symm
        _ ≤ B * Real.exp (-c * Real.sqrt (Real.log X)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
          dsimp [B]
          linarith
    exact hsmall'.trans (by
      have hh := mul_le_mul_of_nonneg_right hrate hXp
      simpa only [K, mul_right_comm] using hh)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_MainWithoutProgression
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The main statements after discharging the prime-progression input -/

namespace Ostmann

noncomputable def actualProgressionInput : PublishedProgressionInput :=
  progressionInput_of_actual_theta actualProgressionTheta

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityCharacterFamily
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Grouping the actual primitive characters by their conductors -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators Classical

noncomputable def densityCharacterFamily (F : Finset PrimitiveComplexCharacter) (q : ℕ) :
    Finset (DirichletCharacter ℂ q) :=
  ((F.filter fun χ => χ.modulus = q).attach).image fun χ =>
    χ.val.atModulus q (Finset.mem_filter.mp χ.property).2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityZeroBins
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual zero indices, unit ordinate bins and separated representatives -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def densityZeroIndices (F : Finset PrimitiveComplexCharacter) (σ T : ℝ) :
    Finset DensityZeroIndex :=
  F.sigma fun χ => ((actualCharacterZeros χ).heightIndices T).filter
    (fun i => σ ≤ ((actualCharacterZeros χ).zeros i).re)

noncomputable def densityZeroBin (i : DensityZeroIndex) : DensityZeroBin :=
  ⟨i.1, ⌊((actualCharacterZeros i.1).zeros i.2).im⌋⟩

end Ostmann

end OAI
end


