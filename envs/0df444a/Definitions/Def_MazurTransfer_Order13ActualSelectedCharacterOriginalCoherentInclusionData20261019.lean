-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualSelectedCharacterOriginalCoherentInclusionData20261019
-- name    : MazurTransfer_Order13ActualSelectedCharacterOriginalCoherentInclusionData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T02:54:33.830254+00:00
-- url     : https://prove2.me/theorems/67992876-1473-46f6-9349-39dbefd924ff
-- title:
--   Original coherent character inclusions for the specified norm quotients
-- statement:
--   The original character inclusions selected for the previously chosen actual norm quotient maps. Both inclusions are injective and their ranges are exactly the respective specified quotient kernels. Eight original declaration types, both whole chosen inclusion values, the finite-dimension provider type, and the original chosen quotient context are checked. The named downstream consumer is actual selected character Kummer kernel control.
-- source:
--   MazurTheorem Order13ActualSelectedCharacterExactSequences; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: keep BOTH previously selected actual character quotient
intertwiners and construct character inclusions with ranges EXACTLY their
kernels. No independently selected quotient replaces either original map.
Named downstream consumer: actual continuous-H1 character kernel control
for the norm Kummer maps and their numerical norm quotient estimates.
-/
import Definitions.Def_MazurTransfer_Order13ActualOrderedCharacterContinuousH1OriginalChosenQuotientsAndKummerDataFixedKernelActionsAndContinuousNamespacesV320261019
import Theorems.Thm_MazurTransfer_OneDimensionalSelectedQuotientKernel_exists_injective_with_selected_kernel
import Theorems.Thm_MazurTransfer_order13_actual_ordered_arithmetic_character_sequence_certificates
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve MazurTransfer
open NeronModelInfra GoodReductionJacobian
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelCyclotomicCharacter Order13ActualNormKernelCyclotomicQuotient
open Order13ActualNormKernelF19Representation NineteenRootsGaloisRepresentation
open Order13ActualNineteenTorsionNormPairingAdjoint Order13ActualNormKernelProductCardinality
open Order13ActualNormKernelNineteenEmbedding
open scoped CategoryTheory.MonObj
attribute [local instance] kernelCharacterOriginalGroupProvider20261018 kernelCharacterOriginalCommProvider20261018 kernelCharacterOriginalPiHomProvider20261018 kernelCharacterOriginalConjugateHomProvider20261018 kernelCharacterOriginalPrimeProvider20261018 kernelCharacterOriginalLeftModuleProvider20261018 kernelCharacterOriginalRightModuleProvider20261018 kernelCharacterOriginalRootsModuleProvider20261018 kernelNineteenEmbeddingOriginalFiniteProvider20261018

open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualNormKernelRanksTwo
open Order13ActualPicardSchemeNineteenNorm
attribute [local instance] originalNormKernelRanksTwoPiFiniteProvider20261018 originalNormKernelRanksTwoConjugateFiniteProvider20261018 originalNormKernelRanksTwoPiExponentProvider20261018 originalNormKernelRanksTwoConjugateExponentProvider20261018 originalNormKernelRanksTwoPiModuleProvider20261018 originalNormKernelRanksTwoConjugateModuleProvider20261018


open Order13ReflectionParameter Order13ActualNormKernelReflection
open Order13ActualReflectionPairingOrthogonality Order13ActualGeometricNineteenDivisorialPairing
open Order13ReflectionSexticSymmetry Order13ActualReflectionCoefficientCovariance Order13CyclotomicReflectionCoefficients
open Order13ActualNineteenTorsionReflection Order13ActualGeometricNineteenTorsionDiamondComparison
open MazurTransfer.ThirteenToNineteenCharacters MazurTransfer.Order13ActualCyclotomicThirteenKernelCharacter
attribute [local instance] characterOriginalPrime13Provider20261018 characterOriginalPrime19Provider20261018
open MazurTransfer.Order13ActualArithmeticCharacterExactSequence MazurTransfer.ScalarCharacterLine
open Order13ActualComplementaryCharacterExactSequence Order13ActualNormKernelEigenCharacterQuotient RepresentationCharacterTwist
open Order13ActualNormKernelCrossPairing
open Order13ActualNormKernelInvariantDimensions
open Order13ActualNormCharacterH1Exactness Order13ActualNormCharacterKummerKernelControl
open RepresentationCharacterTwist ScalarCharacterLine Order13ActualPicardGeometricNormPreimages
attribute [local instance] sourceArithmeticExactSequenceRationalFactProvider20261018 originalNormKernelRanksTwoPiKernelFiniteProvider20261018 originalNormKernelRanksTwoConjugateKernelFiniteProvider20261018
attribute [local instance] MazurTransfer.Order13ActualNormCharacterH1Exactness.actualNormCharacterH1ExactnessDataProvider520261018 MazurTransfer.Order13ActualNormCharacterH1Exactness.actualNormCharacterH1ExactnessDataProvider620261018 MazurTransfer.Order13ActualNormCharacterH1Exactness.actualNormCharacterH1ExactnessDataProvider720261018 MazurTransfer.Order13ActualNormCharacterH1Exactness.actualNormCharacterH1ExactnessDataProvider820261018
open Order13ActualNormCharacterContinuousH1 Order13ActualNormCharacterKummerUnramified
open RepresentationDiscreteCoefficients ContinuousCoefficientExponentAndContinuity
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormAlgebraicKummerInjection
open Order13ActualOrderedCharacterContinuousH1
attribute [local instance] Order13ActualOrderedCharacterContinuousH1.orderedContinuousOriginalPiKernelActionProvider20261019 Order13ActualOrderedCharacterContinuousH1.orderedContinuousOriginalConjugateKernelActionProvider20261019
open OneDimensionalSelectedQuotientKernel
namespace MazurTransfer.Order13ActualSelectedCharacterExactSequences
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
local instance selectedCharacterOriginalRootsFiniteDimProvider20261019 : FiniteDimensional (ZMod 19) (Additive (Roots K)) := FiniteDimensional.of_finrank_pos (by rw [roots_finrank_one K]; decide)
variable (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover)
theorem exists_pi_selected_kernel_inclusion :
    ∃ i : Representation.IntertwiningMap
        (ScalarCharacterLine.scalarRepresentation (piConjugateReflectedCharacter K z hz))
        (kernelRepresentation K schemePi),
      Function.Injective i ∧ LinearMap.range i.toLinearMap = LinearMap.ker (piQuotient K z hz 𝒱).toLinearMap := by
  obtain ⟨i, q, hi, hq, hker⟩ :=
    ((MazurTransfer.order13_actual_ordered_arithmetic_character_sequence_certificates).1 K z hz 𝒱).1
  exact exists_injective_with_selected_kernel _ _ _ (roots_finrank_one K)
    i q hi hq hker (piQuotient K z hz 𝒱) (piQuotient_surjective K z hz 𝒱)

theorem exists_piConjugate_selected_kernel_inclusion :
    ∃ i : Representation.IntertwiningMap
        (Representation.trivial (ZMod 19) (K ≃ₐ[ℚ] K) (ZMod 19))
        (kernelRepresentation K schemePiConjugate),
      Function.Injective i ∧
        LinearMap.range i.toLinearMap = LinearMap.ker (piConjugateQuotient K z hz 𝒱).toLinearMap := by
  obtain ⟨i, q, hi, hq, hker⟩ :=
    ((MazurTransfer.order13_actual_ordered_arithmetic_character_sequence_certificates).1 K z hz 𝒱).2
  exact exists_injective_with_selected_kernel _ _ _ (roots_finrank_one K)
    i q hi hq hker (piConjugateQuotient K z hz 𝒱) (piConjugateQuotient_surjective K z hz 𝒱)

def selectedPiInclusion : Representation.IntertwiningMap
    (ScalarCharacterLine.scalarRepresentation (piConjugateReflectedCharacter K z hz))
    (kernelRepresentation K schemePi) :=
  Classical.choose (exists_pi_selected_kernel_inclusion K z hz 𝒱)

theorem selectedPiInclusion_injective : Function.Injective (selectedPiInclusion K z hz 𝒱) :=
  (Classical.choose_spec (exists_pi_selected_kernel_inclusion K z hz 𝒱)).1

theorem selectedPiInclusion_range :
    LinearMap.range (selectedPiInclusion K z hz 𝒱).toLinearMap =
      LinearMap.ker (piQuotient K z hz 𝒱).toLinearMap :=
  (Classical.choose_spec (exists_pi_selected_kernel_inclusion K z hz 𝒱)).2

def selectedPiConjugateInclusion : Representation.IntertwiningMap
    (Representation.trivial (ZMod 19) (K ≃ₐ[ℚ] K) (ZMod 19))
    (kernelRepresentation K schemePiConjugate) :=
  Classical.choose (exists_piConjugate_selected_kernel_inclusion K z hz 𝒱)

theorem selectedPiConjugateInclusion_injective : Function.Injective (selectedPiConjugateInclusion K z hz 𝒱) :=
  (Classical.choose_spec (exists_piConjugate_selected_kernel_inclusion K z hz 𝒱)).1

theorem selectedPiConjugateInclusion_range :
    LinearMap.range (selectedPiConjugateInclusion K z hz 𝒱).toLinearMap =
      LinearMap.ker (piConjugateQuotient K z hz 𝒱).toLinearMap :=
  (Classical.choose_spec (exists_piConjugate_selected_kernel_inclusion K z hz 𝒱)).2

end MazurTransfer.Order13ActualSelectedCharacterExactSequences
#print axioms MazurTransfer.Order13ActualSelectedCharacterExactSequences.exists_pi_selected_kernel_inclusion
#print axioms MazurTransfer.Order13ActualSelectedCharacterExactSequences.exists_piConjugate_selected_kernel_inclusion
#print axioms MazurTransfer.Order13ActualSelectedCharacterExactSequences.selectedPiInclusion
#print axioms MazurTransfer.Order13ActualSelectedCharacterExactSequences.selectedPiInclusion_injective
#print axioms MazurTransfer.Order13ActualSelectedCharacterExactSequences.selectedPiInclusion_range
#print axioms MazurTransfer.Order13ActualSelectedCharacterExactSequences.selectedPiConjugateInclusion
#print axioms MazurTransfer.Order13ActualSelectedCharacterExactSequences.selectedPiConjugateInclusion_injective
#print axioms MazurTransfer.Order13ActualSelectedCharacterExactSequences.selectedPiConjugateInclusion_range


