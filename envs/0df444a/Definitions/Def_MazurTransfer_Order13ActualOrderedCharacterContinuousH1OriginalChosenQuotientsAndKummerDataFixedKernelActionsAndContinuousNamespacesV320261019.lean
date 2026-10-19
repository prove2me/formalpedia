-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualOrderedCharacterContinuousH1OriginalChosenQuotientsAndKummerDataFixedKernelActionsAndContinuousNamespacesV320261019
-- name    : MazurTransfer_Order13ActualOrderedCharacterContinuousH1OriginalChosenQuotientsAndKummerDataFixedKernelActionsAndContinuousNamespacesV320261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T02:03:57.019047+00:00
-- url     : https://prove2.me/theorems/d76f425c-64a4-4f7d-b808-9ee7616d1903
-- title:
--   Original coherently chosen ordered norm quotient and Kummer maps
-- statement:
--   The original chosen surjective quotients of the two actual norm kernels, with literal nineteen-root target for pi and the original inverse-character twist for the conjugate factor. These same choices define both continuous H1 maps and both actual norm Kummer pushforwards. Thirteen original declaration types, seven whole constructor values, both fixed kernel-action provider types and values, and all required contexts have been checked. Named downstream consumers: coherent subgroup restriction and unramified Kummer certificates, exceptional-prime local conditions and Selmer bounds.
-- source:
--   MazurTheorem Order13ActualOrderedCharacterContinuousH1, original chosen quotient, continuous H1 and norm Kummer constructors; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: instantiate the continuous H1 and Kummer pushforwards with
the SAME actual ordered norm quotients: pi to literal mu19, and conjugate pi
to mu19 twisted by chi13 inverse. Named downstream consumer: exceptional-prime
local Kummer conditions and global norm Selmer bounds.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNormKernelReflectionOriginalRestrictedCompleteEquivalencesAndEmbeddingCertificatesExplicitFiniteExponentContextV220261018
import Definitions.Def_MazurTransfer_Order13CyclotomicReflectionParameterOriginalPolynomialDataAndConstructorCertificates20261018
import Definitions.Def_MazurTransfer_Order13ActualCoefficientFunctionFieldActionAndReflectionParameterOriginalDataMinimalPublicNamespacesV220261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelRanksTwoOriginalModuleContextData20261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicQuotientOriginalPredicateData20261018
import Definitions.Def_MazurTransfer_Order13ActualThirteenthCyclotomicReflectedCharacterOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualArithmeticCharacterExactSequenceOriginalPredicateDataExplicitFiniteModuleNamespaceV220261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicCharacterIntertwiningOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualComplementaryCharacterExactSequenceOriginalFixedVectorAndPredicateData20261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelEigenCharacterIntertwiningOriginalDataAndEquivarianceCertificate20261018
import Definitions.Def_MazurTransfer_Order13ActualNormCharacterH1ExactSequenceData
import Definitions.Def_MazurTransfer_Order13ActualNormCharacterKummerKernelControlData
import Theorems.Thm_MazurTransfer_order13_actual_ordered_arithmetic_character_sequence_certificates
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricNormPreimages_schemePi_geometricPoint_surjective
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricNormPreimages_schemePiConjugate_geometricPoint_surjective
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
namespace MazurTransfer.Order13ActualOrderedCharacterContinuousH1
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
local instance orderedContinuousOriginalPiKernelActionProvider20261019 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K schemePi) := kernelAction K schemePi
local instance orderedContinuousOriginalConjugateKernelActionProvider20261019 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K schemePiConjugate) := kernelAction K schemePiConjugate
variable (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover)
abbrev twistedRootsRepresentation := twist (piConjugateReflectedCharacter K z hz)⁻¹ (rootsRepresentation K)

include z hz 𝒱

theorem exists_pi_quotient : ∃ p : Representation.IntertwiningMap
    (kernelRepresentation K schemePi) (rootsRepresentation K), Function.Surjective p := by
  obtain ⟨i, p, hi, hp, hker⟩ := ((MazurTransfer.order13_actual_ordered_arithmetic_character_sequence_certificates).1 K z hz 𝒱).1
  exact ⟨p, hp⟩

theorem exists_piConjugate_quotient : ∃ p : Representation.IntertwiningMap
    (kernelRepresentation K schemePiConjugate) (twistedRootsRepresentation K z hz),
    Function.Surjective p := by
  obtain ⟨i, p, hi, hp, hker⟩ := ((MazurTransfer.order13_actual_ordered_arithmetic_character_sequence_certificates).1 K z hz 𝒱).2
  exact ⟨p, hp⟩

def piQuotient : Representation.IntertwiningMap (kernelRepresentation K schemePi)
    (rootsRepresentation K) := Classical.choose (exists_pi_quotient K z hz 𝒱)
def piConjugateQuotient : Representation.IntertwiningMap (kernelRepresentation K schemePiConjugate)
    (twistedRootsRepresentation K z hz) := Classical.choose (exists_piConjugate_quotient K z hz 𝒱)

theorem piQuotient_surjective : Function.Surjective (piQuotient K z hz 𝒱) :=
  Classical.choose_spec (exists_pi_quotient K z hz 𝒱)
theorem piConjugateQuotient_surjective : Function.Surjective (piConjugateQuotient K z hz 𝒱) :=
  Classical.choose_spec (exists_piConjugate_quotient K z hz 𝒱)

theorem piCoefficient_continuousSMul : ContinuousSMul (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)) :=
  coefficient_continuousSMul K schemePi (rootsRepresentation K) (piQuotient K z hz 𝒱)
    (piQuotient_surjective K z hz 𝒱)
theorem piConjugateCoefficient_continuousSMul :
    ContinuousSMul (K ≃ₐ[ℚ] K) (Coefficient (twistedRootsRepresentation K z hz)) :=
  coefficient_continuousSMul K schemePiConjugate (twistedRootsRepresentation K z hz)
    (piConjugateQuotient K z hz 𝒱) (piConjugateQuotient_surjective K z hz 𝒱)

def piMapClass := mapClass K schemePi (rootsRepresentation K) (piQuotient K z hz 𝒱)
def piConjugateMapClass := mapClass K schemePiConjugate (twistedRootsRepresentation K z hz)
  (piConjugateQuotient K z hz 𝒱)

def piKummerHom := normQuotientCharacterHom K schemePi (rootsRepresentation K) (piQuotient K z hz 𝒱)
  (schemePi_geometricPoint_surjective K)
def piConjugateKummerHom := normQuotientCharacterHom K schemePiConjugate (twistedRootsRepresentation K z hz)
  (piConjugateQuotient K z hz 𝒱) (schemePiConjugate_geometricPoint_surjective K)

end MazurTransfer.Order13ActualOrderedCharacterContinuousH1
#print axioms MazurTransfer.Order13ActualOrderedCharacterContinuousH1.twistedRootsRepresentation
#print axioms MazurTransfer.Order13ActualOrderedCharacterContinuousH1.exists_pi_quotient
#print axioms MazurTransfer.Order13ActualOrderedCharacterContinuousH1.exists_piConjugate_quotient
#print axioms MazurTransfer.Order13ActualOrderedCharacterContinuousH1.piQuotient
#print axioms MazurTransfer.Order13ActualOrderedCharacterContinuousH1.piConjugateQuotient
#print axioms MazurTransfer.Order13ActualOrderedCharacterContinuousH1.piQuotient_surjective
#print axioms MazurTransfer.Order13ActualOrderedCharacterContinuousH1.piConjugateQuotient_surjective
#print axioms MazurTransfer.Order13ActualOrderedCharacterContinuousH1.piCoefficient_continuousSMul
#print axioms MazurTransfer.Order13ActualOrderedCharacterContinuousH1.piConjugateCoefficient_continuousSMul
#print axioms MazurTransfer.Order13ActualOrderedCharacterContinuousH1.piMapClass
#print axioms MazurTransfer.Order13ActualOrderedCharacterContinuousH1.piConjugateMapClass
#print axioms MazurTransfer.Order13ActualOrderedCharacterContinuousH1.piKummerHom
#print axioms MazurTransfer.Order13ActualOrderedCharacterContinuousH1.piConjugateKummerHom


