-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualComplementaryCharacterExactSequenceOriginalFixedVectorAndPredicateData20261018
-- name    : MazurTransfer_Order13ActualComplementaryCharacterExactSequenceOriginalFixedVectorAndPredicateData20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T00:34:57.175131+00:00
-- url     : https://prove2.me/theorems/3ee3088e-fcb8-4de4-a929-c76532c16926
-- title:
--   Original complementary-character fixed-vector map and exact-sequence predicate
-- statement:
--   The original intertwining injection associated to a rational fixed vector and the original complementary exact-sequence predicate with a quotient into the inverse-character twist of literal nineteen roots. Both complete constructor types and whole values, the generic module provider type and value, and all required original contexts are checked. Named downstream consumer: both actual complementary-character exact sequences and their pair with the arithmetic-character sequences. This data interface adds no arithmetic existence proof.
-- source:
--   MazurTheorem Order13ActualComplementaryCharacterExactSequence, original fixedVectorIntertwining and HasComplementaryCharacterExactSequence declarations; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the SAME actual norm factor containing the rational fixed
line is an extension of literal mu19 twisted by chi13 inverse by the trivial
representation. Together with the opposite norm factor's checked sequence,
this identifies both actual arithmetic character exact sequences.
Named downstream consumer: exceptional-prime local Kummer and norm Selmer bounds.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicCharacterOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelRanksTwoOriginalModuleContextData20261018
import Definitions.Def_MazurTransfer_RepresentationCharacterTwistOriginalDataAndActionCertificate20261018
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve MazurTransfer
open NeronModelInfra GoodReductionJacobian
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelCyclotomicCharacter Order13ActualNormKernelFiniteModule
open Order13ActualNormKernelF19Representation NineteenRootsGaloisRepresentation
open Order13ActualNineteenTorsionNormPairingAdjoint Order13ActualNormKernelProductCardinality
open Order13ActualNormKernelNineteenEmbedding
open scoped CategoryTheory.MonObj
attribute [local instance] kernelCharacterOriginalGroupProvider20261018 kernelCharacterOriginalCommProvider20261018 kernelCharacterOriginalPiHomProvider20261018 kernelCharacterOriginalConjugateHomProvider20261018 kernelCharacterOriginalPrimeProvider20261018 kernelCharacterOriginalLeftModuleProvider20261018 kernelCharacterOriginalRightModuleProvider20261018 kernelCharacterOriginalRootsModuleProvider20261018 kernelNineteenEmbeddingOriginalFiniteProvider20261018

open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualNormKernelRanksTwo
open Order13ActualPicardSchemeNineteenNorm
attribute [local instance] originalNormKernelRanksTwoPiFiniteProvider20261018 originalNormKernelRanksTwoConjugateFiniteProvider20261018 originalNormKernelRanksTwoPiExponentProvider20261018 originalNormKernelRanksTwoConjugateExponentProvider20261018 originalNormKernelRanksTwoPiModuleProvider20261018 originalNormKernelRanksTwoConjugateModuleProvider20261018

local instance sourceComplementaryExactSequenceRationalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
namespace MazurTransfer.Order13ActualComplementaryCharacterExactSequence
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
open RepresentationCharacterTwist
section Generic
variable (ψ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
  [IsMonHom ψ] [IsFinite ψ.left] [Fact (∀ z : Kernel K ψ, z ^ 19 = 1)]
local instance complementaryExactSequenceOriginalGenericModuleProvider20261018 : Module (ZMod 19) (Additive (Kernel K ψ)) := kernelZModModule K ψ

def fixedVectorIntertwining (a : Additive (Kernel K ψ))
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K ψ σ a = a) :
    Representation.IntertwiningMap (Representation.trivial (ZMod 19) (K ≃ₐ[ℚ] K) (ZMod 19))
      (kernelRepresentation K ψ) :=
  (LinearMap.toSpanSingleton (ZMod 19) (Additive (Kernel K ψ)) a).intertwiningMap_of_isIntertwiningMap _ _ (by
    intro σ c
    change c • a = kernelRepresentation K ψ σ (c • a)
    rw [map_smul, ha σ])

def HasComplementaryCharacterExactSequence (χ : (K ≃ₐ[ℚ] K) →* (ZMod 19)ˣ) : Prop :=
  ∃ i : Representation.IntertwiningMap
      (Representation.trivial (ZMod 19) (K ≃ₐ[ℚ] K) (ZMod 19)) (kernelRepresentation K ψ),
  ∃ p : Representation.IntertwiningMap (kernelRepresentation K ψ) (twist χ⁻¹ (rootsRepresentation K)),
    Function.Injective i ∧ Function.Surjective p ∧ LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap
end Generic

end MazurTransfer.Order13ActualComplementaryCharacterExactSequence
#print axioms MazurTransfer.Order13ActualComplementaryCharacterExactSequence.fixedVectorIntertwining
#print axioms MazurTransfer.Order13ActualComplementaryCharacterExactSequence.HasComplementaryCharacterExactSequence


