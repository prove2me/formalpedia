-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualArithmeticCharacterExactSequenceOriginalPredicateDataExplicitFiniteModuleNamespaceV220261018
-- name    : MazurTransfer_Order13ActualArithmeticCharacterExactSequenceOriginalPredicateDataExplicitFiniteModuleNamespaceV220261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T23:48:44.982825+00:00
-- url     : https://prove2.me/theorems/8f5d4399-a132-4055-8aba-41cb142191bd
-- title:
--   Original actual arithmetic-character exact-sequence predicate
-- statement:
--   The original generic predicate requiring an injective scalar-character intertwining map, a surjective map to the literal nineteen-root representation, and equality of image and kernel. Its full type and whole value, the full generic module-provider type and value, and every required original context are checked. Named downstream consumer: both fixed-line arithmetic-character exact sequences and their original dichotomy. This definition supplies no arithmetic existence proof.
-- source:
--   MazurTheorem original declarations and immediately necessary constructor certificates; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual norm factor opposite the rational fixed line is
an extension of the literal cyclotomic19 representation by the explicit
order-six arithmetic13 character. Both factor orderings are retained.
Named downstream consumer: full norm representations and the exceptional
local Kummer/Selmer conditions in the rank-zero descent.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicCharacterOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelRanksTwoOriginalModuleContextData20261018
import Definitions.Def_MazurTransfer_ScalarCharacterLineOriginalRepresentationsAndIntertwiningData20261018
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

local instance sourceArithmeticExactSequenceRationalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
namespace MazurTransfer.Order13ActualArithmeticCharacterExactSequence
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
open ScalarCharacterLine
section Generic
variable (ψ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
  [IsMonHom ψ] [IsFinite ψ.left] [Fact (∀ z : Kernel K ψ, z ^ 19 = 1)]
local instance arithmeticExactSequenceOriginalGenericModuleProvider20261018 : Module (ZMod 19) (Additive (Kernel K ψ)) := kernelZModModule K ψ

def HasArithmeticCharacterExactSequence (χ : (K ≃ₐ[ℚ] K) →* (ZMod 19)ˣ) : Prop :=
  ∃ i : Representation.IntertwiningMap (scalarRepresentation χ) (kernelRepresentation K ψ),
  ∃ p : Representation.IntertwiningMap (kernelRepresentation K ψ) (rootsRepresentation K),
    Function.Injective i ∧ Function.Surjective p ∧ LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap
end Generic

end MazurTransfer.Order13ActualArithmeticCharacterExactSequence
#print axioms MazurTransfer.Order13ActualArithmeticCharacterExactSequence.HasArithmeticCharacterExactSequence


