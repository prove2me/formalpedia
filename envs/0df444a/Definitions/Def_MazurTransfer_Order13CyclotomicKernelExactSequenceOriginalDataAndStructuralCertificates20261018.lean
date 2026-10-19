-- Prove2me | Definitions.Def_MazurTransfer_Order13CyclotomicKernelExactSequenceOriginalDataAndStructuralCertificates20261018
-- name    : MazurTransfer_Order13CyclotomicKernelExactSequenceOriginalDataAndStructuralCertificates20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T20:43:25.386976+00:00
-- url     : https://prove2.me/theorems/3f0d4a7b-aa42-4453-9a1e-c91e308d9eba
-- title:
--   Original cyclotomic kernel representation, inclusion and exact-sequence predicate
-- statement:
--   The kernel of an equivariant character to the literal nineteen-root representation carries its original Galois representation. Its original inclusion is injective with range exactly the character kernel. The exact-sequence predicate retains surjectivity of the character, this injection and range equality, and one-dimensionality of the kernel. Five complete original declaration types and three whole constructor values are checked, together with fifty-five context provider types and twenty-four whole nonproof values. Named downstream consumers: Order13ActualNormKernelCyclotomicExactSequence.hasCyclotomicExactSequence_of_quotient and Order13ActualNormKernelCyclotomicExactSequence.actual_cyclotomic_exact_sequence_dichotomy.
-- source:
--   MazurTheorem Order13ActualNormKernelCyclotomicExactSequence.cyclotomicKernelRepresentation, cyclotomicKernelInclusion, cyclotomicKernelInclusion_injective, cyclotomicKernelInclusion_range, and HasCyclotomicExactSequence; complete original types and constructor values preserved; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual cyclotomic quotient extends to a short exact
sequence of Galois representations with a one-dimensional stable kernel.
Named downstream consumer: identifying that kernel's arithmetic13 character
and the local norm Selmer conditions. No splitting is asserted.
-/
/- Constructor interface: the kernel representation and inclusion, their structural injection/range certificates, and the original exact-sequence predicate. Named downstream consumer: the actual cyclotomic short exact sequence. -/
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual norm factor opposite the actual invariant line
has an equivariant quotient onto the literal cyclotomic19 representation,
with a one-dimensional kernel. Both possible factor orderings are retained.
Named downstream consumer: identifying the remaining arithmetic13 character
and proving the actual local Selmer conditions.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicQuotientOriginalPredicateData20261018
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
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


namespace MazurTransfer.Order13ActualNormKernelCyclotomicExactSequence
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
variable (ψ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom ψ] [IsFinite ψ.left] [Fact (∀ z : Kernel K ψ, z ^ 19 = 1)]
abbrev cyclotomicKernelRepresentation
    (f : Representation.IntertwiningMap (kernelRepresentation K ψ) (rootsRepresentation K)) :=
  f.ker.toRepresentation

def cyclotomicKernelInclusion
    (f : Representation.IntertwiningMap (kernelRepresentation K ψ) (rootsRepresentation K)) :
    Representation.IntertwiningMap (cyclotomicKernelRepresentation K ψ f) (kernelRepresentation K ψ) :=
  (LinearMap.ker f.toLinearMap).subtype.intertwiningMap_of_isIntertwiningMap _ _ (by
    intro σ z
    rfl)

theorem cyclotomicKernelInclusion_injective
    (f : Representation.IntertwiningMap (kernelRepresentation K ψ) (rootsRepresentation K)) :
    Function.Injective (cyclotomicKernelInclusion K ψ f) := Subtype.val_injective

theorem cyclotomicKernelInclusion_range
    (f : Representation.IntertwiningMap (kernelRepresentation K ψ) (rootsRepresentation K)) :
    LinearMap.range (cyclotomicKernelInclusion K ψ f).toLinearMap = LinearMap.ker f.toLinearMap :=
  Submodule.range_subtype _

def HasCyclotomicExactSequence : Prop :=
  ∃ f : Representation.IntertwiningMap (kernelRepresentation K ψ) (rootsRepresentation K),
    Function.Surjective f ∧ Function.Injective (cyclotomicKernelInclusion K ψ f) ∧
      LinearMap.range (cyclotomicKernelInclusion K ψ f).toLinearMap = LinearMap.ker f.toLinearMap ∧
      Module.finrank (ZMod 19) (LinearMap.ker f.toLinearMap) = 1

end MazurTransfer.Order13ActualNormKernelCyclotomicExactSequence
#print axioms MazurTransfer.Order13ActualNormKernelCyclotomicExactSequence.cyclotomicKernelInclusion
#print axioms MazurTransfer.Order13ActualNormKernelCyclotomicExactSequence.HasCyclotomicExactSequence


