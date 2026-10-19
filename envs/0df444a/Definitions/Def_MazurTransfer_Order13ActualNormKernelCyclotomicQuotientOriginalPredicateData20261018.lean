-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicQuotientOriginalPredicateData20261018
-- name    : MazurTransfer_Order13ActualNormKernelCyclotomicQuotientOriginalPredicateData20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T16:12:37.777211+00:00
-- url     : https://prove2.me/theorems/f9d369f2-05a3-4110-88ef-37d2dae38e1b
-- title:
--   Original actual norm-kernel cyclotomic quotient predicate
-- statement:
--   The original predicate asserting an equivariant quotient from an actual norm kernel to literal nineteen-th roots with one-dimensional kernel. The complete original predicate type and value, forty-seven complete original provider types and twenty-three nonproof provider values are checked. The named downstream consumers are hasCyclotomicQuotient_of_fixed_line and actual_cyclotomic_quotient_dichotomy. This definition alone asserts no quotient existence.
-- source:
--   MazurTheorem Order13ActualNormKernelCyclotomicQuotient.HasCyclotomicQuotient, exact original predicate; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original predicate for a quotient of an actual norm
kernel representation onto literal nineteen roots, with one-dimensional
kernel. The complete original predicate type and value are checked.
Named downstream consumers: hasCyclotomicQuotient_of_fixed_line and
actual_cyclotomic_quotient_dichotomy. No quotient existence is asserted here.
Original MazurTheorem predicate, using official Anthropic FLT interfaces at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicCharacterIntertwiningOriginalData20261018
noncomputable section
namespace MazurTransfer.Order13ActualNormKernelCyclotomicQuotient
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelF19Representation Order13ActualNormKernelCyclotomicCharacter
open NineteenRootsGaloisRepresentation
open scoped CategoryTheory.MonObj
attribute [local instance] kernelCharacterOriginalGroupProvider20261018 kernelCharacterOriginalCommProvider20261018 kernelCharacterOriginalPiHomProvider20261018 kernelCharacterOriginalConjugateHomProvider20261018 kernelCharacterOriginalPrimeProvider20261018 kernelCharacterOriginalLeftModuleProvider20261018 kernelCharacterOriginalRightModuleProvider20261018 kernelCharacterOriginalRootsModuleProvider20261018
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
variable (ψ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
  [IsMonHom ψ] [IsFinite ψ.left] [Fact (∀ z : Kernel K ψ, z ^ 19 = 1)]

def HasCyclotomicQuotient : Prop :=
  ∃ f : Representation.IntertwiningMap (kernelRepresentation K ψ) (rootsRepresentation K),
    Function.Surjective f ∧ Module.finrank (ZMod 19) (LinearMap.ker f.toLinearMap) = 1

end MazurTransfer.Order13ActualNormKernelCyclotomicQuotient
#print axioms MazurTransfer.Order13ActualNormKernelCyclotomicQuotient.HasCyclotomicQuotient


