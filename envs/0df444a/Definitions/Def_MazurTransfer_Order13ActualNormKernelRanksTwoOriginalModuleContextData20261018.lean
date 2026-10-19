-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualNormKernelRanksTwoOriginalModuleContextData20261018
-- name    : MazurTransfer_Order13ActualNormKernelRanksTwoOriginalModuleContextData20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T12:29:29.871534+00:00
-- url     : https://prove2.me/theorems/f0e1ddf1-39d3-410f-b114-28dd1aea3d22
-- title:
--   Original finite F19 module context for both actual norm kernels
-- statement:
--   Publish the original prime, finite-morphism, finite-kernel and exponent proof providers and the two original F19 module values needed to state the actual norm-kernel dimension-two theorem. Nine complete original declarations and both nonproof module values are checked, together with four original rank-context group providers and two kernel-group dependency providers. This interface asserts no numerical dimension; its named consumer is Order13ActualNormKernelRanksTwo.actual_norm_kernel_ranks_two.
-- source:
--   MazurTheorem Order13ActualNormKernelRanksTwo original finite/module context; full original types and the two original module values preserved.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: preserve the original finite F19-module context of each
actual norm kernel, including its finite/exponent proof providers and
literal module value. No numerical rank is asserted by this interface.
Named downstream consumer: Order13ActualNormKernelRanksTwo.actual_norm_kernel_ranks_two.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelProductCardinalityData20261018
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormFiniteEtaleIsogenies_actual_norm_factors_are_finite_etale_surjective
noncomputable section
namespace MazurTransfer.Order13ActualNormKernelRanksTwo
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
open Order13ActualPicardNormKernelGaloisAction Order13ActualNormKernelFiniteModule
open Order13ActualNormKernelProductCardinality
attribute [local instance] actualNineteenTorsionProductOriginalGroupProvider20261018
  actualNineteenTorsionProductOriginalCommProvider20261018
  actualNineteenTorsionProductOriginalPiHomProvider20261018
  actualNineteenTorsionProductOriginalConjugateHomProvider20261018
local instance originalNormKernelRanksTwoPrimeProvider20261018 : Fact (Nat.Prime 19) := ⟨by decide⟩
local instance originalNormKernelRanksTwoPiFiniteProvider20261018 : IsFinite schemePi.left :=
  Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective.1.1
local instance originalNormKernelRanksTwoConjugateFiniteProvider20261018 : IsFinite schemePiConjugate.left :=
  Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective.2.1
variable (K : Type) [Field K] [CharZero K]
local instance originalNormKernelRanksTwoPiKernelFiniteProvider20261018 : Finite (Kernel K schemePi) := kernel_finite K schemePi
local instance originalNormKernelRanksTwoConjugateKernelFiniteProvider20261018 : Finite (Kernel K schemePiConjugate) := kernel_finite K schemePiConjugate
local instance originalNormKernelRanksTwoPiExponentProvider20261018 : Fact (∀ z : Kernel K schemePi, z ^ 19 = 1) := ⟨pi_kernel_exponent_nineteen K⟩
local instance originalNormKernelRanksTwoConjugateExponentProvider20261018 : Fact (∀ z : Kernel K schemePiConjugate, z ^ 19 = 1) := ⟨piConjugate_kernel_exponent_nineteen K⟩
local instance originalNormKernelRanksTwoPiModuleProvider20261018 : Module (ZMod 19) (Additive (Kernel K schemePi)) := kernelZModModule K schemePi
local instance originalNormKernelRanksTwoConjugateModuleProvider20261018 : Module (ZMod 19) (Additive (Kernel K schemePiConjugate)) := kernelZModModule K schemePiConjugate
end MazurTransfer.Order13ActualNormKernelRanksTwo
#print axioms MazurTransfer.Order13ActualNormKernelRanksTwo.originalNormKernelRanksTwoPiModuleProvider20261018
#print axioms MazurTransfer.Order13ActualNormKernelRanksTwo.originalNormKernelRanksTwoConjugateModuleProvider20261018


