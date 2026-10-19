-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicCharacterOriginalData20261018
-- name    : MazurTransfer_Order13ActualNormKernelCyclotomicCharacterOriginalData20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T15:24:18.059641+00:00
-- url     : https://prove2.me/theorems/c42d96d8-ead8-49b0-a8cf-f812de18b7cc
-- title:
--   Original actual norm-kernel pairing characters into nineteen-th roots
-- statement:
--   The original monoid character and F19-linear character obtained by pairing a vector in one actual norm kernel against the other actual norm kernel. Both complete original constructor types and values are checked. Seven original pairing-law proof helpers are retained with full types checked and zero nonproof helpers. Thirty-four original group, action, module and scalar provider types and sixteen nonproof values are checked. The named downstream consumers are kernelCharacter_galois, kernelCharacter_surjective_of_cross and actual cyclotomic quotients. No Galois compatibility, surjectivity, Selmer bound or rational rank result is asserted by this constructor interface.
-- source:
--   MazurTheorem Order13ActualNormKernelCyclotomicCharacter, exact original constructors and checked original pairing laws; official Anthropic FLT interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: original monoid and F19-linear characters obtained by
pairing a vector in one actual norm kernel against the other kernel.
Seven original pairing-law proof helpers are retained with their complete
types checked; no nonproof helper or additional arithmetic hypothesis is
introduced. Named downstream consumers: kernelCharacter_galois and
kernelCharacter_surjective_of_cross, then actual cyclotomic quotients.
Original MazurTheorem constructors and pairing laws; official Anthropic FLT
interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelNineteenEmbeddingOriginalData20261018
import Definitions.Def_MazurTransfer_NineteenRootsGaloisRepresentationOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionPairingTransportOriginalData20261018

noncomputable section
namespace MazurTransfer.KernelCyclotomicCharacterOriginalProofHelpers20261018
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualNormKernelProductCardinality Order13ActualGeometricNineteenTorsionDivisorComparison
open Order13ActualNineteenTorsionPairingTransport Order13ActualGeometricNineteenDivisorialPairing
open scoped CategoryTheory.MonObj
attribute [local instance] actualNineteenTorsionProductOriginalGroupProvider20261018 actualNineteenTorsionProductOriginalCommProvider20261018
attribute [local instance] pairingTransportOriginalFactProvider20261018 pairingTransportOriginalAlgebraProvider20261018
variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
variable (d : DivisorialWeilPairingData K (actualCurveFunctionField K) 19)

theorem pairingUnits_add_left (x x' y : NineteenTorsion K) :
    pairingUnits K d (x + x') y = pairingUnits K d x y * pairingUnits K d x' y := by
  apply Units.ext
  change d.pair (geometricNineteenTorsionDivisorAddEquiv K (x + x'))
    (geometricNineteenTorsionDivisorAddEquiv K y) = _
  rw [map_add]
  exact d.pair_add_left _ _ _

theorem pairingUnits_add_right (x y y' : NineteenTorsion K) :
    pairingUnits K d x (y + y') = pairingUnits K d x y * pairingUnits K d x y' := by
  apply Units.ext
  change d.pair (geometricNineteenTorsionDivisorAddEquiv K x)
    (geometricNineteenTorsionDivisorAddEquiv K (y + y')) = _
  rw [map_add]
  exact d.pair_add_right _ _ _

theorem pairingUnits_zero_left (y : NineteenTorsion K) : pairingUnits K d 0 y = 1 := by
  apply Units.ext
  change d.pair (geometricNineteenTorsionDivisorAddEquiv K 0)
    (geometricNineteenTorsionDivisorAddEquiv K y) = 1
  rw [map_zero]
  exact d.pair_zero_left _

theorem pairingUnits_zero_right (x : NineteenTorsion K) : pairingUnits K d x 0 = 1 := by
  apply Units.ext
  change d.pair (geometricNineteenTorsionDivisorAddEquiv K x)
    (geometricNineteenTorsionDivisorAddEquiv K 0) = 1
  rw [map_zero]
  exact d.pair_zero_right _

theorem pairingUnits_nsmul_left (n : ℕ) (x y : NineteenTorsion K) :
    pairingUnits K d (n • x) y = pairingUnits K d x y ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pairingUnits_zero_left, pow_zero]
  | succ n ih => rw [succ_nsmul, pairingUnits_add_left, ih, pow_succ]

theorem actualPairing_pow_nineteen (x y : NineteenTorsion K) :
    actualGeometricNineteenPairing K x y ^ 19 = 1 := by
  have hx : (19 : ℕ) • x = 0 := by
    apply Subtype.ext
    exact x.property
  change pairingUnits K (actualDivisorialNineteenPairingData K) x y ^ 19 = 1
  rw [← pairingUnits_nsmul_left, hx, pairingUnits_zero_left]

theorem actualPairing_add_right (x y y' : NineteenTorsion K) :
    actualGeometricNineteenPairing K x (y + y') =
      actualGeometricNineteenPairing K x y * actualGeometricNineteenPairing K x y' :=
  pairingUnits_add_right K _ x y y'

end MazurTransfer.KernelCyclotomicCharacterOriginalProofHelpers20261018

noncomputable section
namespace MazurTransfer.Order13ActualNormKernelCyclotomicCharacter
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance kernelCharacterOriginalGroupProvider20261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance kernelCharacterOriginalCommProvider20261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance kernelCharacterOriginalPiHomProvider20261018 : IsMonHom schemePi := schemePi_isMonHom
local instance kernelCharacterOriginalConjugateHomProvider20261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]

open Order13ActualNormKernelNineteenEmbedding Order13ActualNormKernelF19Representation
open Order13ActualNormKernelFiniteModule Order13ActualNormKernelProductCardinality
open Order13ActualNineteenTorsionNormPairingAdjoint Order13ActualNineteenTorsionGaloisPairingBridge
open Order13ActualGeometricNineteenDivisorialPairing
open NineteenRootsGaloisRepresentation
variable [IsAlgClosed K]
local instance kernelCharacterOriginalPrimeProvider20261018 : Fact (Nat.Prime 19) := ⟨by decide⟩
variable (φ ψ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
  [IsMonHom φ] [IsMonHom ψ] [IsFinite φ.left] [IsFinite ψ.left]
  [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] [Fact (∀ z : Kernel K ψ, z ^ 19 = 1)]
local instance kernelCharacterOriginalLeftModuleProvider20261018 : Module (ZMod 19) (Additive (Kernel K φ)) := kernelZModModule K φ
local instance kernelCharacterOriginalRightModuleProvider20261018 : Module (ZMod 19) (Additive (Kernel K ψ)) := kernelZModModule K ψ
local instance kernelCharacterOriginalRootsModuleProvider20261018 : Module (ZMod 19) (Additive (Roots K)) := rootsZModModule K

open KernelCyclotomicCharacterOriginalProofHelpers20261018

def kernelCharacter (a : Additive (Kernel K φ)) : Kernel K ψ →* Roots K where
  toFun z := ⟨actualGeometricNineteenPairing K (kernelNineteenAddHom K φ a)
    (kernelNineteenAddHom K ψ (Additive.ofMul z)), actualPairing_pow_nineteen K _ _⟩
  map_one' := by
    apply Subtype.ext
    change actualGeometricNineteenPairing K (kernelNineteenAddHom K φ a)
      (kernelNineteenAddHom K ψ 0) = 1
    rw [map_zero]
    exact pairingUnits_zero_right K (actualDivisorialNineteenPairingData K) _
  map_mul' x y := by
    apply Subtype.ext
    change actualGeometricNineteenPairing K (kernelNineteenAddHom K φ a)
      (kernelNineteenAddHom K ψ (Additive.ofMul x + Additive.ofMul y)) = _
    rw [map_add, actualPairing_add_right]
    rfl

def kernelCharacterLinear (a : Additive (Kernel K φ)) :
    Additive (Kernel K ψ) →ₗ[ZMod 19] Additive (Roots K) :=
  (kernelCharacter K φ ψ a).toAdditive.toZModLinearMap 19

end MazurTransfer.Order13ActualNormKernelCyclotomicCharacter
#print axioms MazurTransfer.Order13ActualNormKernelCyclotomicCharacter.kernelCharacter
#print axioms MazurTransfer.Order13ActualNormKernelCyclotomicCharacter.kernelCharacterLinear


