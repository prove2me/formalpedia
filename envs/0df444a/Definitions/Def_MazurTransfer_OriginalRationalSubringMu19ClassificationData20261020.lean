-- Prove2me | Definitions.Def_MazurTransfer_OriginalRationalSubringMu19ClassificationData20261020
-- name    : MazurTransfer_OriginalRationalSubringMu19ClassificationData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-22T02:04:36.0209+00:00
-- url     : https://prove2.me/theorems/1b60a7a7-fbe3-4f59-bf35-145f878c6633
-- title:
--   Original fixed field-point restriction for normalized local mu19 scalar change
-- statement:
--   Retain the same original fixed field-point restriction under canonical scalar change at nineteen, with all five original prime, field algebra, scalar tower and root module providers. The complete original restriction type and whole value, all provider types and nonproof whole values, every generated helper type, and original coefficient and point-operation contexts are independently checked. Named downstream consumer: exact previously selected pi quotient map in literal mu19 coordinates before integral norm torsor pushforward.
-- source:
--   MazurTheorem Order13RationalSubringMu19Classification by Vas and contributors; same local Hopf model, canonical scalar change and given arithmetic label, Apache-2.0.

import Definitions.Def_MazurTransfer_OriginalRationalSubringBaseChangeData20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: normalize the canonical scalar change of the SAME local
literal-root quotient to its GIVEN arithmetic label, pointwise.
Named downstream consumer: exact previously selected pi quotient map in
literal mu19 coordinates, before actual integral norm torsor pushforward.
-/

noncomputable section
namespace MazurTransfer.Order13RationalSubringMu19Classification
open Order13LocalIntegralCoefficientMaps Order13RationalSubringBaseChange
open NineteenRootsGaloisRepresentation
open scoped TensorProduct
local instance instFactPrimeOfNatNat_order13RationalSubringMu19Classification : Fact (Nat.Prime 19) := ⟨by decide⟩
local notation "F" => AlgebraicClosure ℚ
local notation "R" => LocalRing 19
local notation "S" => GaloisRep.ratLocalizedAt 19
local instance instAlgebraLocalRingOfNatNatAlgebraicClosureRat_order13RationalSubringMu19Classification : Algebra R F := Algebra.compHom F (algebraMap R ℚ)
local instance instIsScalarTowerLocalRingOfNatNatRatAlgebraicClosure_order13RationalSubringMu19Classification : IsScalarTower R ℚ F := IsScalarTower.of_algebraMap_eq' rfl
local instance instIsScalarTowerLocalRingOfNatNatSubtypeRatMemSubringRatLocalizedAtAlgebraicClosure_order13RationalSubringMu19Classification : IsScalarTower R S F :=
  localSubringTower 19 F (aRK := (inferInstance : Algebra R F))
    (tRQ := (inferInstance : IsScalarTower R ℚ F))
local instance instModuleZModOfNatNatAdditiveSubtypeUnitsAlgebraicClosureRatMemSubgroupRoots_order13RationalSubringMu19Classification : Module (ZMod 19) (Additive (Roots F)) := rootsZModModule F
variable (H : Type) [CommRing H] [HopfAlgebra R H]
variable [Module.Finite R H] [Module.Flat R H] [Coalgebra.IsCocomm R H]
def fixedBasePoint (f : WithConv (S ⊗[R] H →ₐ[S] F)) : WithConv (H →ₐ[R] F) :=
  @HopfBaseChangeArithmeticPoints.restrictPoint R S H F _ _ _ _ _ _
    (inferInstance : Algebra R F) _ (inferInstance : IsScalarTower R S F) f

variable (e : WithConv (H →ₐ[R] F) ≃ Additive (Roots F))
variable (he_add : ∀ f g, e (f * g) = e f + e g)
variable (he_act : ∀ (σ : F ≃ₐ[ℚ] F) (f g : WithConv (H →ₐ[R] F)),
  (∀ x : H, g x = σ (f x)) → e g = rootsRepresentation F σ (e f))



end MazurTransfer.Order13RationalSubringMu19Classification

#print axioms MazurTransfer.Order13RationalSubringMu19Classification.fixedBasePoint
#print axioms MazurTransfer.Order13RationalSubringMu19Classification.instAlgebraLocalRingOfNatNatAlgebraicClosureRat_order13RationalSubringMu19Classification
#print axioms MazurTransfer.Order13RationalSubringMu19Classification.instIsScalarTowerLocalRingOfNatNatSubtypeRatMemSubringRatLocalizedAtAlgebraicClosure_order13RationalSubringMu19Classification
#print axioms MazurTransfer.Order13RationalSubringMu19Classification.instFactPrimeOfNatNat_order13RationalSubringMu19Classification
#print axioms MazurTransfer.Order13RationalSubringMu19Classification.instIsScalarTowerLocalRingOfNatNatRatAlgebraicClosure_order13RationalSubringMu19Classification
#print axioms MazurTransfer.Order13RationalSubringMu19Classification.instModuleZModOfNatNatAdditiveSubtypeUnitsAlgebraicClosureRatMemSubgroupRoots_order13RationalSubringMu19Classification


