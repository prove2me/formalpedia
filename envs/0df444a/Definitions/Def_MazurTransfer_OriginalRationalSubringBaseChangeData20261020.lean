-- Prove2me | Definitions.Def_MazurTransfer_OriginalRationalSubringBaseChangeData20261020
-- name    : MazurTransfer_OriginalRationalSubringBaseChangeData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T20:57:43.233299+00:00
-- url     : https://prove2.me/theorems/3251e6b4-a2b4-4cbc-a094-4722421b7f53
-- title:
--   Original scalar base change and arithmetic labels along the proved rational subring equivalence
-- statement:
--   Retain the canonical original scalar base change of the same Hopf model and the same arithmetic point label along the proved coefficient equivalence. Preserve and independently compare every original algebra, scalar tower, prime and literal-root module provider, complete label type and whole value, and original coefficient and point-operation contexts. Named downstream consumer: normalized same-model selected pi quotients and torsor pushforward at nineteen.
-- source:
--   MazurTheorem Order13RationalSubringBaseChange by Vas and contributors; canonical same-model scalar base change and fixed arithmetic labels, Apache-2.0.

import Definitions.Def_MazurTransfer_OriginalHopfBaseChangeArithmeticPointsData20261020
import Definitions.Def_MazurTransfer_OriginalLocalRationalSubringEquivalenceData20261020
import Definitions.Def_MazurTransfer_OriginalNineteenRootsCyclotomicPowerData20261020
import Theorems.Thm_MazurTransfer_original_local_rational_subring_equivalence_compatibility
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: CANONICAL scalar base change of the GIVEN local Hopf model
along the PROVED base equivalence, preserving its GIVEN arithmetic label.
Named downstream consumer: classification and torsor pushforward for the
SAME selected pi quotient at nineteen. Descent of the inverse-character
twist and integral Kummer unit conditions are separate obligations.
-/

noncomputable section
namespace MazurTransfer.Order13RationalSubringBaseChange
open Order13LocalIntegralCoefficientMaps Order13LocalRationalSubringEquivalence
open scoped TensorProduct
variable (q : ℕ) [Fact q.Prime]

instance localSubringAlgebra : Algebra (LocalRing q) (GaloisRep.ratLocalizedAt q) :=
  (localRationalSubringEquiv q).toRingHom.toAlgebra

variable (K : Type) [CommRing K] [Algebra ℚ K]
variable [aRK : Algebra (LocalRing q) K] [tRQ : IsScalarTower (LocalRing q) ℚ K]
variable [aSK : Algebra (GaloisRep.ratLocalizedAt q) K]
variable [tSQ : IsScalarTower (GaloisRep.ratLocalizedAt q) ℚ K]

instance localSubringTower : IsScalarTower (LocalRing q) (GaloisRep.ratLocalizedAt q) K :=
  IsScalarTower.of_algebraMap_eq fun r => (MazurTransfer.original_local_rational_subring_equivalence_compatibility.2.2.2.1 q K r).symm

variable {H : Type} [CommRing H] [HopfAlgebra (LocalRing q) H] {M : Type}
variable (e : WithConv (H →ₐ[LocalRing q] K) ≃ M)

def baseChangeLabel :
    WithConv (GaloisRep.ratLocalizedAt q ⊗[LocalRing q] H →ₐ[GaloisRep.ratLocalizedAt q] K) ≃ M :=
  HopfBaseChangeArithmeticPoints.pointEquiv.trans e

variable [AddCommGroup M]
variable (he_add : ∀ f g, e (f * g) = e f + e g)


variable (ρ : (K ≃ₐ[ℚ] K) → M → M)
variable (he_act : ∀ (σ : K ≃ₐ[ℚ] K) (f g : WithConv (H →ₐ[LocalRing q] K)),
  (∀ x : H, g x = σ (f x)) → e g = ρ σ (e f))


section Nineteen
local instance instFactPrimeOfNatNat_order13RationalSubringBaseChange : Fact (Nat.Prime 19) := ⟨by decide⟩
local notation "F" => AlgebraicClosure ℚ
local notation "R" => LocalRing 19
local notation "S" => GaloisRep.ratLocalizedAt 19
open NineteenRootsGaloisRepresentation
local instance instAlgebraLocalRingOfNatNatAlgebraicClosureRat_order13RationalSubringBaseChange : Algebra R F := Algebra.compHom F (algebraMap R ℚ)
local instance instIsScalarTowerLocalRingOfNatNatRatAlgebraicClosure_order13RationalSubringBaseChange : IsScalarTower R ℚ F := IsScalarTower.of_algebraMap_eq' rfl
local instance instModuleZModOfNatNatAdditiveSubtypeUnitsAlgebraicClosureRatMemSubgroupRoots_order13RationalSubringBaseChange : Module (ZMod 19) (Additive (Roots F)) := rootsZModModule F

variable (G : Type) [CommRing G] [HopfAlgebra R G]
variable [Module.Finite R G] [Module.Flat R G] [Coalgebra.IsCocomm R G]
variable (label : WithConv (G →ₐ[R] F) ≃ Additive (Roots F))
variable (hadd : ∀ f g, label (f * g) = label f + label g)
variable (hact : ∀ (σ : F ≃ₐ[ℚ] F) (f g : WithConv (G →ₐ[R] F)),
  (∀ x : G, g x = σ (f x)) → label g = rootsRepresentation F σ (label f))


end Nineteen

end MazurTransfer.Order13RationalSubringBaseChange
#print axioms MazurTransfer.Order13RationalSubringBaseChange.baseChangeLabel
#print axioms MazurTransfer.Order13RationalSubringBaseChange.instModuleZModOfNatNatAdditiveSubtypeUnitsAlgebraicClosureRatMemSubgroupRoots_order13RationalSubringBaseChange
#print axioms MazurTransfer.Order13RationalSubringBaseChange.localSubringTower
#print axioms MazurTransfer.Order13RationalSubringBaseChange.instFactPrimeOfNatNat_order13RationalSubringBaseChange
#print axioms MazurTransfer.Order13RationalSubringBaseChange.localSubringAlgebra
#print axioms MazurTransfer.Order13RationalSubringBaseChange.instIsScalarTowerLocalRingOfNatNatRatAlgebraicClosure_order13RationalSubringBaseChange
#print axioms MazurTransfer.Order13RationalSubringBaseChange.instAlgebraLocalRingOfNatNatAlgebraicClosureRat_order13RationalSubringBaseChange


