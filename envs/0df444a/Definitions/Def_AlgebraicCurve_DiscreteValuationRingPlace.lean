-- Prove2me | Definitions.Def_AlgebraicCurve_DiscreteValuationRingPlace
-- name    : AlgebraicCurve_DiscreteValuationRingPlace
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T17:59:51.463296+00:00
-- url     : https://prove2.me/theorems/4f7e1aa2-c064-4c54-90ec-138e08ebb448
-- title:
--   A discrete valuation ring as a place of its fraction field
-- statement:
--   Let $k$ be a field, let $R$ be a discrete valuation $k$-algebra, and let $F$ be a fraction field of $R$ with compatible scalar actions. The file defines the place $P_R$ of $F$ whose valuation ring is the image of $R$, together with equivalences $$R≃_k O_{P_R},   κ(R)≃_k κ(P_R).$$ This turns an explicit local DVR into an actual algebraic-curve place without losing its residue algebra.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
/-! A discrete valuation local ring defines a place of its fraction field,
with the same residue field over the constants. -/
noncomputable section
namespace AlgebraicCurve

variable (k R F : Type*) [Field k] [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] [Field F] [Algebra k R] [Algebra R F]
  [Algebra k F] [IsScalarTower k R F] [IsFractionRing R F]

/-- The place whose valuation ring is the image of a given DVR in its fraction field. -/
def placeOfDiscreteValuationRing : Place k F :=
  Place.ofHeightOneSpectrum (IsDiscreteValuationRing.maximalIdeal R)

/-- Identify the original DVR with the valuation ring of the associated place. -/
def discreteValuationRingPlaceAlgEquiv :
    R ≃ₐ[k] (placeOfDiscreteValuationRing k R F).toValuationSubring :=
  AlgEquiv.ofRingEquiv (f := IsDiscreteValuationRing.equivValuationSubring (A := R) (K := F))
    (fun a => by
      apply Subtype.ext
      change algebraMap R F (algebraMap k R a) = algebraMap k F a
      exact (IsScalarTower.algebraMap_apply k R F a).symm)

/-- The associated place has the same residue field as the original DVR. -/
def discreteValuationRingPlaceResidueAlgEquiv :
    IsLocalRing.ResidueField R ≃ₐ[k] (placeOfDiscreteValuationRing k R F).ResidueField :=
  AlgEquiv.ofRingEquiv
    (f := IsLocalRing.ResidueField.mapEquiv (discreteValuationRingPlaceAlgEquiv k R F).toRingEquiv)
    (fun a => by
      show IsLocalRing.ResidueField.mapEquiv _ (IsLocalRing.residue _ _)
        = IsLocalRing.residue _ _
      rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
      exact congrArg _ ((discreteValuationRingPlaceAlgEquiv k R F).commutes a))

end AlgebraicCurve


