-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerImage
-- name    : QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerImage
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:06:00.413557+00:00
-- url     : https://prove2.me/theorems/538d4402-a502-4e24-bd7f-565121944ab1
-- title:
--   Affine Kaehler Image
-- statement:
--   Definitions and structural lemmas for Affine Kaehler Image, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineKaehlerImage.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_KaehlerMapImage
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.LocalProperties.Submodule
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ValuationCentres
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
noncomputable section
section module
variable (A W : Type*) [CommRing A] [AddCommGroup W] [Module A W]
end module
section localization
variable (R A B K : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing K]
variable [Algebra R A] [Algebra R B] [Algebra R K]
variable [Algebra A B] [Algebra B K] [Algebra A K]
variable [IsScalarTower R A B] [IsScalarTower R B K] [IsScalarTower R A K]
variable [IsScalarTower A B K]
variable [SMulCommClass R A B] [SMulCommClass R A K] [SMulCommClass R B K]
end localization
section allMaximal
variable (R A K : Type*) [CommRing R] [CommRing A] [CommRing K]
variable [Algebra R A] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
variable [SMulCommClass R A K]
variable (B : ∀ (P : Ideal A) [P.IsMaximal], Type*)
variable [∀ (P : Ideal A) [P.IsMaximal], CommRing (B P)]
variable [∀ (P : Ideal A) [P.IsMaximal], Algebra A (B P)]
variable [∀ (P : Ideal A) [P.IsMaximal], IsLocalization.AtPrime (B P) P]
variable [∀ (P : Ideal A) [P.IsMaximal], Algebra R (B P)]
variable [∀ (P : Ideal A) [P.IsMaximal], Algebra (B P) K]
variable [∀ (P : Ideal A) [P.IsMaximal], IsScalarTower R A (B P)]
variable [∀ (P : Ideal A) [P.IsMaximal], IsScalarTower R (B P) K]
variable [∀ (P : Ideal A) [P.IsMaximal], IsScalarTower A (B P) K]
variable [∀ (P : Ideal A) [P.IsMaximal], SMulCommClass R A (B P)]
variable [∀ (P : Ideal A) [P.IsMaximal], SMulCommClass R (B P) K]
end allMaximal
end
end QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
noncomputable section
def kaehlerValuationSubringEquiv {K : Type*} [Field K]
    (S T : ValuationSubring K) (h : S = T) : S ≃+* T where
  toFun x := ⟨x.val, by rw [← h]; exact x.property⟩
  invFun x := ⟨x.val, by rw [h]; exact x.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
section
variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]
variable [Algebra R A] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
variable [SMulCommClass R A K] [IsDedekindDomain A] [IsFractionRing A K]
variable (H : IsDedekindDomain.HeightOneSpectrum A) (T : ValuationSubring K)
variable [Algebra R T] [Algebra T K] [IsScalarTower R T K] [SMulCommClass R T K]
end
end
end QEC.Coding.AlgebraicGeometry


