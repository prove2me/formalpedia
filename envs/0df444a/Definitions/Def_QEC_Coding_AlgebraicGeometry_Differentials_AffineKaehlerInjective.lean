-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerInjective
-- name    : QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerInjective
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:06:40.021121+00:00
-- url     : https://prove2.me/theorems/f4b33006-ccf5-4142-903f-d10ba521fd81
-- title:
--   Affine Kaehler Injective
-- statement:
--   Definitions and structural lemmas for Affine Kaehler Injective, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineKaehlerInjective.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerImage
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.Algebra.GroupWithZero.Action.Units
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
noncomputable section
variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]
variable [Algebra R A] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
variable [IsDedekindDomain A] [IsFractionRing A K] [Algebra.EssFiniteType R A]
variable (H : IsDedekindDomain.HeightOneSpectrum A) (T : ValuationSubring K)
variable [Algebra R T] [Algebra T K] [IsScalarTower R T K]
end
end QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
noncomputable section
section
variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]
variable [Algebra R A] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
variable [SMulCommClass R A K] [IsDedekindDomain A] [IsFractionRing A K]
variable (H : IsDedekindDomain.HeightOneSpectrum A) (T : ValuationSubring K)
variable [Algebra R T] [Algebra T K] [IsScalarTower R T K] [SMulCommClass R T K]
end
end
end QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
noncomputable section
section localization
variable (R A B K : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing K]
variable [Algebra R A] [Algebra R B] [Algebra R K]
variable [Algebra A B] [Algebra B K] [Algebra A K]
variable [IsScalarTower R A B] [IsScalarTower R B K] [IsScalarTower R A K]
variable [IsScalarTower A B K]
variable [SMulCommClass R A B] [SMulCommClass R A K] [SMulCommClass R B K]
end localization
end
end QEC.Coding.AlgebraicGeometry


