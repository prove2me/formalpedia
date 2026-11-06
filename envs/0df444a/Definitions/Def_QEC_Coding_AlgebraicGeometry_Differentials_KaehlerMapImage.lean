-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_KaehlerMapImage
-- name    : QEC_Coding_AlgebraicGeometry_Differentials_KaehlerMapImage
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:05:22.034207+00:00
-- url     : https://prove2.me/theorems/a011e8aa-59a2-4092-8586-ba3f18bbd984
-- title:
--   Kaehler Map Image
-- statement:
--   Definitions and structural lemmas for Kaehler Map Image, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/KaehlerMapImage.lean

import Mathlib.RingTheory.Kaehler.Basic
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
noncomputable section
variable (R A B K : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing K]
variable [Algebra R A] [Algebra R B] [Algebra R K]
variable [Algebra A B] [Algebra B K] [Algebra A K]
variable [IsScalarTower R A B] [IsScalarTower R B K] [IsScalarTower R A K]
variable [IsScalarTower A B K]
variable [SMulCommClass R A B] [SMulCommClass R A K] [SMulCommClass R B K]
end
end QEC.Coding.AlgebraicGeometry


