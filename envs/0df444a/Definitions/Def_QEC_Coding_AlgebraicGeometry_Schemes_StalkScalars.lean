-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_StalkScalars
-- name    : QEC_Coding_AlgebraicGeometry_Schemes_StalkScalars
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:07:34.015213+00:00
-- url     : https://prove2.me/theorems/67e6d047-e4c8-4fba-afc0-7f0cc97a2404
-- title:
--   Stalk Scalars
-- statement:
--   Definitions and structural lemmas for Stalk Scalars, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/StalkScalars.lean

import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Scheme
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
noncomputable section
def schemeStalkScalar (R : CommRingCat) (X : Scheme)
    (f : X ⟶ Spec R) (x : X) : R →+* X.presheaf.stalk x :=
  (f.stalkMap x).hom.comp (StructureSheaf.toStalk R (f x)).hom
end
end QEC.Coding.AlgebraicGeometry


