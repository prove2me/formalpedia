-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_LocalizedPrime
-- name    : QEC_Coding_AlgebraicGeometry_Differents_LocalizedPrime
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:14:17.324991+00:00
-- url     : https://prove2.me/theorems/982ce864-8f78-4259-a37d-8270b66b626e
-- title:
--   Localized Prime
-- statement:
--   Definitions and structural lemmas for Localized Prime, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/LocalizedPrime.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_Localization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_LocalIntegralClosureFree
import Mathlib.RingTheory.Localization.AtPrime.Extension
import Mathlib.RingTheory.Localization.Integral
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open F256GarciaStichtenoth
noncomputable section
noncomputable def localizedIntegralClosureMap
    (B Bm L : Type*)
    [CommRing B] [CommRing Bm] [CommRing L]
    [Algebra B Bm] [Algebra B L] [Algebra Bm L]
    [IsScalarTower B Bm L] :
    integralClosure B L →+* integralClosure Bm L where
  toFun x := ⟨x, x.property.tower_top⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
end
end QEC.Coding.AlgebraicGeometry


