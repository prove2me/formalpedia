-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_TrivialFieldExtension
-- name    : QEC_Coding_AlgebraicGeometry_Differents_TrivialFieldExtension
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:27:59.451826+00:00
-- url     : https://prove2.me/theorems/b76be696-0990-4522-92a8-a73fa1a7eced
-- title:
--   Trivial Field Extension
-- statement:
--   Definitions and structural lemmas for Trivial Field Extension, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/TrivialFieldExtension.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrder
import Mathlib.RingTheory.DedekindDomain.Different
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
noncomputable section
variable (B C K L : Type*) [CommRing B] [CommRing C] [Field K] [Field L]
    [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [Algebra B C] [Algebra C L] [IsFractionRing C L] [IsScalarTower B C L]
    [Module.IsTorsionFree B C] [Module.Finite B C]
    [Algebra.IsSeparable K L]
end
end QEC.Coding.AlgebraicGeometry


