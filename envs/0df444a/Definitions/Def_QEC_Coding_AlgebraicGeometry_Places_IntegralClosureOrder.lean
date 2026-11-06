-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralClosureOrder
-- name    : QEC_Coding_AlgebraicGeometry_Places_IntegralClosureOrder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:18:48.175646+00:00
-- url     : https://prove2.me/theorems/301e9eb1-74fb-4236-8394-58a7830c5bda
-- title:
--   Integral Closure Order
-- statement:
--   Definitions and structural lemmas for Integral Closure Order, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/IntegralClosureOrder.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ArtinSchreierOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Mathlib.NumberTheory.RamificationInertia.Basic
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
noncomputable section
variable {k : Type*} [Field k] [Finite k]
noncomputable def integralClosurePlace
    {O L : Type*} [CommRing O] [_root_.Field L] [Algebra k L]
    [Algebra O L] [IsDedekindDomain (integralClosure O L)]
    [IsFractionRing (integralClosure O L) L]
    (H : IsDedekindDomain.HeightOneSpectrum (integralClosure O L)) :
    GlobalPlace k L where
  valuation := H.valuation L
  normalized := H.valuation_surjective L
end
end QEC.Coding.AlgebraicGeometry


