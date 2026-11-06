-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_FinitePlaceDivisor
-- name    : QEC_Coding_AlgebraicGeometry_Divisors_FinitePlaceDivisor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:34:29.865679+00:00
-- url     : https://prove2.me/theorems/413a6c71-6899-48c3-a502-7a068421a14f
-- title:
--   Finite Place Divisor
-- statement:
--   Definitions and structural lemmas for Finite Place Divisor, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/FinitePlaceDivisor.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrement
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped BigOperators
noncomputable section
namespace GlobalPlace
variable {k F ι : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]
noncomputable def finitePlaceDivisor [Fintype ι]
    (P : ι → GlobalPlace k F) : Divisor (GlobalPlace k F) :=
  ∑ i : ι, placeDivisor (P i)
end GlobalPlace
end
end QEC.Coding.AlgebraicGeometry


