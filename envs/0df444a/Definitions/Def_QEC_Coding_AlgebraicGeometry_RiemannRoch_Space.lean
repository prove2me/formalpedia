-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Space
-- name    : QEC_Coding_AlgebraicGeometry_RiemannRoch_Space
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:46:08.476318+00:00
-- url     : https://prove2.me/theorems/3a79a057-03b3-43d1-ae40-886f5c4910b8
-- title:
--   Space
-- statement:
--   Definitions and structural lemmas for Space, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/Space.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_ValuationBound
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped WithZero
namespace GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
def valuationFamily : GlobalPlace k F → Valuation F ℤᵐ⁰ := fun P => P.valuation
def riemannRochSubmodule (G : Divisor (GlobalPlace k F)) : Submodule k F :=
  ValuationBound.space valuationFamily G
noncomputable def evaluateAtNonpositive (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F)
    (f : riemannRochSubmodule G) (hGP : G P ≤ 0) : residueField P :=
  evaluateRegular P (f : F)
    ((f.property P).trans (WithZero.exp_le_exp.mpr hGP))
end GlobalPlace
end QEC.Coding.AlgebraicGeometry


