-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_PrincipalOrder
-- name    : QEC_Coding_AlgebraicGeometry_Divisors_PrincipalOrder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:42:36.780101+00:00
-- url     : https://prove2.me/theorems/16937b3e-b121-40cc-a9d4-f91f8f1c6368
-- title:
--   Principal Order
-- statement:
--   Definitions and structural lemmas for Principal Order, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/PrincipalOrder.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
namespace GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
def principalOrder (f : Fˣ) : GlobalPlace k F → ℤ := fun P => order P f
end GlobalPlace
end QEC.Coding.AlgebraicGeometry


