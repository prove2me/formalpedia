-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticDifferent
-- name    : QEC_Coding_AlgebraicGeometry_Towers_QuadraticDifferent
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:53:55.467168+00:00
-- url     : https://prove2.me/theorems/b866f52d-8c10-45be-be62-5cddc4849f75
-- title:
--   Quadratic Different
-- statement:
--   Definitions and structural lemmas for Quadratic Different, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticDifferent.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_Transport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralClosureOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticLocalModels
set_option autoImplicit false
open IntermediateField
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K L : Type*} [_root_.Field K] [_root_.Field L]
  [Algebra F256 K] [Algebra K L]
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


