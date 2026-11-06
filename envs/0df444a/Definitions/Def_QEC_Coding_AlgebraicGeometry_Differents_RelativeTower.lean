-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_RelativeTower
-- name    : QEC_Coding_AlgebraicGeometry_Differents_RelativeTower
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:29:00.609205+00:00
-- url     : https://prove2.me/theorems/df7fa483-6392-4e50-aa3c-adea3285153f
-- title:
--   Relative Tower
-- statement:
--   Definitions and structural lemmas for Relative Tower, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/RelativeTower.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_ExponentTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_TrivialFieldExtension
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


