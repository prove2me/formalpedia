-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureFibreDifferentialOrder
-- name    : QEC_Coding_AlgebraicGeometry_Towers_ClosureFibreDifferentialOrder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T21:08:48.27757+00:00
-- url     : https://prove2.me/theorems/0621bf5e-d803-4f47-8d4a-6c944cfb1490
-- title:
--   Closure Fibre Differential Order
-- statement:
--   Definitions and structural lemmas for Closure Fibre Differential Order, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureFibreDifferentialOrder.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_WBaseDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialPlaceTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureFibreDifferent
set_option autoImplicit false
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] closureDifferent_modelDedekind closureDifferent_modelFinite
  closureDifferent_modelFraction closureDifferent_modelTorsionFree
  fibreDifferent_baseAlgebra fibreDifferent_baseFraction fibreDifferent_baseFaithful
  fibreDifferent_baseDVR fibreDifferent_ambientAlgebra fibreDifferent_baseTower
  fibreDifferent_ambientTorsionFree
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


