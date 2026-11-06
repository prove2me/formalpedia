-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ArtinSchreierCancellation
-- name    : QEC_Coding_AlgebraicGeometry_Towers_ArtinSchreierCancellation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:04:35.438211+00:00
-- url     : https://prove2.me/theorems/bd3f0857-f93e-4802-a080-116e3f001a99
-- title:
--   Artin Schreier Cancellation
-- statement:
--   Definitions and structural lemmas for Artin Schreier Cancellation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ArtinSchreierCancellation.lean

import Mathlib.FieldTheory.Perfect
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
variable [Algebra (Polynomial F256) K] [Algebra (RatFunc F256) K]
variable [IsScalarTower (Polynomial F256) (RatFunc F256) K]
variable [_root_.FunctionField F256 K]
variable [Algebra.IsSeparable (RatFunc F256) K]
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


