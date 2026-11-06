-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_AuxiliaryMinpoly
-- name    : QEC_Coding_AlgebraicGeometry_Towers_AuxiliaryMinpoly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:52:11.335351+00:00
-- url     : https://prove2.me/theorems/36f85ddb-0a1d-427a-873c-7f4bd3044164
-- title:
--   Auxiliary Minpoly
-- statement:
--   Definitions and structural lemmas for Auxiliary Minpoly, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/AuxiliaryMinpoly.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Galois
import Mathlib.FieldTheory.PrimitiveElement
set_option autoImplicit false
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K]
noncomputable def stepAuxiliaryPolynomial
    (x : K) : K[X] :=
  X ^ 16 + (X - C (x ^ 17))
variable [Algebra F256 K]
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


