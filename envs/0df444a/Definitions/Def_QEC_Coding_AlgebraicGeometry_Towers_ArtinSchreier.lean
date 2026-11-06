-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ArtinSchreier
-- name    : QEC_Coding_AlgebraicGeometry_Towers_ArtinSchreier
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:08:51.079503+00:00
-- url     : https://prove2.me/theorems/4d5fd418-559e-405e-a2d8-5f82fb771fb1
-- title:
--   Artin Schreier
-- statement:
--   Definitions and structural lemmas for Artin Schreier, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ArtinSchreier.lean

import Mathlib
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.ArtinSchreier
open scoped WithZero BigOperators
open Polynomial
variable {F : Type*} [Field F]
noncomputable def artinSchreierPolynomial (u : F) : F[X] :=
  X ^ 32 + X - C u
end QEC.Coding.AlgebraicGeometry.ArtinSchreier


