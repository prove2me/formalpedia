-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:38:33.421444+00:00
-- url     : https://prove2.me/theorems/cf2cd3aa-384a-456d-b113-971e9a79aca0
-- title:
--   Norm
-- statement:
--   Definitions and structural lemmas for Norm, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/Norm.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_FiniteImage
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
noncomputable def cyclicBMatrix {K : Type*} [Field K]
    (r : Rank) (y : K) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank) K := by
  cases r with
  | three =>
      change Matrix (Fin 3) (Fin 3) K
      exact 1 - !![0, 1, 0; 0, 0, 1; (1 + y)⁻¹, 0, 0]
  | four =>
      change Matrix (Fin 4) (Fin 4) K
      exact 1 - !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1;
        (1 + y)⁻¹, 0, 0, 0]
noncomputable def cartwrightStegerNormUnit (P : BasePrime) (r : Rank) :
    (SplittingFunctionField P r)ˣ :=
  Units.mk0 (splittingY P r / (1 + splittingY P r))
    (div_ne_zero (splittingY_ne_zero P r) (onePlusY_ne_zero P r))
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


