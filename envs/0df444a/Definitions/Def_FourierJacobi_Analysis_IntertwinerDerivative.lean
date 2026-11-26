-- Prove2me | Definitions.Def_FourierJacobi_Analysis_IntertwinerDerivative
-- name    : FourierJacobi_Analysis_IntertwinerDerivative
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:49:05.681384+00:00
-- url     : https://prove2.me/theorems/8d4bbf47-415b-4438-99d5-1d578aae369b
-- title:
--   Intertwiner Derivative
-- statement:
--   Definitions and structural lemmas for Intertwiner Derivative, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/IntertwinerDerivative.lean

import Definitions.Def_FourierJacobi_Algebra_Intertwiner
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
set_option autoImplicit false
namespace FourierJacobi
namespace Analysis
noncomputable def inducingPower (q s : ℝ) : ℝ :=
  Real.exp ((-2 * Real.log q) * s)
noncomputable def intertwinerFamily (q s : ℝ) :=
  intertwinerMatrix q (inducingPower q s)
end Analysis
end FourierJacobi


