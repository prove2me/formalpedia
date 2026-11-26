-- Prove2me | Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
-- name    : FourierJacobi_Algebra_UnitaryParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:43:05.97455+00:00
-- url     : https://prove2.me/theorems/089ce25d-4651-5b2a-8645-f582b63f1e43
-- title:
--   Unitary Parameters
-- statement:
--   Definitions and structural lemmas for Unitary Parameters, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryParameters.lean

import Definitions.Def_FourierJacobi_Algebra_EulerFactors
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
set_option autoImplicit false
namespace FourierJacobi
namespace Algebra
noncomputable def inverseSqrt (q : ℝ) : ℝ := (Real.sqrt q)⁻¹
end Algebra
end FourierJacobi


