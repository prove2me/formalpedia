-- Prove2me | Definitions.Def_FourierJacobi_Algebra_Intertwiner
-- name    : FourierJacobi_Algebra_Intertwiner
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:40:26.048445+00:00
-- url     : https://prove2.me/theorems/26ac57f4-d644-5dd8-ad29-4b2f1b606d21
-- title:
--   Intertwiner
-- statement:
--   Definitions and structural lemmas for Intertwiner, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Intertwiner.lean

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
set_option autoImplicit false
namespace FourierJacobi
open Matrix
variable {K : Type*} [Field K]
def intertwinerMatrix (q r : K) : Matrix (Fin 2) (Fin 2) K :=
  !![(1 - q⁻¹) * r / (1 - r), 1;
      q⁻¹, (1 - q⁻¹) / (1 - r)]
def specialVector (q : K) : Fin 2 → K := ![1, -q⁻¹]
noncomputable def compactGram (q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / (q + 1), 0; 0, q / (q + 1)]
end FourierJacobi


