-- Prove2me | Definitions.Def_Eden_SingularValues
-- name    : Eden_SingularValues
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:17:08.526833+00:00
-- url     : https://prove2.me/theorems/48d568ad-72b4-5581-b987-06889af3a0c5
-- title:
--   Singular Values
-- statement:
--   Definitions and structural lemmas for Singular Values, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValues.lean

import Definitions.Def_Eden_DerivativeDecomposition
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
set_option autoImplicit true
noncomputable section
open Polynomial
namespace Eden
def orthogonalDiagonalMap (U V : PhaseSpace ≃ₗᵢ[ℝ] PhaseSpace) (d : PhaseSpace) :
    PhaseSpace →ₗ[ℝ] PhaseSpace :=
  U.toLinearMap ∘ₗ diagonalLinear d ∘ₗ V.symm.toLinearMap
end Eden


