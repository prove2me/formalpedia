-- Prove2me | Definitions.Def_D1Bound5_DeterminantNormalization_Definitions
-- name    : D1Bound5_DeterminantNormalization_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:23:50.10599+00:00
-- url     : https://prove2.me/theorems/5638bcf1-c438-44c9-a844-fef3008fbfc3
-- title:
--   Determinant Normalization
-- statement:
--   A matrix with its rows and columns multiplied by prescribed roots. The construction also permits zero roots. The named objects in this bundle include `scaledRootMatrix`, `normalizedRootError`.
-- source:
--   D1Bound5/DeterminantNormalization.lean, lines 12-16, SHA-256 196cc874899f4fdc78056f81619aaf82ead08fc052cbd1257526b60749c0f0be; D1Bound5/DeterminantNormalization.lean, lines 18-21, SHA-256 196cc874899f4fdc78056f81619aaf82ead08fc052cbd1257526b60749c0f0be. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open scoped BigOperators
open Matrix

namespace D1Bound5

/-- A matrix with its rows and columns multiplied by prescribed roots.
The construction also permits zero roots. -/
def scaledRootMatrix {R n : Type*} [CommRing R] (u : n → R)
    (M : Matrix n n R) : Matrix n n R :=
  fun i j => u i * M i j * u j

/-- Correction term after subtracting the rank-one matrix of the entries. -/
def normalizedRootError {R n : Type*} [CommRing R] (a u : n → R)
    (M : Matrix n n R) : Matrix n n R :=
  fun i j => scaledRootMatrix u M i j - a i * a j















end D1Bound5
end


