-- Prove2me | Definitions.Def_D1Bound5_ProductFiveBlockDet_Definitions
-- name    : D1Bound5_ProductFiveBlockDet_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:39:10.5307+00:00
-- url     : https://prove2.me/theorems/1cf9d48a-db8a-46fc-812b-127f95a22367
-- title:
--   Product Five Block Det
-- statement:
--   The five-by-five block matrix in equation (integrated-3), indexed by Fin 4 ⊕ Fin 1. All products are bilinear, without complex conjugation. The named objects in this bundle include `productFiveIntegratedBlock`.
-- source:
--   D1Bound5/ProductFiveBlockDet.lean, lines 49-59, SHA-256 10e7a7c95556fd99f1056a1878c1c35778ba742ada21bee32a4eb5948f7ada68. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open Matrix

namespace D1Bound5



/-- The five-by-five block matrix in equation (integrated-3), indexed by
Fin 4 ⊕ Fin 1. All products are bilinear, without complex conjugation. -/
noncomputable def productFiveIntegratedBlock
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (f w : Fin 4 → ℂ) (d : ℂ) :
    Matrix (Fin 4 ⊕ Fin 1) (Fin 4 ⊕ Fin 1) ℂ :=
  Matrix.fromBlocks
    (F + Matrix.of (fun i j => w i * w j))
    (fun i (_ : Fin 1) => f i + d * w i)
    (fun (_ : Fin 1) j => f j + d * w j)
    (fun (_ _ : Fin 1) => d^2)



end D1Bound5
end


