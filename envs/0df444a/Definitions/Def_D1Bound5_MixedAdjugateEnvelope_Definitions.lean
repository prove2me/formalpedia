-- Prove2me | Definitions.Def_D1Bound5_MixedAdjugateEnvelope_Definitions
-- name    : D1Bound5_MixedAdjugateEnvelope_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:26:35.646439+00:00
-- url     : https://prove2.me/theorems/a0a3a2e6-1b8c-4488-8156-50a85db9342c
-- title:
--   Mixed Adjugate Envelope
-- statement:
--   Nonnegative symmetric entrywise envelope for mixed adjugate errors. The named objects in this bundle include `mixedAdjEnvelope`.
-- source:
--   D1Bound5/MixedAdjugateEnvelope.lean, lines 9-12, SHA-256 f452ef49f0d5283120370edce69efeffabb48f22241346c2ec9821c339c43131. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5

/-- Nonnegative symmetric entrywise envelope for mixed adjugate errors. -/
noncomputable def mixedAdjEnvelope (i j : Fin 4) : ℝ :=
  if i = j then (if i = 0 then 1/40 else 7/100)
  else if i = 0 ∨ j = 0 then 53/1000 else 47/1000









end D1Bound5
end


