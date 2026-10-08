-- Prove2me | Definitions.Def_ZetaNine_CoefficientMapMatrix
-- name    : ZetaNine_CoefficientMapMatrix
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-04T13:12:16.929243+00:00
-- url     : https://prove2.me/theorems/81dc9962-744c-4b2c-b4c2-2a67fb50ec61
-- title:
--   The actual monomial-row F matrix and selected rational inverse
-- statement:
--   Define the genuine F monomial rows and five actual output columns, the two selected integer directions B and rho9, and their actual rational inverse multiplier on Even n>=2. All five original Definition values remain fixed; no invertibility or sum premise is added.
-- source:
--   Actual frozen native CoefficientMapMatrix SHA256 a4bf1766c8bbcc1f2f83af27594ba10b3dfcd4e55058f10ccc4d4b25cb9c6d99

import Definitions.Def_ZetaNine_CoefficientMapKernelBridge
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
open Polynomial

namespace ZetaNine.CoefficientMapMatrix

open CoefficientMapAggregate CoefficientMapKernelBridge

def actualFMatrix (n : ℕ) : Matrix (Fin 5) (Fin 5) ℚ :=
  fun i j => aggregate n (X ^ i.val) j

/-- The genuine two selected output directions are B and rho9. -/
def selectionMatrix : Matrix (Fin 2) (Fin 5) ℚ :=
  fun i j => if i = 0 then (if j = 0 then 1 else 0) else (if j = 4 then 1 else 0)

def selectedIntegerPair (b a : ℤ) : Fin 2 → ℚ :=
  fun i => if i = 0 then (b : ℚ) else (a : ℚ)

def selectedIntegerOutput (b a : ℤ) : Fin 5 → ℚ :=
  fun j => if j = 0 then (b : ℚ) else if j = 4 then (a : ℚ) else 0

def selectedIntegerMultiplier (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b a : ℤ) : ℚ[X] :=
  inverseMultiplier n hn2 hn (selectedIntegerOutput b a)

end ZetaNine.CoefficientMapMatrix


