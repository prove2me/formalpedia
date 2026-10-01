-- Prove2me | Definitions.Def_Yukon_a1a3aabf93c629033becc7ad
-- name    : Yukon_a1a3aabf93c629033becc7ad
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T14:37:38.039673+00:00
-- url     : https://prove2.me/theorems/b80baed0-a01e-416a-ae5e-45e49d5ab711
-- title:
--   YukonModule.ArkLib.Data.CodingTheory.BerlekampWelch.Sorries.part0
-- statement:
--   Source module ArkLib.Data.CodingTheory.BerlekampWelch.Sorries.
-- source:
--   https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/Data/CodingTheory/BerlekampWelch/Sorries.lean
--
--   provider-v8:d4f90260c3b6ac5025094abe829fdb999e418d86ac092f78e418d3f08d87ca0a
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJwcm92aWRlci12ODpkNGY5MDI2MGMzYjZhYzUwMjUwOTRhYmU4MjlmZGI5OTllNDE4ZDg2YWMwOTJmNzhlNDE4ZDNmMDhkODdjYTBhIiwiaGFzaCI6IjQ1NzY4MmMzZDUzMTVhYTg0M2VlMjZmN2M3MDQ5ODRkMzkwOTZlMDgzZGEzMjMyYzljZjExMTk1MDMyMDRjMjMiLCJraW5kIjoiZGVmaW5pdGlvbiIsInRhcmdldCI6Ill1a29uX2ExYTNhYWJmOTNjNjI5MDMzYmVjYzdhZCIsImVudmlyb25tZW50Ijp7Im1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0IiwidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIn0sInRhZyI6ImJldHRlci1jb2RlcyJ9]

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Matrix.Mul


import Init
set_option backward.isDefEq.respectTransparency.types false
/-!
  # All the sorries Berlekamp-Welch decoder relies upon.

  The sorries are related to solving linear systems of equations.
-/

variable {α : Type} {F : Type} [Field F]
variable {n m : ℕ}

/--
Noncomputable linear system solver for Berlekamp-Welch decoding.

Solves the matrix equation A·x = b for x, where:
- A is an n × m coefficient matrix
- b is a length-n RHS vector
Returning either:
- `some x` if a solution exists
- `none` if the system is inconsistent

### Parameters:
- `A : Matrix (Fin n) (Fin m) F` - Coefficient matrix with dimensions n × m
- `b : Fin n → F` - Right-hand side vector of length n

### Returns:
- `some x` where `x : Fin m → F` is a solution vector if one exists
- `none` if the system has no solution

### Behavior:
1. For consistent systems (solutions exist):
   - Returns any valid solution (chosen via `Classical.choose`)
2. For inconsistent systems (no solution):
   - Returns `none`

### Implementation Notes:
- Marked `noncomputable` because the existence check uses classical logic.
- Used internally by the Berlekamp-Welch decoder.
-/
noncomputable def linsolve (A : Matrix (Fin n) (Fin m) F) (b : Fin n → F) :
    Option (Fin m → F) := by
    classical
    exact if h : ∃ x, A.mulVec x = b then some (Classical.choose h) else none

/--
**Solution correctness theorem** for the linear system solver.

### Theorem Statement:
If `linsolve` returns `some x`, then `x` is indeed a solution to the linear system.

### Parameters:
- `A : Matrix (Fin n) (Fin m) F` - Coefficient matrix
- `b : Fin n → F` - Right-hand side vector
- `x : Fin m → F` - Candidate solution vector
- `h : linsolve A b = some x` - Proof that the solver returned this solution
-/
theorem linsolve_some {A : Matrix (Fin n) (Fin m) F} {b : Fin n → F} {x : Fin m → F}
    (h : linsolve A b = some x) : A.mulVec x = b := by
  unfold linsolve at h
  by_cases hex : ∃ x, A.mulVec x = b
  · rw [dif_pos hex] at h
    injection h with h'
    rw [← h']
    exact Classical.choose_spec hex
  · rw [dif_neg hex] at h
    cases h

/--
**Inconsistency theorem** for the linear system solver.

### Theorem Statement:
If `linsolve` returns `none`, the linear system has no solution.

### Parameters:
- `A : Matrix (Fin n) (Fin m) F` - Coefficient matrix
- `b : Fin n → F` - Right-hand side vector
- `h : linsolve A b = none` - Proof that the solver failed to find a solution
-/
theorem linsolve_none {A : Matrix (Fin n) (Fin m) F} {b : Fin n → F}
    (h : linsolve A b = none) : ¬∃ x, A.mulVec x = b := by
  unfold linsolve at h
  by_cases hex : ∃ x, A.mulVec x = b
  · rw [dif_pos hex] at h
    cases h
  · exact hex


