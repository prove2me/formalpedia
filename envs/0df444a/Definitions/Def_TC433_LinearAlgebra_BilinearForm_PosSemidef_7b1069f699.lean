-- Prove2me | Definitions.Def_TC433_LinearAlgebra_BilinearForm_PosSemidef_7b1069f699
-- name    : TC433_LinearAlgebra_BilinearForm_PosSemidef_7b1069f699
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:13:48.207665+00:00
-- url     : https://prove2.me/theorems/9165472e-d884-48ee-b03a-dfacb04889c4
-- title:
--   TauCeti: LinearAlgebra / BilinearForm / PosSemidef
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.LinearAlgebra.BilinearForm.PosSemidef for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/LinearAlgebra/BilinearForm/PosSemidef.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Positive-semidefinite bilinear forms

This file records a pointwise characterization of positive semidefiniteness for symmetric
bilinear forms. It converts `IsPosSemidef` into diagonal nonnegativity, the form consumed by
quadratic-form signature criteria and other pointwise positivity arguments.

## Main results

* `LinearMap.BilinForm.isPosSemidef_iff_forall_nonneg`: a symmetric bilinear form is
  positive-semidefinite exactly when its diagonal values are nonnegative.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace LinearMap.BilinForm

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [LE R]

/-- A symmetric bilinear form is positive-semidefinite if and only if its values on all vectors
are nonnegative. -/
@[grind =]
theorem isPosSemidef_iff_forall_nonneg (B : LinearMap.BilinForm R M) (hB : B.IsSymm) :
    B.IsPosSemidef ↔ ∀ x, 0 ≤ B x x := by
  rw [LinearMap.BilinForm.isPosSemidef_def, LinearMap.BilinForm.isNonneg_def]
  simp only [hB, true_and]

end LinearMap.BilinForm


