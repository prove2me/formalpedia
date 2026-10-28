-- Prove2me | Definitions.Def_OAI_PiExponent_FormalInterpolation_coordinateSliceRestriction
-- name    : OAI_PiExponent_FormalInterpolation_coordinateSliceRestriction
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-25T08:09:43.293976+00:00
-- url     : https://prove2.me/theorems/fc754f41-a751-4de3-9187-ef5d00b9be21
-- title:
--   Restriction to an affine coordinate slice
-- statement:
--   The polynomial algebra map retaining coordinates in A, reindexed by e, and substituting constants for complementary coordinates.

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.EquivFin

/-- Keep the coordinates in A, indexed by e, and fix the other coordinates at c. -/
noncomputable def OAI.PiExponent.FormalInterpolation.coordinateSliceRestriction
    {d : Nat} (A : Finset (Fin d)) (e : Fin A.card ≃ A)
    (c : Fin d → Complex) :
    MvPolynomial (Fin d) Complex →ₐ[Complex]
      MvPolynomial (Fin A.card) Complex := by
  classical
  exact MvPolynomial.aeval (fun i =>
    if hi : i ∈ A then MvPolynomial.X (e.symm ⟨i, hi⟩)
    else MvPolynomial.C (c i))


