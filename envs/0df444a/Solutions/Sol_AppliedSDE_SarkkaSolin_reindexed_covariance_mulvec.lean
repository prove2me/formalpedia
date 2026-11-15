-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.reindexed_covariance_mulvec
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:30:55.70705+00:00
-- url     : https://prove2.me/submissions/9ecf1885-ef9c-4676-bf45-1c22babf37de

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix

/-- Matrix-vector multiplication is preserved by simultaneous row/column
reindexing along a finite equivalence. -/
theorem solution
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : Matrix ι ι ℝ) (e : κ ≃ ι) (z : ι → ℝ) :
    (C.submatrix e e).mulVec (z ∘ e) = (C.mulVec z) ∘ e := by
  rw [Matrix.submatrix_mulVec_equiv]
  simp [Function.comp_def]
