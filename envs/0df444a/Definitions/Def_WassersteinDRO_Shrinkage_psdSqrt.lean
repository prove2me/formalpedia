-- Prove2me | Definitions.Def_WassersteinDRO_Shrinkage_psdSqrt
-- name    : WassersteinDRO_Shrinkage_psdSqrt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:44:29.84677+00:00
-- url     : https://prove2.me/theorems/e9b4dd32-e1fd-4f35-ba9e-4bf771c162db
-- title:
--   Positive-semidefinite square root of a matrix
-- statement:
--   For a positive semidefinite matrix $A$, $\mathrm{psdSqrt}(A)$ denotes the unique positive
--   semidefinite matrix $B$ with $BB = A$ (the $\Sigma^{1/2}$ notation used throughout the paper).
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, INFORMS TutORials 2019, notation used from eq. (8), p. 8, onward

import Mathlib

open Classical

namespace WassersteinDRO.Shrinkage

/-- The positive-semidefinite square root of a matrix, `Σ^{1/2}`. Redefined locally in this
chapter's own namespace, matching `02-gelbrich`'s definition of the same name: `02-gelbrich`
is not yet a published mission, so a draft item cannot import another draft
(`CAPTAIN_ADDENDUM_WAVE2.md`, rule 5). -/
noncomputable def psdSqrt {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) :
    Matrix n n ℝ :=
  if h : ∃ B : Matrix n n ℝ, B.PosSemidef ∧ B * B = A then h.choose else 0

end WassersteinDRO.Shrinkage


