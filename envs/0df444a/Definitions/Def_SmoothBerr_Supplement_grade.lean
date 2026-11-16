-- Prove2me | Definitions.Def_SmoothBerr_Supplement_grade
-- name    : SmoothBerr_Supplement_grade
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:54:11.937713+00:00
-- url     : https://prove2.me/theorems/861f8774-27ae-43b1-8619-59c96f26a42d
-- title:
--   Grade of $A$ with respect to $b$ (Definition 6.6)
-- statement:
--   The **grade** of a matrix $A\in\mathbb R^{n\times n}$ with respect to a vector $b\in\mathbb R^n$ is the dimension
--   $$
--   d:=\dim R_n(A,b)
--   $$
--   of the right-side Krylov subspace of degree $n$, the largest dimension a right-side Krylov subspace of $A$ started from $b$ can reach. It bounds the number of matvecs in Theorem 6.7.
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), Definition 6.6, p.18

import Mathlib
import Definitions.Def_SmoothBerr_Supplement_rightKrylov

namespace SmoothBerr.Supplement

/-- The **grade** of `A` with respect to `b` (Dereziński, Mahoney, Meyer, Musco, *From smoothed
analysis to backward error: The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256
9575cd20…, Definition 6.6, p.18): `d := dim R_n(A, b)`. -/
noncomputable def grade {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) : ℕ :=
  Module.finrank ℝ (rightKrylov A b n)

end SmoothBerr.Supplement


