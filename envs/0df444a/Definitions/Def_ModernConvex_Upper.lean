-- Prove2me | Definitions.Def_ModernConvex_Upper
-- name    : ModernConvex_Upper
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:41:36.608132+00:00
-- url     : https://prove2.me/theorems/91bef27f-464f-4f11-a8a3-6a8f659cae1a
-- title:
--   The Max-Cut SDP body in free upper-triangular coordinates
-- statement:
--   **Free coordinates for the Max-Cut SDP body.**
--
--   The feasible set of the Max-Cut semidefinite relaxation is $\{X\succeq0,\ X_{ii}=1\}$. It lies in the affine subspace of matrices with unit diagonal, so in the space of all symmetric matrices it has empty interior — which means the ellipsoid method cannot be run on it directly, since that method requires a full-dimensional convex body.
--
--   The diagonal constraints are therefore eliminated. A symmetric matrix with unit diagonal is determined by its entries above the diagonal, so we parametrise it by the strict upper triangle: `matOfUpper z` has entry $z_{ij}$ in positions $(i,j)$ and $(j,i)$ for $i<j$, and $1$ on the diagonal. The map $z\mapsto\texttt{matOfUpper}\,z$ is affine and injective, and the body becomes
--   $$\{z : \texttt{matOfUpper}\,z\succeq0\},$$
--   a full-dimensional set in the space of dimension $\binom n2$: the identity matrix corresponds to $z = 0$, and a small perturbation of $0$ stays positive definite.
--
--   `upperOff z` is the off-diagonal part, so that `matOfUpper z = 1 + upperOff z` — the form in which the quadratic form, and hence the interior statement, is proved.
-- source:
--   Elimination of the diagonal constraints X_ii = 1 of the MAXCUT SDP, Ben-Tal & Nemirovski (4.3.15), p. 170, so that the body becomes full dimensional for Bubeck arXiv:1405.4980v2, Thm 2.4.

import Mathlib

/-!
# Free coordinates for the Max-Cut SDP body: the strict upper triangle

The primal body `{X : X ⪰ 0, X_ii = 1}` lies in the affine subspace of matrices with unit
diagonal, so it has empty interior in the space of all matrices and cannot be a convex body in
the sense required by the ellipsoid method. The diagonal constraints are therefore eliminated: a
symmetric matrix with unit diagonal is determined by its strict upper triangle.

`matOfUpper z` is the symmetric matrix with `z` in positions `(i,j)` and `(j,i)` for `i < j` and
`1` on the diagonal; `upperOff z` is its off-diagonal part.
-/

open Matrix
open scoped BigOperators MatrixOrder

namespace ModernConvex.Relaxations

/-- The index type of strict upper-triangular positions. -/
def UpIdx (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- The symmetric matrix with unit diagonal determined by its strict upper triangle. -/
noncomputable def matOfUpper {n : ℕ} (z : UpIdx n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if h : i < j then z ⟨(i, j), h⟩
    else if h : j < i then z ⟨(j, i), h⟩ else 1

/-- `matOfUpper z` is symmetric. -/
theorem matOfUpper_symm {n : ℕ} (z : UpIdx n → ℝ) (i j : Fin n) :
    matOfUpper z i j = matOfUpper z j i := by
  simp only [matOfUpper, Matrix.of_apply]
  by_cases hij : i < j
  · have hji : ¬ j < i := not_lt.mpr (le_of_lt hij)
    rw [dif_pos hij, dif_neg hji, dif_pos hij]
  · by_cases hji : j < i
    · rw [dif_neg hij, dif_pos hji, dif_neg hij, dif_pos hji]
    · have hEq : i = j := le_antisymm (not_lt.mp hji) (not_lt.mp hij)
      subst hEq
      rw [dif_neg hij, dif_neg hji]

/-- The diagonal of `matOfUpper z` is one. -/
@[simp] theorem matOfUpper_diag {n : ℕ} (z : UpIdx n → ℝ) (i : Fin n) :
    matOfUpper z i i = 1 := by
  simp only [matOfUpper, Matrix.of_apply]
  have h : ¬ i < i := lt_irrefl i
  rw [dif_neg h, dif_neg h]

/-- `matOfUpper z` is symmetric, as a Hermitian matrix. -/
theorem matOfUpper_isHermitian {n : ℕ} (z : UpIdx n → ℝ) :
    (matOfUpper z).IsHermitian := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  exact (matOfUpper_symm z i j).symm

/-- The off-diagonal part of `matOfUpper z`. -/
noncomputable def upperOff {n : ℕ} (z : UpIdx n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if i = j then 0 else matOfUpper z i j

@[simp] theorem upperOff_diag {n : ℕ} (z : UpIdx n → ℝ) (i : Fin n) : upperOff z i i = 0 := by
  simp [upperOff]

/-- `matOfUpper z = 1 + upperOff z`. -/
theorem matOfUpper_eq_one_add {n : ℕ} (z : UpIdx n → ℝ) :
    matOfUpper z = 1 + upperOff z := by
  ext i j
  by_cases h : i = j
  · subst h
    rw [matOfUpper_diag, Matrix.add_apply, Matrix.one_apply_eq, upperOff_diag]
    ring
  · rw [Matrix.add_apply, Matrix.one_apply_ne h, upperOff, Matrix.of_apply, if_neg h]
    ring

end ModernConvex.Relaxations


