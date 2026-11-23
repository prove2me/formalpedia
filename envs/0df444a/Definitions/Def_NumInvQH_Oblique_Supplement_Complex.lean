-- Prove2me | Definitions.Def_NumInvQH_Oblique_Supplement_Complex
-- name    : NumInvQH_Oblique_Supplement_Complex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T21:36:28.361583+00:00
-- url     : https://prove2.me/theorems/1c248f3a-d34f-45f3-9e18-5240fe4897f1
-- title:
--   Complex Penrose equations and Hermitian subspaces
-- statement:
--   For a complex matrix $A$ and a matrix $P$ of the transposed shape, the Moore–Penrose predicate is the conjunction
--   $$APA=A,\qquad PAP=P,\qquad (AP)^*=AP,\qquad(PA)^*=PA.$$
--   Column spaces and null spaces are complex linear subspaces; orthogonality means $\sum_i\overline{y_i}x_i=0$ for every $y$ in the subspace. Matrix action on a subspace means its image, including when the matrix is a pseudoinverse. These definitions support the complex version of Theorem A.2, independently of the base mission's real predicate.
-- source:
--   Černý, Czichowsky & Kallsen, Numeraire-invariant quadratic hedging and mean–variance portfolio allocation, arXiv:2110.09416v4, pp. 24–25, (A.2), Theorem A.2

import Mathlib

open Matrix

namespace NumInvQH.Oblique.Supplement

/-- The four Penrose equations over the complex numbers, including both Hermitian equations. -/
def IsComplexMoorePenrose {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (P : Matrix (Fin n) (Fin m) ℂ) : Prop :=
  A * P * A = A ∧ P * A * P = P ∧ (A * P).conjTranspose = A * P ∧
    (P * A).conjTranspose = P * A

/-- Column space in complex coordinates. -/
def complexRange {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    Submodule ℂ (Fin m → ℂ) := LinearMap.range (Matrix.toLin' A)

/-- Null space in complex coordinates. -/
def complexNull {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    Submodule ℂ (Fin n → ℂ) := LinearMap.ker (Matrix.toLin' A)

/-- Hermitian orthogonal complement, without using the sup norm on coordinate functions. -/
def hermitianPerp {n : ℕ} (W : Submodule ℂ (Fin n → ℂ)) :
    Submodule ℂ (Fin n → ℂ) where
  carrier := {x | ∀ y ∈ W, star y ⬝ᵥ x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x z hx hz y hy
    simp only [Set.mem_setOf_eq] at hx hz ⊢
    rw [dotProduct_add, hx y hy, hz y hy, add_zero]
  smul_mem' := by
    intro c x hx y hy
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [dotProduct_smul, hx y hy, smul_zero]

/-- Image of a complex subspace under a matrix (not inverse image). -/
def complexImage {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (W : Submodule ℂ (Fin n → ℂ)) : Submodule ℂ (Fin m → ℂ) :=
  W.map (Matrix.toLin' A)

end NumInvQH.Oblique.Supplement


