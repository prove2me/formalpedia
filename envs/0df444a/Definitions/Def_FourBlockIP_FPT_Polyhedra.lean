-- Prove2me | Definitions.Def_FourBlockIP_FPT_Polyhedra
-- name    : FourBlockIP_FPT_Polyhedra
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:32.018475+00:00
-- url     : https://prove2.me/theorems/3d83dcc5-62ec-4bf0-978c-977105a1240b
-- title:
--   Integral polytopes, IDP and free-width n-fold matrix classes
-- statement:
--   An integral polytope is the convex hull of a finite set of integer vectors, including the empty hull. Its affine dimension is the dimension of the span of point differences. Vertices are extreme points. A set $Q$ has the integer decomposition property if
--
--   $$z\in kQ\cap\mathbb Z^n\ \Longrightarrow\ z=\sum_{j=1}^k z_j,\quad z_j\in Q\cap\mathbb Z^n,$$
--
--   for every natural $k$, including zero. Dilation is the image of the set under scalar multiplication, so zero times an empty set is empty and zero times a nonempty set is $\{0\}$.
--
--   A matrix class has IDP after an $M$-dilation when every polyhedron $M\{x\ge0:Ax=b\}$ has IDP, for every member and every integer right-hand side. Closure under inverting columns means closure under negating one whole column. The n-fold class contains matrices with any number of blocks and independently chosen block widths $t_i$, with $r$ global rows and $s$ rows per local block. The $B_i,D_i$ coefficients are bounded by $\Delta$. The row and column identifications enforce the displayed order; they do not add arbitrary permutations.
--
--   These notions supply the polyhedral and matrix-class layer of Lemmas 3–5 without requiring full dimension or nonempty polytopes.
-- source:
--   Martin Koutecký, Alexandra Lassota, Koen Ligthart, 4-Block Integer Programming is in FPT, STOC 2027 submission #392 (October 2026), p. 5, Lemma 3; pp. 6–7, IDP, dilation, n-fold and column inversion definitions; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/392.pdf

import Mathlib
import Definitions.Def_FourBlockIP_FPT_Data

open scoped Pointwise

namespace FourBlockIP.FPT

/-- Convex hull of finitely many lattice points, including the empty polytope. -/
def IntegralPolytope {n : ℕ} (P : Set (Fin n → ℝ)) : Prop :=
  ∃ V : Finset (Fin n → ℤ), P = convexHull ℝ (castVec '' (V : Set (Fin n → ℤ)))

noncomputable def affDim {n : ℕ} (P : Set (Fin n → ℝ)) : ℕ :=
  Module.finrank ℝ (vectorSpan ℝ P)

def IsVertex {n : ℕ} (x : Fin n → ℝ) (Q : Set (Fin n → ℝ)) : Prop :=
  x ∈ Q.extremePoints ℝ

/-- IDP, p. 6. Scaling is the image under multiplication, even at k=0:
zero times a nonempty set is {0}; zero times the empty set is empty. -/
def HasIDP {n : ℕ} (Q : Set (Fin n → ℝ)) : Prop :=
  ∀ k : ℕ, ∀ x : Fin n → ℤ, castVec x ∈ (k : ℝ) • Q →
    ∃ xs : Fin k → (Fin n → ℤ),
      (∀ j, castVec (xs j) ∈ Q) ∧ x = ∑ j, xs j

abbrev SizedMatrix := Σ m : ℕ, Σ n : ℕ, Matrix (Fin m) (Fin n) ℤ
abbrev MatrixClass := Set SizedMatrix

def invertColumn {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (j : Fin n) :
    Matrix (Fin m) (Fin n) ℤ := fun a b => if b = j then - A a b else A a b

def ClosedUnderInvertingColumns (cls : MatrixClass) : Prop :=
  ∀ m n (A : Matrix (Fin m) (Fin n) ℤ), ⟨m,n,A⟩ ∈ cls →
    ∀ j, (⟨m,n,invertColumn A j⟩ : SizedMatrix) ∈ cls

def IDPAfterDilation (cls : MatrixClass) (M : ℕ) : Prop :=
  ∀ m n (A : Matrix (Fin m) (Fin n) ℤ), ⟨m,n,A⟩ ∈ cls →
    ∀ b : Fin m → ℤ, HasIDP ((M : ℝ) •
      {x : Fin n → ℝ | (∀ j, 0 ≤ x j) ∧
        (fun i => ∑ j, (A i j : ℝ) * x j) = castVec b})

/-- The n-fold class (p. 6), with any number of blocks and free widths t_i.
The two equivalences only identify the displayed ordered row/column types with
Fin; their value equations enforce the displayed order, without extra permutations. -/
def nfold (r s delta : ℕ) : MatrixClass :=
  {a | ∃ (k : ℕ) (width : Fin k → ℕ)
    (B : (i : Fin k) → Matrix (Fin r) (Fin (width i)) ℤ)
    (D : (i : Fin k) → Matrix (Fin s) (Fin (width i)) ℤ),
    (∀ i q j, |B i q j| ≤ (delta : ℤ)) ∧
    (∀ i q j, |D i q j| ≤ (delta : ℤ)) ∧
    ∃ (er : (Fin r ⊕ (Fin k × Fin s)) ≃ Fin a.1)
      (ec : (Σ i : Fin k, Fin (width i)) ≃ Fin a.2.1),
      (∀ q, (er (.inl q)).val = q.val) ∧
      (∀ i q, (er (.inr (i,q))).val = r + i.val * s + q.val) ∧
      (∀ i j, (ec ⟨i,j⟩).val =
        (∑ h ∈ Finset.univ.filter (fun h : Fin k => h < i), width h) + j.val) ∧
      ∀ row col, a.2.2 (er row) (ec col) =
        match row with
        | .inl q => B col.1 q col.2
        | .inr (i,q) => if h : col.1 = i then D i q (h ▸ col.2) else 0}

end FourBlockIP.FPT


