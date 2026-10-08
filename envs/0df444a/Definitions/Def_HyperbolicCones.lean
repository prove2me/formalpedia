-- Prove2me | Definitions.Def_HyperbolicCones
-- name    : HyperbolicCones
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:14.718285+00:00
-- url     : https://prove2.me/theorems/41a9a9ca-79e5-403d-8f37-77e5fd2f25ab
-- statement:
--   This block defines a set called cone inside the real vector space Ambient of triples (X, Z, y), where X and Z are real symmetric 4×4 matrices and y is a vector in ℝ³, giving 10+10+3 = 23 real coordinates. For y in a commutative ring, qMatrix(y) is the 3×3 matrix with diagonal entries y_i²+y_{i+1}² (indices mod 3) and off-diagonal entries −y_i y_j. From it, phi(y,X) builds a 4×4 matrix in block form: its top-left entry is the trace of qMatrix(y) times the lower-right 3×3 block of X, its first row and column hold the negatives of the products of qMatrix(y) with X's first column and row (without the corner entry), and its lower-right 3×3 block is X₀₀·qMatrix(y). The function matrixValue(X,Z,y) is det(det(X)·Z − phi(y, adj(X))), where adj is the adjugate. Using symmetricCoordinates to fill symmetric matrices from independent upper-triangular entries, polynomial is this expression viewed as a real multivariate polynomial in the 23 coordinates. The base point is X=Z=identity, y=0. For a point x, linePolynomial(x) is the one-variable real polynomial obtained by substituting, for each coordinate, (base coordinate)·t − (coordinate of x) into polynomial, that is, restricting to the line through the base point direction. Finally, cone is the set of x for which every complex root t of linePolynomial(x) is real and nonnegative, meaning zero imaginary part and nonnegative real part. These are definitions only; no property of the cone is proved or asserted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/HyperbolicCones.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/HyperbolicCones.lean; bytes 16..2177
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open scoped Matrix.Norms.L2Operator

universe u

namespace Paper256

abbrev Mat (n : ℕ) (R : Type u) := Matrix (Fin n) (Fin n) R

abbrev Sym (n : ℕ) := selfAdjoint (Mat n ℝ)

instance instFiniteDimensionalSym (n : ℕ) : FiniteDimensional ℝ (Sym n) :=
  FiniteDimensional.finiteDimensional_submodule (selfAdjoint.submodule ℝ (Mat n ℝ))

abbrev Ambient := (Sym 4 × Sym 4) × (Fin 3 → ℝ)

abbrev SymIndex := {ij : Fin 4 × Fin 4 // ij.1 ≤ ij.2}

abbrev Coord := (SymIndex ⊕ SymIndex) ⊕ Fin 3

def qMatrix {R : Type u} [CommRing R] (y : Fin 3 → R) : Mat 3 R :=
  fun i j => if i = j then y i ^ 2 + y (i + 1) ^ 2 else -(y i * y j)

def phi {R : Type u} [CommRing R] (y : Fin 3 → R) (X : Mat 4 R) : Mat 4 R :=
  fun i j => Fin.cases
    (Fin.cases
      (Matrix.trace (qMatrix y * X.submatrix Fin.succ Fin.succ))
      (fun j => -(∑ k, X 0 k.succ * qMatrix y k j)) j)
    (fun i => Fin.cases
      (-(∑ k, qMatrix y i k * X k.succ 0))
      (fun j => X 0 0 * qMatrix y i j) j) i

def matrixValue {R : Type u} [CommRing R]
    (X Z : Mat 4 R) (y : Fin 3 → R) : R :=
  Matrix.det ((Matrix.det X) • Z - phi y (Matrix.adjugate X))

def symmetricCoordinates {R : Type u} (v : SymIndex → R) : Mat 4 R :=
  fun i j => if h : i ≤ j then v ⟨(i, j), h⟩
    else v ⟨(j, i), le_of_lt (lt_of_not_ge h)⟩

def polynomial : MvPolynomial Coord ℝ :=
  matrixValue
    (symmetricCoordinates fun ij => MvPolynomial.X (Sum.inl (Sum.inl ij)))
    (symmetricCoordinates fun ij => MvPolynomial.X (Sum.inl (Sum.inr ij)))
    (fun i => MvPolynomial.X (Sum.inr i))

def coordinates (x : Ambient) : Coord → ℝ :=
  Sum.elim (Sum.elim
    (fun ij => (x.1.1 : Mat 4 ℝ) ij.val.1 ij.val.2)
    (fun ij => (x.1.2 : Mat 4 ℝ) ij.val.1 ij.val.2)) x.2

def basePoint : Ambient := ((1, 1), 0)

def linePolynomial (x : Ambient) : Polynomial ℝ :=
  MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (coordinates basePoint i) * Polynomial.X -
      Polynomial.C (coordinates x i)) polynomial

def cone : Set Ambient :=
  {x | ∀ t : ℂ, (linePolynomial x).aeval t = 0 → t.im = 0 ∧ 0 ≤ t.re}



end Paper256
end
end OAI


