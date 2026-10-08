-- Prove2me | Definitions.Def_GroupRingDeterminant
-- name    : GroupRingDeterminant
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:13.452269+00:00
-- url     : https://prove2.me/theorems/08749b92-f1ba-4084-87bd-aeaf275bcd9e
-- statement:
--   Over a group G and size n, Hilbert(G,n) is the Hilbert space l²(Fin n × G) of square-summable complex families. identityVector(i) is the basis vector at (i, 1), the identity element of G in component i. groupTrace(T) of a bounded linear operator T on this space is the unnormalized trace, the sum over i<n of the inner product of identityVector(i) with T applied to identityVector(i). For an invertible operator, fkDet(T) is the Fuglede–Kadison determinant exp(Re groupTrace(log(T*T))/2), using the continuous-functional-calculus logarithm. IsRegularOperator(A,T) says that, for a matrix A over the integral group ring ℤ[G], T acts by the left-regular coordinate formula: (Tξ)(i,h) is the sum over j and over the support of A_ij of the integer coefficient z at g times ξ(j, g⁻¹h). rationalMatrix(A) maps the entries coefficientwise into ℚ[G]. MainStatement is a defined proposition, not an established theorem: it asserts there exist a finitely generated group G, some n ≥ 1, an n×n matrix A over ℤ[G], and a bounded operator T such that A is invertible over ℚ[G], T is the regular operator of A, T is invertible as a bounded operator, and its Fuglede–Kadison determinant satisfies 0 < fkDet(T) < 1.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/GroupRingDeterminant.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/GroupRingDeterminant.lean; bytes 16..2041
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

/-- The Hilbert space l²(G)^n, with the product coordinates flattened. -/
abbrev Hilbert (G : Type) (n : ℕ) := lp (fun _ : Fin n × G => ℂ) 2

/-- The identity vector in component i. -/
def identityVector {G : Type} [Group G] {n : ℕ} (i : Fin n) : Hilbert G n :=
  by
    classical
    exact lp.single 2 (i, 1) 1

/-- The unnormalized matrix trace, linear in its operator argument. -/
def groupTrace {G : Type} [Group G] {n : ℕ}
    (T : Hilbert G n →L[ℂ] Hilbert G n) : ℂ :=
  ∑ i : Fin n, inner ℂ (identityVector i) (T (identityVector i))

/-- The invertible-case Fuglede--Kadison determinant.
It is used below only for invertible regular operators. -/
def fkDet {G : Type} [Group G] {n : ℕ}
    (T : Hilbert G n →L[ℂ] Hilbert G n) : ℝ :=
  Real.exp ((groupTrace (CFC.log (star T * T))).re / 2)

/-- Exact coordinate specification of the bounded left-regular operator of A. -/
def IsRegularOperator {G : Type} [Group G] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℤ G))
    (T : Hilbert G n →L[ℂ] Hilbert G n) : Prop :=
  ∀ (ξ : Hilbert G n) (i : Fin n) (h : G),
    (T ξ) (i, h) = ∑ j : Fin n,
      (A i j).coeff.sum fun g z => (z : ℂ) * ξ (j, g⁻¹ * h)

/-- Coefficientwise extension from the integral to the rational group ring. -/
def rationalMatrix {G : Type} [Group G] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℤ G)) :
    Matrix (Fin n) (Fin n) (MonoidAlgebra ℚ G) :=
  A.map (MonoidAlgebra.mapRingHom G (Int.castRingHom ℚ))

/-- An integral group-ring matrix with rational and bounded inverses and determinant in (0, 1). -/
def MainStatement : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Group.FG G) (n : ℕ),
    1 ≤ n ∧ ∃ (A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℤ G))
      (T : Hilbert G n →L[ℂ] Hilbert G n),
      IsUnit (rationalMatrix A) ∧ IsRegularOperator A T ∧ IsUnit T ∧
        0 < fkDet T ∧ fkDet T < 1



end GroupRingDeterminant
end
end OAI


