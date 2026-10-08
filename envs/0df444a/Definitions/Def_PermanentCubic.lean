-- Prove2me | Definitions.Def_PermanentCubic
-- name    : PermanentCubic
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:02.725683+00:00
-- url     : https://prove2.me/theorems/9a1c8090-408d-4349-8e63-f8699835d728
-- statement:
--   Over the complex numbers, Variables(m) is the set of index pairs (i,j) in Fin m × Fin m, used as variable names, and Poly(σ) is the ring of complex-coefficient multivariate polynomials in variables indexed by σ. permanentPolynomial(m) is the sum over all permutations τ of Fin m of the product over i of the variable X(i,τ(i)), that is, the m×m permanent in m² variables. For a finite variable type σ, an n×n constant matrix A₀ and matrices A_v indexed by v in σ, affineMatrixPolynomial(n,A₀,A) is the determinant of the n×n matrix whose (i,j) entry is the constant A₀(i,j) plus the sum over v of A_v(i,j) times X_v, a polynomial in the variables. HasExactDeterminant(n,p) says n>0 and there exist such A₀ and A with affineMatrixPolynomial(n,A₀,A) exactly equal to p. HasBorderDeterminant(n,p) says n>0 and there exist sequences A₀(j) and A(j) of such matrices, indexed by natural numbers j, such that for every exponent vector d (a finitely supported map from σ to ℕ), the coefficient of the monomial d in the determinant polynomial for index j converges, as j tends to infinity, to the coefficient of d in p. These are defined predicates only, and no relation between them or any bound on n is asserted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PermanentCubic.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PermanentCubic.lean; bytes 16..1169
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace PermanentBorder

open Filter
open scoped Topology

abbrev Variables (m : ℕ) := Fin m × Fin m
abbrev Poly (σ : Type*) := MvPolynomial σ ℂ

noncomputable def permanentPolynomial (m : ℕ) : Poly (Variables m) :=
  ∑ τ : Equiv.Perm (Fin m), ∏ i : Fin m, MvPolynomial.X (i, τ i)

noncomputable def affineMatrixPolynomial {σ : Type*} [Fintype σ] (n : ℕ)
    (A₀ : Matrix (Fin n) (Fin n) ℂ)
    (A : σ → Matrix (Fin n) (Fin n) ℂ) : Poly σ :=
  Matrix.det (fun i j => MvPolynomial.C (A₀ i j) +
    ∑ v : σ, MvPolynomial.C (A v i j) * MvPolynomial.X v)

def HasBorderDeterminant {σ : Type*} [Fintype σ] (n : ℕ) (p : Poly σ) : Prop :=
  0 < n ∧ ∃ (A₀ : ℕ → Matrix (Fin n) (Fin n) ℂ)
    (A : ℕ → σ → Matrix (Fin n) (Fin n) ℂ),
    ∀ d : σ →₀ ℕ, Tendsto
      (fun j => (affineMatrixPolynomial n (A₀ j) (A j)).coeff d)
      atTop (𝓝 (p.coeff d))

def HasExactDeterminant {σ : Type*} [Fintype σ] (n : ℕ) (p : Poly σ) : Prop :=
  0 < n ∧ ∃ (A₀ : Matrix (Fin n) (Fin n) ℂ)
    (A : σ → Matrix (Fin n) (Fin n) ℂ), affineMatrixPolynomial n A₀ A = p



end PermanentBorder
end OAI


