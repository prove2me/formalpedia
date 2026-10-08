-- Prove2me | Definitions.Def_SmoothInitialForm
-- name    : SmoothInitialForm
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:02.92682+00:00
-- url     : https://prove2.me/theorems/16dfe118-04d8-45ef-be05-c57ac0eec437
-- statement:
--   Polynomials in variables indexed by a finite type σ are taken over the complex numbers, and Poly(σ) denotes this polynomial ring. For a size n, a constant complex n×n matrix A₀ and a family of n×n complex matrices A_v indexed by σ, affineMatrixPolynomial is the determinant, as a polynomial in the variables X_v, of the matrix whose (i,j) entry is A₀(i,j) plus the sum over v of A_v(i,j)·X_v, so each entry is an affine-linear polynomial. HasExactDeterminant(n,p) says that n>0 and p equals such a determinant for some A₀ and some family A. HasBorderDeterminant(n,p) says that n>0 and there exist sequences A₀(j) and A(j), indexed by natural numbers j, of such matrix data for which, for every exponent vector d, the coefficient of the monomial d in the j-th determinant polynomial converges, as j tends to infinity, to the coefficient of d in p. This is coefficientwise convergence of determinants of size n, which allows p to be a limit of exact determinants without itself being one. Finally, for a point b in ℂ^σ and a matrix B of complex entries B(v,w) indexed by σ×τ with τ finite, affineSubstitution is the ℂ-algebra homomorphism from Poly(σ) to Poly(τ) that sends each variable X_v to the affine-linear polynomial b_v plus the sum over w of B(v,w)·X_w.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SmoothInitialForm.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SmoothInitialForm.lean; bytes 16..1256
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open MvPolynomial
namespace PermanentBorder

open Filter
open scoped Topology

abbrev Poly (σ : Type*) := MvPolynomial σ ℂ

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

noncomputable def affineSubstitution {σ τ : Type*} [Fintype τ]
    (b : σ → ℂ) (B : σ → τ → ℂ) : Poly σ →ₐ[ℂ] Poly τ :=
  MvPolynomial.aeval (fun v => MvPolynomial.C (b v) +
    ∑ w : τ, MvPolynomial.C (B v w) * MvPolynomial.X w)



end PermanentBorder
end OAI


