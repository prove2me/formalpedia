-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
-- name    : OAI_Analysis_DirectCrouzeix_PolynomialCalculus
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:24:41.795614+00:00
-- url     : https://prove2.me/theorems/1a621d42-c3d2-4620-ac5b-1ffd2b57c240
-- title:
--   Tensor functional calculus $\sum_k C_kX^k\mapsto\sum_k A^k\otimes C_k$ for polynomials with matrix coefficients
-- statement:
--   Fix $n,m\in\mathbb{N}$. Write $M_m(\mathbb{C})$ for the ring of complex $m\times m$ matrices and $M_m(\mathbb{C})[X]$ for the ring of polynomials in an indeterminate $X$ with coefficients in $M_m(\mathbb{C})$; the coefficients need not commute with each other, but $X$ commutes with every coefficient. For $A\in M_n(\mathbb{C})$ and $B\in M_m(\mathbb{C})$, $A\otimes B$ is the Kronecker product: the $nm\times nm$ matrix whose rows and columns are indexed by pairs $(i,j)$ with $1\le i\le n$, $1\le j\le m$, and whose entries are $(A\otimes B)_{(i,j),(i',j')}=A_{ii'}B_{jj'}$. The module defines:
--
--   1. **Coefficient embedding.** The unital ring homomorphism
--   $$
--   \iota_{n,m}:M_m(\mathbb{C})\to M_{nm}(\mathbb{C}),\qquad \iota_{n,m}(B)=I_n\otimes B .
--   $$
--
--   2. **Tensor evaluation of a matrix polynomial.** For $A\in M_n(\mathbb{C})$, the ring homomorphism $\tau_A:M_m(\mathbb{C})[X]\to M_{nm}(\mathbb{C})$ that applies $\iota_{n,m}$ to the coefficients and substitutes $X=A\otimes I_m$:
--   $$
--   \tau_A\Big(\sum_{k}C_kX^{k}\Big)=\sum_{k}(I_n\otimes C_k)\,(A\otimes I_m)^{k}=\sum_{k}A^{k}\otimes C_k .
--   $$
--   It is multiplicative because every matrix $I_n\otimes C$ commutes with $A\otimes I_m$. The two basic evaluation rules $\tau_A(C)=I_n\otimes C$ for a constant polynomial $C$ and $\tau_A(X)=A\otimes I_m$ are recorded as simplification lemmas.
--
--   3. **Coefficient polynomial.** For $d\in\mathbb{N}$ and matrices $B_0,\dots,B_d\in M_m(\mathbb{C})$, the matrix polynomial
--   $$
--   P_B=\sum_{k=0}^{d}B_k\,X^{k}\in M_m(\mathbb{C})[X].
--   $$
--
--   The tensor evaluation $\sum_{k=0}^{d}A^{k}\otimes B_k$, the left-hand side of the matrix-coefficient Crouzeix-type bound with constant $2$ studied in this development, equals $\tau_A(P_B)$ (proved separately). Realizing it as the image of a ring homomorphism turns products and factorizations of matrix polynomials into products of $nm\times nm$ matrices.
--
--   **Formalization Note** The maps are `coefficientEmbedding n m` and `tensorPolynomial A`, the latter built with `Polynomial.eval₂RingHom'`, whose side condition is the commutation of each `1 ⊗ₖ B` with `A ⊗ₖ 1`; `coefficientPolynomial B` takes `B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ`. Matrices of size $nm$ are indexed by `Fin n × Fin m`. The simplification lemmas are `tensorPolynomial_C` and `tensorPolynomial_X`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/PolynomialCalculus.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/PolynomialCalculus.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DirectCrouzeix mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

def coefficientEmbedding (n m : ℕ) :
    Matrix (Fin m) (Fin m) ℂ →+*
      Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ where
  toFun B := (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ B
  map_zero' := Matrix.kronecker_zero _
  map_one' := Matrix.one_kronecker_one
  map_add' B C := Matrix.kronecker_add _ B C
  map_mul' B C := by
    simpa using Matrix.mul_kronecker_mul
      (1 : Matrix (Fin n) (Fin n) ℂ) 1 B C

def tensorPolynomial {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Polynomial (Matrix (Fin m) (Fin m) ℂ) →+*
      Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  Polynomial.eval₂RingHom' (coefficientEmbedding n m)
    (A ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) (by
      intro B
      change (1 ⊗ₖ B) * (A ⊗ₖ 1) = (A ⊗ₖ 1) * (1 ⊗ₖ B)
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
      simp)

def coefficientPolynomial {m d : ℕ}
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) :
    Polynomial (Matrix (Fin m) (Fin m) ℂ) :=
  ∑ k : Fin (d + 1), Polynomial.C (B k) * Polynomial.X ^ (k : ℕ)

@[simp] theorem tensorPolynomial_C {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin m) (Fin m) ℂ) :
    tensorPolynomial A (Polynomial.C B) = (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ B := by
  exact Polynomial.eval₂_C _ _

@[simp] theorem tensorPolynomial_X {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    tensorPolynomial (m := m) A Polynomial.X = A ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ) := by
  exact Polynomial.eval₂_X _ _

end DirectCrouzeix

end

end OAI


