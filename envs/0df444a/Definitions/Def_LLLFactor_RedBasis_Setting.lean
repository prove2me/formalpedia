-- Prove2me | Definitions.Def_LLLFactor_RedBasis_Setting
-- name    : LLLFactor_RedBasis_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:59:18.641905+00:00
-- url     : https://prove2.me/theorems/09c020bf-7a9d-4ae4-b746-3ce02b2ed24c
-- title:
--   Sect. 1, pp. 516–517 — lattices, d(L) (1.1), Gram–Schmidt coefficients μ_ij (1.3), reduced bases (1.4)–(1.5)
-- statement:
--   Let $n$ be a positive integer and let $b_1,\ldots,b_n$ be vectors in $\mathbb R^n$, with the ordinary inner product $(\,\cdot\,,\,\cdot\,)$ and Euclidean length $|\cdot|$.
--
--   1. **Lattice spanned.** $L(b)=\sum_{i=1}^n\mathbb Z b_i=\{\sum_i r_ib_i : r_i\in\mathbb Z\}$. The vectors *form a basis for* a subgroup $L\subseteq\mathbb R^n$ when they are linearly independent over $\mathbb R$ and $L(b)=L$.
--   2. **Determinant (1.1).** $d(L)=|\det(b_1,\ldots,b_n)|$, the absolute value of the determinant of the matrix whose columns are the $b_i$.
--   3. **Gram–Schmidt (1.2)–(1.3).** $b_i^*=b_i-\sum_{j<i}\mu_{ij}b_j^*$ (unnormalised), with
--   $$\mu_{ij}=\frac{(b_i,b_j^*)}{(b_j^*,b_j^*)}.$$
--   4. **Reduced basis (1.4)–(1.5).** The family is *reduced* when
--   $$|\mu_{ij}|\le\tfrac12\quad(1\le j<i\le n),\qquad |b_i^*+\mu_{i\,i-1}b_{i-1}^*|^2\ge\tfrac34|b_{i-1}^*|^2\quad(1<i\le n).$$
--
--   These are the objects of Section 1 of Lenstra–Lenstra–Lovász; every statement of this mission is phrased in them.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` (abbreviated `Vec n`), $b_i^*$ is Mathlib's unnormalised `InnerProductSpace.gramSchmidt`, and the lattice is the $\mathbb Z$-submodule spanned by the $b_i$. $d(L)$ is defined by the determinant (1.1), not by the product $\prod|b_i^*|$, which is a separate theorem. The reducedness predicate does not itself assert linear independence (for a dependent family it can hold degenerately), so every theorem using it also assumes the family is a basis. In Lean's 0-based indices the pair $(i-1,i)$ of (1.5) is $(i,i+1)$. Lean indexes the basis by $\{0,\ldots,n-1\}$, so the paper's $b_i$ is Lean's `b ⟨i-1, _⟩`; a paper exponent $2^{i-1}$ at index $i$ becomes `2 ^ (i : ℕ)` at the Lean index.
-- source:
--   Lenstra, Lenstra, Lovász, Factoring polynomials with rational coefficients, Math. Ann. 261 (1982), pp. 516–517, (1.1)–(1.5); DOI: https://doi.org/10.1007/BF01457454

import Mathlib

namespace LLLFactor.RedBasis
noncomputable section

abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

def gs {n : ℕ} (b : Fin n → Vec n) (i : Fin n) : Vec n :=
  InnerProductSpace.gramSchmidt ℝ b i

def mu {n : ℕ} (b : Fin n → Vec n) (i j : Fin n) : ℝ :=
  inner ℝ (b i) (gs b j) / inner ℝ (gs b j) (gs b j)

def latticeOf {n : ℕ} (b : Fin n → Vec n) : Submodule ℤ (Vec n) :=
  Submodule.span ℤ (Set.range b)

def IsBasisFor {n : ℕ} (b : Fin n → Vec n) (L : Submodule ℤ (Vec n)) : Prop :=
  LinearIndependent ℝ b ∧ latticeOf b = L

def latticeDet {n : ℕ} (b : Fin n → Vec n) : ℝ :=
  |Matrix.det (Matrix.of fun i j => b j i)|

def IsReduced {n : ℕ} (b : Fin n → Vec n) : Prop :=
  (∀ i j : Fin n, j < i → |mu b i j| ≤ (1 / 2 : ℝ)) ∧
  (∀ (i : ℕ) (hi : i + 1 < n),
    (3 / 4 : ℝ) * ‖gs b ⟨i, by omega⟩‖ ^ 2 ≤
      ‖gs b ⟨i + 1, hi⟩ + mu b ⟨i + 1, hi⟩ ⟨i, by omega⟩ • gs b ⟨i, by omega⟩‖ ^ 2)

end
end LLLFactor.RedBasis


