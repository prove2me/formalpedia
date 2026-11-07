-- Prove2me | Definitions.Def_F3SubsetSum_MonomialShadow
-- name    : F3SubsetSum_MonomialShadow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:27:45.894178+00:00
-- url     : https://prove2.me/theorems/0929909b-af2f-48a5-9ff3-0d2481f8bb0a
-- title:
--   Degree and shadow of a family of monomials
-- statement:
--   Identify a monomial $x^\alpha$ in $x_1,\dots,x_n$ with its exponent vector $\alpha\in\mathbb N^n$ (a multiset over $[n]$), of degree $|\alpha|=\sum_j\alpha_j$. The **shadow** of a family $\mathcal A$ of monomials is
--
--   $$
--   \partial\mathcal A=\{x^\alpha/x_i : x^\alpha\in\mathcal A,\ \alpha_i\ge1\},
--   $$
--
--   the family of all monomials obtained by removing one variable from a member of $\mathcal A$. Shadows are the combinatorial core of Corollary 4.18 and Theorem 4.19.
--
--   **Formalization Note** Exponent vectors are `Fin n →₀ ℕ`; $x^\alpha/x_i$ is `α - single i 1`.
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, §4.4.2, p.27

import Mathlib

namespace F3SubsetSum

/-- The total degree `|α| = Σ_j α_j` of the monomial `x^α` with exponent vector `α`. -/
def monoDeg {n : ℕ} (α : Fin n →₀ ℕ) : ℕ := ∑ j, α j

/-- **The shadow of a family of monomials** (Kothari, Metger, O'Donnell, Shutty, Wu,
arXiv:2609.40321v1, p.27): `∂𝒜 = {x^α / x_i : x^α ∈ 𝒜, α_i ≥ 1}`. A monomial `x^α` is given by
its exponent vector `α : Fin n →₀ ℕ` (equivalently, a multiset over `[n]`), and `∂𝒜` contains
all `α' ⊂ α` with `|α'| = |α| − 1`. -/
noncomputable def shadow {n : ℕ} (𝒜 : Finset (Fin n →₀ ℕ)) : Finset (Fin n →₀ ℕ) :=
  𝒜.biUnion fun α => α.support.image fun i => α - Finsupp.single i 1

end F3SubsetSum


