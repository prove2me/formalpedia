-- Prove2me | Definitions.Def_LiqPremiaEq_colKron
-- name    : LiqPremiaEq_colKron
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:01:05.661317+00:00
-- url     : https://prove2.me/theorems/d1f5db38-3253-4f6b-bfd4-93748a8e872b
-- title:
--   Stacking conventions: $c\otimes B$, $\mathbb 1_{N-1}\otimes v$ and the stacked loading matrix $\xi$
-- statement:
--   The paper stacks the quantities of agents $1,\dots,N-1$ into block vectors and matrices and uses the Kronecker product $A\otimes B$, whose $(i,j)$ block is $A_{ij}B$ (p.3). Three special cases recur:
--
--   1. for a column vector $c\in\mathbb R^{N-1}$ and $B\in\mathbb R^{K\times K'}$, $c\otimes B\in\mathbb R^{(N-1)K\times K'}$ is the matrix whose $n$-th block of rows is $c_nB$ (used with $B=I_K$ and $B=\Lambda$);
--   2. for $v\in\mathbb R^K$, $\mathbb 1_{N-1}\otimes v\in\mathbb R^{(N-1)K}$ consists of $N-1$ copies of $v$;
--   3. for loadings $\xi^1,\dots,\xi^{N-1}\in\mathbb R^{D\times D}$, $\xi=[\xi^1,\dots,\xi^{N-1}]^\top\in\mathbb R^{(N-1)D\times D}$ is the stacked matrix of Assumption 4.3.
--
--   **Formalization Note** Stacked indices are `Fin M × Fin K` (or `Fin M × Fin D`), agent block first, which is the index order of Mathlib's `Matrix.kroneckerMap`; general Kronecker products are `kroneckerMap (· * ·)`. In `c ⊗ B` the trivial column index of the vector $c$ is dropped.
-- source:
--   Muhle-Karbe–Shi–Yang, An Equilibrium Model for the Cross-Section of Liquidity Premia, arXiv:2011.13625v1, Notation, p.3; Lemma 4.2, p.7; Assumption 4.3, p.7; Lemma 4.4, p.8

import Mathlib

open Matrix

namespace LiqPremiaEq

/-- The Kronecker product `c ⊗ B` of a column vector `c ∈ ℝ^{N−1}` with a matrix
`B ∈ ℝ^{K×K'}`: the `(N − 1)K × K'` matrix whose `n`-th block of rows is `cₙ B`.
With `B = I_K` this is `c ⊗ I_K`, with `B = Λ` it is `c ⊗ Λ`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Notation, p.3 (Kronecker product), Lemma 4.4 (p.8) and
Theorem 4.5 (p.8).

**Formalization Note** Stacked indices are `Fin M × Fin K` with the agent (block) index first,
matching Mathlib's `Matrix.kroneckerMap` and the page's block convention. Mathlib's
`kroneckerMap (·*·) (col c) B` has row index `Fin M × Unit`; the `Unit` factor is dropped. -/
def colKron {M K K' : ℕ} (c : Fin M → ℝ) (B : Matrix (Fin K) (Fin K') ℝ) :
    Matrix (Fin M × Fin K) (Fin K') ℝ :=
  Matrix.of fun q k' => c q.1 * B q.2 k'

/-- The vector `1_{N−1} ⊗ v ∈ ℝ^{K(N−1)}`: `N − 1` stacked copies of `v ∈ ℝᴷ`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Lemma 4.2, p.7.

**Formalization Note** Indexed by `Fin M × Fin K`, block index first. -/
def onesKron {M K : ℕ} (v : Fin K → ℝ) : Fin M × Fin K → ℝ :=
  fun q => v q.2

/-- The stacked matrix `ξ = [ξ¹, …, ξ^{N−1}]ᵀ ∈ ℝ^{(N−1)D×D}` of the endowment loadings
`ξⁿ ∈ ℝ^{D×D}`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Assumption 4.3, p.7.

**Formalization Note** Rows are indexed by `Fin M × Fin D`, block `n` first. -/
def stackMat {M D D' : ℕ} (ξ : Fin M → Matrix (Fin D) (Fin D') ℝ) :
    Matrix (Fin M × Fin D) (Fin D') ℝ :=
  Matrix.of fun q d' => ξ q.1 q.2 d'

end LiqPremiaEq


