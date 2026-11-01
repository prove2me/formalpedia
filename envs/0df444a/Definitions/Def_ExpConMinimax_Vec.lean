-- Prove2me | Definitions.Def_ExpConMinimax_Vec
-- name    : ExpConMinimax_Vec
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:44.389482+00:00
-- url     : https://prove2.me/theorems/51e33692-7b1d-4f58-9673-0736b79d620d
-- title:
--   Euclidean space $\mathbb R^n$, the orthant $\mathbb R^n_+$ and the positive part $v_+$
-- statement:
--   Throughout the mission, $\mathbb R^n$ carries the Euclidean inner product $\langle u,v\rangle=u^\top v$ and the Euclidean norm $\|\cdot\|$ (the paper's $\|\cdot\|_2$).
--
--   1. The **nonnegative orthant** $\mathbb R^n_+$ is the set of vectors all of whose coordinates are $\ge 0$; the multipliers $\gamma\in\mathbb R^{m_1}_+$, $\lambda\in\mathbb R^{m_2}_+$ live there.
--   2. The **positive part** of $v\in\mathbb R^n$ is the vector $v_+$ with coordinates $(v_+)_i=\max\{v_i,0\}$.
--
--   The positive parts $H(x)_+$ and $G(y)_+$ measure the violation of the constraints $H(x)\le0$, $G(y)\le0$; their norms are the feasibility residuals of the paper.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, with coordinates indexed by $0,\dots,n-1$.
-- source:
--   Yang, Li, Lan, Data-Driven Minimax Optimization with Expectation Constraints, arXiv:2202.07868v2, Notation, p.7; (2.1), p.8

import Mathlib

namespace ExpConMinimax

/-- **Euclidean space `ℝⁿ`.**
Yang, Li, Lan, *Data-Driven Minimax Optimization with Expectation Constraints*,
arXiv:2202.07868v2, §1, p.2 (`X ⊂ ℝ^{d_x}`, `Y ⊂ ℝ^{d_y}`) and Notation, p.7 (`‖·‖` is the
Euclidean norm).

`Vec n` is `ℝⁿ` with the Euclidean inner product `⟨u, v⟩ = uᵀv` and the Euclidean norm `‖·‖`.
The paper's `‖·‖₂` (Theorem 9) is the same norm.

**Formalization Note.** `Vec n = EuclideanSpace ℝ (Fin n)`; coordinates are indexed by
`Fin n = {0, …, n − 1}`. -/
abbrev Vec (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- **The nonnegative orthant `ℝⁿ₊`.**
arXiv:2202.07868v2, (2.1), p.8: `γ ∈ ℝ^{m₁}_+`, `λ ∈ ℝ^{m₂}_+`.

`IsNonneg v` holds iff every coordinate of `v` is `≥ 0`. -/
def IsNonneg {n : ℕ} (v : Vec n) : Prop := ∀ i, 0 ≤ v i

/-- **Componentwise positive part `v₊ = max{v, 0}`.**
arXiv:2202.07868v2, Notation, p.7: "`g(x)₊ = max{g(x), 0}`", applied componentwise to the
constraint vectors `H(x) ∈ ℝ^{m₁}` and `G(y) ∈ ℝ^{m₂}` (Lemma 1, p.8; Theorem 9, p.15).

**Formalization Note.** `(vecPosPart v) i = max (v i) 0` for every coordinate `i`. -/
noncomputable def vecPosPart {n : ℕ} (v : Vec n) : Vec n :=
  WithLp.toLp 2 (fun i => max (v i) 0)

end ExpConMinimax


