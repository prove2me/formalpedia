-- Prove2me | Definitions.Def_BlottoLP_Flow_LinearFormulation
-- name    : BlottoLP_Flow_LinearFormulation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:14:31.054265+00:00
-- url     : https://prove2.me/theorems/c9a16c89-6d06-4fda-892b-8909cc9202c4
-- title:
--   Linear formulation of a set with at most m constraints and n variables
-- statement:
--   Let $\iota$ be a finite index set and $P\subseteq\mathbb R^{\iota}$. We say that $P$ **has a linear formulation with at most $m$ constraints and at most $n$ variables** if there are a number $k$ of auxiliary variables, a system of $p$ linear equations and $r$ linear inequalities in $(x,y)\in\mathbb R^{\iota}\times\mathbb R^{k}$,
--   $$
--   E x + F y = g,\qquad E' x + F' y \le g',
--   $$
--   with real coefficient matrices and right-hand sides, such that
--   $$
--   x\in P \iff \exists\, y\in\mathbb R^{k}:\ E x+F y=g\ \text{ and }\ E' x+F' y\le g',
--   $$
--   and such that $p+r\le m$ and $|\iota|+k\le n$. In other words, $P$ is the projection onto the $x$-coordinates of a polyhedron described by at most $m$ linear constraints in at most $n$ variables.
--
--   This is the notion behind the phrase "$\mathcal P_A$ could be formulated with $\Theta(N^2K)$ constraints and $\Theta(N^2K)$ variables" in Theorem 4.6.
--
--   **Formalization Note** Both equations and inequalities count as constraints, as in the paper's own count for Linear Program 1, and the variables counted are the coordinates of $x$ together with the auxiliary ones. Counting inequalities only (the convention of the platform's `ExtensionComplexity.TSP.IsEFOfSize`) would let equations hide work and would not express the paper's two counts.
-- source:
--   Behnezhad, Dehghani, Derakhshan, Hajiaghayi, Seddighin, Faster and Simpler Algorithm for Optimal Strategies of Blotto Game, arXiv preprint (arXiv:1612.04029, PDF of 2016-12-28), p. 8, Theorem 4.6 ("could be formulated with Θ(N²K) constraints and Θ(N²K) variables"), and pp. 10–11, the count for Linear Program 1

import Mathlib

namespace BlottoLP.Flow

open Matrix

/-- A linear formulation (extended formulation) of a set `P ⊆ ℝ^ι` with at most `m` constraints
and at most `n` variables: there are `k` auxiliary variables `y`, `p` linear equations and `r`
linear inequalities in `(x, y)` such that `x ∈ P` exactly when some `y` satisfies all of them.
The constraints counted are the equations plus the inequalities (`p + r ≤ m`); the variables
counted are the coordinates of `x` plus the auxiliary ones (`card ι + k ≤ n`). -/
def HasLinearFormulation {ι : Type*} [Fintype ι] (P : Set (ι → ℝ)) (m n : ℕ) : Prop :=
  ∃ (k p r : ℕ) (Eeq : Matrix (Fin p) ι ℝ) (Feq : Matrix (Fin p) (Fin k) ℝ) (geq : Fin p → ℝ)
    (Ele : Matrix (Fin r) ι ℝ) (Fle : Matrix (Fin r) (Fin k) ℝ) (gle : Fin r → ℝ),
    p + r ≤ m ∧ Fintype.card ι + k ≤ n ∧
    ∀ x : ι → ℝ, x ∈ P ↔
      ∃ y : Fin k → ℝ, Eeq *ᵥ x + Feq *ᵥ y = geq ∧ Ele *ᵥ x + Fle *ᵥ y ≤ gle

end BlottoLP.Flow


