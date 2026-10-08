-- Prove2me | Definitions.Def_MatousekLP_Duality_MinimallyInfeasible
-- name    : MatousekLP_Duality_MinimallyInfeasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T11:04:28.442495+00:00
-- url     : https://prove2.me/theorems/fcedeeb6-23b9-4146-bad8-bdc4180c7238
-- title:
--   Minimally infeasible systems of linear inequalities
-- statement:
--   Let $A$ be a real $m\times n$ matrix with rows $a_1^{T},\dots,a_m^{T}$ and let $b\in\mathbb{R}^m$. The system $Ax\le b$ consists of the $m$ inequalities $a_i^{T}x\le b_i$. It is **minimally infeasible** if
--
--   1. no $x\in\mathbb{R}^n$ satisfies $Ax\le b$, but
--   2. for every $i$, the subsystem $A^{(i)}x\le b^{(i)}$ obtained by dropping the $i$th inequality has a solution, i.e. some $x$ satisfies $a_j^{T}x\le b_j$ for all $j\ne i$.
--
--   Minimally infeasible systems are the starting point of the third proof of the Farkas lemma in §6.6.
--
--   **Formalization Note** Rows are indexed by `Fin m`, so the book's $i=1,\dots,m$ is $0,\dots,m-1$. The subsystem is expressed by quantifying over the rows $j\ne i$ rather than by building a smaller matrix.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 97 (§6.6, minimally infeasible system)

import Mathlib

namespace MatousekLP.Duality

/-!
# Minimally infeasible systems of inequalities

Matoušek & Gärtner, *Understanding and Using Linear Programming*, Springer 2007,
§6.6, p. 97.  The system `Ax ≤ b` has `m` inequalities `a_iᵀx ≤ b_i`, one per row of `A`;
the book's rows `1, …, m` are `0, …, m-1` here.
-/

open Matrix

variable {m n : ℕ}

/-- The system `Ax ≤ b` of `m` inequalities is **minimally infeasible** (p. 97): it has no
solution, but for every `i` the subsystem obtained by dropping the `i`th inequality has a
solution. -/
def IsMinimallyInfeasible (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Prop :=
  (¬ ∃ x : Fin n → ℝ, A *ᵥ x ≤ b) ∧
    ∀ i : Fin m, ∃ x : Fin n → ℝ, ∀ j : Fin m, j ≠ i → (A *ᵥ x) j ≤ b j

end MatousekLP.Duality


