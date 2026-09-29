-- Prove2me | Definitions.Def_DiophantinePreprocessing_FrankTardos_IsWMaximal
-- name    : DiophantinePreprocessing_FrankTardos_IsWMaximal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:39:37.262966+00:00
-- url     : https://prove2.me/theorems/729c794b-f97e-444a-a425-009477290603
-- title:
--   The polyhedron $P = \{x : Ax \le b\}$ and $w$-maximal points
-- statement:
--   Let $A$ be an $m \times n$ integer matrix and $b \in \mathbb{R}^m$. The polyhedron of the primal program (1a) is
--   $$P = \{x \in \mathbb{R}^n : Ax \le b\}.$$
--   For an objective $w \in \mathbb{R}^n$, a vector $\bar x$ is **$w$-maximal** if $\bar x \in P$ and
--   $$w \cdot \bar x = \max(w \cdot x : x \in P),$$
--   that is, $w \cdot x \le w \cdot \bar x$ for every $x \in P$.
--
--   The $w$-maximal points are the optimal solutions of the linear program $\max\{wx : Ax \le b\}$; the paper's goal is an objective $\tilde w$ of small size with the same $\tilde w$-maximal points.
--
--   **Formalization Note** When $P$ is empty or $w$ is unbounded on $P$, no point is $w$-maximal.
-- source:
--   Frank & Tardos, An application of simultaneous diophantine approximation in combinatorial optimization, Combinatorica 7(1) (1987), p. 56 (P) and p. 57, (1) and the definition of w-maximal

import Mathlib

namespace DiophantinePreprocessing.FrankTardos

/-- The polyhedron `P = {x ∈ ℝⁿ : A x ≤ b}` of an integer `m × n` matrix `A` and `b ∈ ℝᵐ`. -/
def polyhedron {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, ∑ j, (A i j : ℝ) * x j ≤ b i}

/-- `x` is `w`-maximal: `x ∈ P` and `w · x = max (w · y : y ∈ P)`. -/
def IsWMaximal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℝ) (w : Fin n → ℝ)
    (x : Fin n → ℝ) : Prop :=
  x ∈ polyhedron A b ∧ ∀ y ∈ polyhedron A b, ∑ j, w j * y j ≤ ∑ j, w j * x j

end DiophantinePreprocessing.FrankTardos


