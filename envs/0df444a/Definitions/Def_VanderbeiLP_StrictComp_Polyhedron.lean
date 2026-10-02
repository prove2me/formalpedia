-- Prove2me | Definitions.Def_VanderbeiLP_StrictComp_Polyhedron
-- name    : VanderbeiLP_StrictComp_Polyhedron
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T17:12:26.289475+00:00
-- url     : https://prove2.me/theorems/bea1d2f3-a1c2-47f9-96ff-558bc1871544
-- title:
--   Halfspaces (nonzero normal) and polyhedra in $\mathbb{R}^n$
-- statement:
--   A **halfspace** of $\mathbb{R}^n$ is a set given by a single nontrivial linear inequality:
--
--   $$H = \Big\{x \in \mathbb{R}^n : \sum_{j=1}^n a_j x_j \le \beta\Big\}, \qquad (a_1, \dots, a_n) \ne 0.$$
--
--   If the coefficient vector is allowed to vanish, the set is a *generalized halfspace*; a generalized halfspace is a halfspace, all of $\mathbb{R}^n$, or the empty set.
--
--   A **polyhedron** is the intersection of finitely many generalized halfspaces, that is, any set of the form
--
--   $$P = \Big\{x \in \mathbb{R}^n : \sum_{j=1}^n a_{ij} x_j \le b_i,\ i = 1, \dots, m\Big\}$$
--
--   for some $m \ge 0$, some real $m \times n$ matrix $(a_{ij})$ and some $b \in \mathbb{R}^m$. With $m = 0$ this is all of $\mathbb{R}^n$.
--
--   These are the objects of the Separation Theorem for polyhedra. The requirement $a \ne 0$ in a halfspace is what makes separation meaningful: without it, the empty set would count as a halfspace.
--
--   **Formalization Note** `IsHalfspace H` asks for $a \ne 0$ and $\beta$ with $H = \{x : a \cdot x \le \beta\}$; `IsPolyhedron P` asks for $m$, $A$ and $b$ with $P = \{x : Ax \le b\}$ componentwise.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 144, Eq. (10.3) (halfspace, PDF p. 157); p. 145 (generalized halfspace, polyhedron, PDF p. 158)

import Mathlib

open Matrix

namespace VanderbeiLP.StrictComp

/-- A halfspace of `ℝⁿ` (10.3): a set `{x : aᵀx ≤ β}` given by a single nontrivial linear
inequality, i.e. with coefficient vector `a ≠ 0`. -/
def IsHalfspace {n : ℕ} (H : Set (Fin n → ℝ)) : Prop :=
  ∃ (a : Fin n → ℝ) (β : ℝ), a ≠ 0 ∧ H = {x | a ⬝ᵥ x ≤ β}

/-- A polyhedron of `ℝⁿ` (p. 145): a set of the form `{x : Σⱼ aᵢⱼ xⱼ ≤ bᵢ, i = 1, …, m}`
for some `m`, some `m × n` real matrix `A` and some `b ∈ ℝᵐ`, i.e. the intersection of
finitely many generalized halfspaces. -/
def IsPolyhedron {n : ℕ} (P : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ), P = {x | A *ᵥ x ≤ b}

end VanderbeiLP.StrictComp


