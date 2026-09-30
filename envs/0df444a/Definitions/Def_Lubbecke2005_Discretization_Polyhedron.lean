-- Prove2me | Definitions.Def_Lubbecke2005_Discretization_Polyhedron
-- name    : Lubbecke2005_Discretization_Polyhedron
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T14:44:16.923624+00:00
-- url     : https://prove2.me/theorems/c6bc4b0d-38cb-4c50-9c01-8f4ed2150be3
-- title:
--   The polyhedron $P$, its integer points $X = P \cap \mathbb{Z}^n$ and its integer rays (Theorem 1)
-- statement:
--   This file fixes the objects of Theorem 1 of Lübbecke and Desrosiers (2005).
--
--   Let $D$ be an $m \times n$ matrix and $\mathbf d$ an $m$-vector, both with **rational** entries. The polyhedron of the theorem is
--
--   $$
--   P = \{\mathbf x \in \mathbb R^n \mid D\mathbf x \geqslant \mathbf d,\ \mathbf x \geqslant \mathbf 0\},
--   $$
--
--   and its set of integer points is $X = P \cap \mathbb Z^n$, the points of $P$ all of whose coordinates are integers. Since $P \subseteq \mathbb R^n_+$, also $X = P \cap \mathbb Z^n_+$.
--
--   The **recession cone** of $P$ is $\{\mathbf r \in \mathbb R^n \mid D\mathbf r \geqslant \mathbf 0,\ \mathbf r \geqslant \mathbf 0\}$; when $P \neq \emptyset$ it is exactly the set of directions $\mathbf r$ with $\mathbf x + t\mathbf r \in P$ for every $\mathbf x \in P$ and $t \geqslant 0$. An **integer ray** of $P$ is a nonzero vector $\mathbf w \in \mathbb Z^n$ lying in this cone. Extremality is not required.
--
--   These are the objects on both sides of the discretization identity (24) and of the Remark that follows it.
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ`; an integer vector `z : Fin n → ℤ` is compared with real vectors through its coordinatewise cast `castVec z`. The data $D$, $\mathbf d$ are rational (`ℚ`) and cast to `ℝ`; the paper names no field, and rationality is an addition justified in the goal theorem. The recession cone is given by its inequality description, which is independent of $\mathbf d$.
-- source:
--   Lübbecke and Desrosiers, Selected Topics in Column Generation, Operations Research 53(6), 2005, pp. 1011–1012, Theorem 1 (definitions of P, X and integer rays)

import Mathlib

namespace Lubbecke2005.Discretization

/-- The cast of an integer vector `z ∈ ℤⁿ` to the real vector `(z₁, …, zₙ) ∈ ℝⁿ`. -/
def castVec {n : ℕ} (z : Fin n → ℤ) : Fin n → ℝ :=
  fun j => (z j : ℝ)

/-- The polyhedron `P = {𝐱 ∈ ℝⁿ | D𝐱 ⩾ 𝐝, 𝐱 ⩾ 𝟎}` of Theorem 1
(Lübbecke–Desrosiers 2005, §3.3, p. 1011), for an `m × n` matrix `D` and an
`m`-vector `𝐝` with rational entries, cast to `ℝ`. -/
def polyhedronP {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℚ) (d : Fin m → ℚ) :
    Set (Fin n → ℝ) :=
  {x | (∀ i, (d i : ℝ) ≤ ∑ j, (D i j : ℝ) * x j) ∧ ∀ j, 0 ≤ x j}

/-- The set of integer points `X = P ∩ ℤⁿ` of Theorem 1 (§3.3, p. 1011): the points
of `P` all of whose coordinates are integers. -/
def integerPoints {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℚ) (d : Fin m → ℚ) :
    Set (Fin n → ℝ) :=
  {x | x ∈ polyhedronP D d ∧ ∃ z : Fin n → ℤ, x = castVec z}

/-- The recession cone `{𝐫 ∈ ℝⁿ | D𝐫 ⩾ 𝟎, 𝐫 ⩾ 𝟎}` of `P`. For nonempty `P` it is the set
of directions `𝐫` with `𝐱 + t𝐫 ∈ P` for all `𝐱 ∈ P`, `t ⩾ 0`. -/
def recessionConeP {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℚ) : Set (Fin n → ℝ) :=
  {r | (∀ i, 0 ≤ ∑ j, (D i j : ℝ) * r j) ∧ ∀ j, 0 ≤ r j}

/-- An *integer ray* of `P` (Theorem 1, §3.3, p. 1011): a nonzero integer vector
`𝐰 ∈ ℤⁿ` lying in the recession cone of `P`. Extremality is not required. -/
def IsIntegerRay {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℚ) (w : Fin n → ℤ) : Prop :=
  w ≠ 0 ∧ castVec w ∈ recessionConeP D

end Lubbecke2005.Discretization


