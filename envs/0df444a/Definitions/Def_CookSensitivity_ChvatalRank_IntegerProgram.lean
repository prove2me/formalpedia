-- Prove2me | Definitions.Def_CookSensitivity_ChvatalRank_IntegerProgram
-- name    : CookSensitivity_ChvatalRank_IntegerProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:12:51.681979+00:00
-- url     : https://prove2.me/theorems/e7a1ff63-977a-4fc0-94cc-f39758d8a32e
-- title:
--   Polyhedra $\{x : Ax \le b\}$, LP and IP optima, rational polyhedra and integer hulls over $\mathbb{Q}$
-- statement:
--   All objects are rational, as in the paper. A vector $x \in \mathbb{Q}^n$ is **integral** if every coordinate is an integer.
--
--   For an integral $m\times n$ matrix $A$ and $b \in \mathbb{Q}^m$, write
--   $$P(A,b) = \{x \in \mathbb{Q}^n : Ax \le b\}$$
--   (componentwise). Given $w \in \mathbb{Q}^n$:
--
--   1. $\bar x$ is an **optimal solution to** $\max\{wx : Ax \le b\}$ if $\bar x \in P(A,b)$ and $wy \le w\bar x$ for all $y \in P(A,b)$;
--   2. $\bar z$ is an **optimal solution to** $\max\{wx : Ax \le b,\ x \text{ integral}\}$ if $\bar z$ is integral, $\bar z \in P(A,b)$, and $wy \le w\bar z$ for every integral $y \in P(A,b)$.
--
--   "The maximum exists" means that an optimal solution exists.
--
--   A set $P \subseteq \mathbb{Q}^n$ is a **(rational) polyhedron** if $P = \{x : Dx \le d\}$ for some rational $k\times n$ matrix $D$ and $d\in\mathbb{Q}^k$ ($k = 0$ allowed, giving $\mathbb{Q}^n$). The **integer hull** of a set $S \subseteq \mathbb{Q}^n$ is
--   $$S_I = \operatorname{conv}\{x \in S : x \text{ integral}\},$$
--   the convex hull over $\mathbb{Q}$ of the integral vectors in $S$.
--
--   These are the integer-programming objects of the whole paper.
--
--   **Formalization Note** Points are `Fin n → ℚ`; `polyhedron A b` uses `A.map Int.cast` and the product order on `Fin m → ℚ`. `integerHull` is `convexHull ℚ`.
-- source:
--   Cook, Gerards, Schrijver, Tardos, Sensitivity theorems in integer linear programming, Math. Programming 34 (1986), p. 252 (§1: all polyhedra, matrices, vectors rational), p. 259 (§3: P_I)

import Mathlib

namespace CookSensitivity.ChvatalRank

open Matrix

/-- A rational vector is integral when every coordinate is an integer. -/
def IsIntegral {n : ℕ} (x : Fin n → ℚ) : Prop :=
  ∀ i, ∃ k : ℤ, x i = k

/-- The polyhedron `{x ∈ ℚⁿ : Ax ≤ b}` of an integral `m × n` matrix `A` and a rational
right-hand side `b` (componentwise order). -/
def polyhedron {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ) : Set (Fin n → ℚ) :=
  {x | (A.map (Int.cast : ℤ → ℚ)) *ᵥ x ≤ b}

/-- `x` is an optimal solution to the linear program `max {wx : Ax ≤ b}`. -/
def IsLPOptimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ) (w : Fin n → ℚ)
    (x : Fin n → ℚ) : Prop :=
  x ∈ polyhedron A b ∧ ∀ y ∈ polyhedron A b, w ⬝ᵥ y ≤ w ⬝ᵥ x

/-- `z` is an optimal solution to the integer program `max {wx : Ax ≤ b, x integral}`. -/
def IsIPOptimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ) (w : Fin n → ℚ)
    (z : Fin n → ℚ) : Prop :=
  IsIntegral z ∧ z ∈ polyhedron A b ∧
    ∀ y ∈ polyhedron A b, IsIntegral y → w ⬝ᵥ y ≤ w ⬝ᵥ z

/-- `P ⊆ ℚⁿ` is a (rational) polyhedron: the solution set of finitely many rational linear
inequalities `Dx ≤ d` (`k = 0` rows gives `ℚⁿ`). -/
def IsPolyhedron {n : ℕ} (P : Set (Fin n → ℚ)) : Prop :=
  ∃ (k : ℕ) (D : Matrix (Fin k) (Fin n) ℚ) (d : Fin k → ℚ), P = {x | D *ᵥ x ≤ d}

/-- The integer hull `S_I`: the convex hull (over `ℚ`) of the integral vectors in `S`. -/
def integerHull {n : ℕ} (S : Set (Fin n → ℚ)) : Set (Fin n → ℚ) :=
  convexHull ℚ {x | x ∈ S ∧ IsIntegral x}

end CookSensitivity.ChvatalRank


