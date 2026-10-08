-- Prove2me | Definitions.Def_VanderbeiLP_SelfDual_SelfDualEmbedding
-- name    : VanderbeiLP_SelfDual_SelfDualEmbedding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T13:35:07.804693+00:00
-- url     : https://prove2.me/theorems/e6d7712f-e09f-471d-87f4-86c130e11ac7
-- title:
--   Standard-form LP (22.1)/(22.2) and its homogeneous self-dual embedding (22.21)
-- statement:
--   Fix integers $m, n \ge 0$, a real $m \times n$ matrix $A$, a right-hand side $b \in \mathbb{R}^m$ and an objective vector $c \in \mathbb{R}^n$. The primal problem (22.1) and its dual (22.2) are
--
--   $$\text{maximize } c^T x \ \text{ s.t. } Ax \le b,\ x \ge 0, \qquad\qquad \text{minimize } b^T y \ \text{ s.t. } A^T y \ge c,\ y \ge 0.$$
--
--   This file defines:
--
--   1. **primal feasibility** ($x \ge 0$, $Ax \le b$) and **dual feasibility** ($y \ge 0$, $A^T y \ge c$);
--   2. **primal optimality**: $x$ is primal feasible and $c^T x' \le c^T x$ for every primal feasible $x'$; **dual optimality**: $y$ is dual feasible and $b^T y \le b^T y'$ for every dual feasible $y'$;
--   3. **feasibility for the self-dual embedding** (22.21): a tuple $(x, y, \phi, z, w, \psi)$ with $x, z \in \mathbb{R}^n$, $y, w \in \mathbb{R}^m$, $\phi, \psi \in \mathbb{R}$ satisfying
--   $$-A^T y + c\phi + z = 0, \qquad Ax - b\phi + w = 0, \qquad -c^T x + b^T y + \psi = 0,$$
--   $$x, y, \phi, z, w, \psi \ge 0;$$
--   4. **strict complementarity** of such a tuple: $x_j + z_j > 0$ for every $j$, $y_i + w_i > 0$ for every $i$, and $\phi + \psi > 0$.
--
--   Problem (22.21) is problem (22.3), $\text{maximize } 0$ subject to $-A^Ty + c\phi \le 0$, $Ax - b\phi \le 0$, $-c^Tx + b^Ty \le 0$, $x, y, \phi \ge 0$, written with slack variables $z, w, \psi$. Its constraint matrix is skew symmetric, so it is a homogeneous self-dual problem; Theorem 22.8 reads off optimal solutions of (22.1)–(22.2), or a certificate of infeasibility, from a strictly complementary solution of it.
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ`, `Fin m → ℝ`, and `A : Matrix (Fin m) (Fin n) ℝ`. "Optimal" is the Chapter 5 notion: a feasible point attaining the best objective value among all feasible points.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 323, Eqs. (22.1)–(22.3) (PDF p. 329); p. 334, Eq. (22.21) and the definition of strict complementarity (PDF p. 340)

import Mathlib
import Definitions.Def_VanderbeiLP_StrictComp_PrimalDualPair

open Matrix

namespace VanderbeiLP.SelfDual

/-- `x` is feasible for the primal problem (22.1)
`maximize cᵀx subject to Ax ≤ b, x ≥ 0`. -/
def PrimalFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) : Prop :=
  (∀ j, 0 ≤ x j) ∧ ∀ i, (A *ᵥ x) i ≤ b i

/-- `y` is feasible for the dual problem (22.2)
`minimize bᵀy subject to Aᵀy ≥ c, y ≥ 0`. -/
def DualFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (y : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ y i) ∧ ∀ j, c j ≤ (Aᵀ *ᵥ y) j

/-- `(x, y, φ, z, w, ψ)` is feasible for the self-dual embedding (22.21):
`-Aᵀy + cφ + z = 0`, `Ax - bφ + w = 0`, `-cᵀx + bᵀy + ψ = 0`,
`x, y, φ, z, w, ψ ≥ 0`. -/
def EmbeddingFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ) (φ : ℝ) (z : Fin n → ℝ)
    (w : Fin m → ℝ) (ψ : ℝ) : Prop :=
  -(Aᵀ *ᵥ y) + φ • c + z = 0 ∧
  A *ᵥ x - φ • b + w = 0 ∧
  -(c ⬝ᵥ x) + b ⬝ᵥ y + ψ = 0 ∧
  (∀ j, 0 ≤ x j) ∧ (∀ i, 0 ≤ y i) ∧ 0 ≤ φ ∧
  (∀ j, 0 ≤ z j) ∧ (∀ i, 0 ≤ w i) ∧ 0 ≤ ψ

/-- Strict complementarity for a solution of (22.21) (Vanderbei, p. 334):
`xⱼ + zⱼ > 0` for all `j`, `yᵢ + wᵢ > 0` for all `i`, and `φ + ψ > 0`. -/
def EmbeddingStrictlyComplementary {m n : ℕ} (x : Fin n → ℝ) (y : Fin m → ℝ) (φ : ℝ)
    (z : Fin n → ℝ) (w : Fin m → ℝ) (ψ : ℝ) : Prop :=
  (∀ j, 0 < x j + z j) ∧ (∀ i, 0 < y i + w i) ∧ 0 < φ + ψ

end VanderbeiLP.SelfDual


