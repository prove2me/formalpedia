-- Prove2me | Definitions.Def_SemialgebraicSDP_Copositive_Forms
-- name    : SemialgebraicSDP_Copositive_Forms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:13:58.918714+00:00
-- url     : https://prove2.me/theorems/4c4dde15-55dd-43ed-b0c3-c4c844004e5f
-- title:
--   §7.5, pp. 317–318 — the forms $P(z) = \sum_{i,j} m_{ij} z_i^2 z_j^2$, $P_r(z) = (\sum_i z_i^2)^r P(z)$ and $P_1(z) = \sum_{i,j,k} m_{ij} z_i^2 z_j^2 z_k^2$
-- statement:
--   Let $n$ be a natural number and $M = (m_{ij})$ a real $n \times n$ matrix. Write $z = (z_1, \dots, z_n)$ for real variables and $\mathbf z = [z_1^2, z_2^2, \dots, z_n^2]^T$ for the vector of their squares. This module defines three real polynomials in $z_1, \dots, z_n$, used in §7.5 of the paper to test copositivity of $M$.
--
--   1. **The fourth order form** (p. 317):
--   $$
--   P(z) := \mathbf z^T M \mathbf z = \sum_{i,j} m_{ij} z_i^2 z_j^2 .
--   $$
--   2. **The family of $2(r+2)$-forms** (p. 318), for $r = 0, 1, 2, \dots$:
--   $$
--   P_r(z) = \Bigl(\sum_{i=1}^n z_i^2\Bigr)^r P(z).
--   $$
--   3. **The sixth order form** (p. 318):
--   $$
--   P_1(z) := \sum_{i,j,k} m_{ij} z_i^2 z_j^2 z_k^2 ,
--   $$
--   where all indices range over $1, \dots, n$.
--
--   Substituting $x_i = z_i^2$ turns the question "is $x^T M x \ge 0$ on the nonnegative orthant?" into "is $P$ nonnegative on all of $\mathbb R^n$?", and multiplying by powers of $\sum_i z_i^2$ yields the hierarchy of stronger sufficient conditions studied in the section.
--
--   **Formalization Note** The forms are elements of `MvPolynomial (Fin n) ℝ`, so they can be both evaluated at points of $\mathbb R^n$ and tested for being sums of squares of polynomials. $P_1$ is defined by its own displayed formula; that it coincides with $P_r$ at $r = 1$ is a separate milestone.
-- source:
--   Parrilo, Semidefinite programming relaxations for semialgebraic problems, Math. Program. Ser. B 96 (2003) 293–320, pp. 317–318, §7.5 (definitions of P(z), P_r(z), P_1(z))

import Mathlib

namespace SemialgebraicSDP.Copositive

open MvPolynomial

/-- The fourth order form of §7.5 (Parrilo 2003, p. 317):
`P(z) := zᵀMz = ∑_{i,j} mᵢⱼ zᵢ² zⱼ²`, where `z = [z₁², …, zₙ²]ᵀ`,
as a real polynomial in the variables `z₁, …, zₙ`. -/
noncomputable def formP {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i, ∑ j, C (M i j) * X i ^ 2 * X j ^ 2

/-- The family of `2(r + 2)`-forms of §7.5 (p. 318):
`P_r(z) = (∑_{i=1}^n zᵢ²)^r P(z)`. -/
noncomputable def formPr {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) :
    MvPolynomial (Fin n) ℝ :=
  (∑ i, X i ^ 2) ^ r * formP M

/-- The sixth order form of §7.5 (p. 318): `P₁(z) := ∑_{i,j,k} mᵢⱼ zᵢ² zⱼ² z_k²`. -/
noncomputable def formP1 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i, ∑ j, ∑ k, C (M i j) * X i ^ 2 * X j ^ 2 * X k ^ 2

end SemialgebraicSDP.Copositive


