-- Prove2me | Definitions.Def_RobustSurvey_Affine_Data
-- name    : RobustSurvey_Affine_Data
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:01:08.791168+00:00
-- url     : https://prove2.me/theorems/28db80c9-995a-49b5-8893-ed3c60e79db0
-- title:
--   Two-stage linear data with uncertain recourse
-- statement:
--   For arbitrary finite dimensions $m,n_1,n_2,L$, the data are real vectors $c\in\mathbb R^{n_1}$ and $b\in\mathbb R^m$, constant matrices $A_1^{(0)},A_2^{(0)}$, and coefficient matrices $A_1^{(l)},A_2^{(l)}$ for $1\le l\le L$, with $m$ rows and respectively $n_1,n_2$ columns. Define
--   $$A_j(u)=A_j^{(0)}+\sum_{l=1}^L u_l A_j^{(l)},\qquad j=1,2.$$
--   For an arbitrary uncertainty set $U\subseteq\mathbb R^L$, first-stage vector $x$, and rule $y:\mathbb R^L\to\mathbb R^{n_2}$, robust feasibility means
--   $$A_1(u)x+A_2(u)y(u)\le b\quad\text{componentwise for every }u\in U.$$
--   The objective is $c^Tx$. The rule may depend on the entire observed vector $u$. These general data impose neither fixed recourse nor sign, integrality, feasibility, or attainment assumptions. Finite coordinates use zero-based indices, with the constant matrices stored separately.
-- source:
--   Bertsimas, Brown and Caramanis, Theory and Applications of Robust Optimization, held PDF marked arXiv:1010.5445v1 (2010), https://arxiv.org/abs/1010.5445v1; SHA-256 25714e004b9b868fcb48997d3364800e379cd1be5f8b027ca6f50ee08f25ae50; anomalous revised-version date November 26, 2024; (4.10), printed p. 22 / PDF p. 23, and affine data expansion, printed p. 24 / PDF p. 25.

import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped BigOperators
open Matrix

namespace RobustSurvey.Affine

/-- General two-stage real linear data with affine uncertainty in both matrices. -/
structure Data (m n₁ n₂ L : ℕ) where
  c : Fin n₁ → ℝ
  b : Fin m → ℝ
  A₁₀ : Matrix (Fin m) (Fin n₁) ℝ
  A₁ : Fin L → Matrix (Fin m) (Fin n₁) ℝ
  A₂₀ : Matrix (Fin m) (Fin n₂) ℝ
  A₂ : Fin L → Matrix (Fin m) (Fin n₂) ℝ

noncomputable def Data.firstMatrix {m n₁ n₂ L : ℕ} (D : Data m n₁ n₂ L)
    (u : Fin L → ℝ) : Matrix (Fin m) (Fin n₁) ℝ :=
  D.A₁₀ + ∑ l, u l • D.A₁ l

noncomputable def Data.recourseMatrix {m n₁ n₂ L : ℕ} (D : Data m n₁ n₂ L)
    (u : Fin L → ℝ) : Matrix (Fin m) (Fin n₂) ℝ :=
  D.A₂₀ + ∑ l, u l • D.A₂ l

/-- Feasibility for an arbitrary rule after the entire uncertainty vector is revealed. -/
def Data.RobustFeasible {m n₁ n₂ L : ℕ} (D : Data m n₁ n₂ L)
    (U : Set (Fin L → ℝ)) (x : Fin n₁ → ℝ)
    (y : (Fin L → ℝ) → Fin n₂ → ℝ) : Prop :=
  ∀ u ∈ U, D.firstMatrix u *ᵥ x + D.recourseMatrix u *ᵥ y u ≤ D.b

noncomputable def Data.objective {m n₁ n₂ L : ℕ} (D : Data m n₁ n₂ L)
    (x : Fin n₁ → ℝ) : ℝ := D.c ⬝ᵥ x

end RobustSurvey.Affine


