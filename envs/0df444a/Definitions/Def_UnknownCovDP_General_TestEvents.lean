-- Prove2me | Definitions.Def_UnknownCovDP_General_TestEvents
-- name    : UnknownCovDP_General_TestEvents
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:10:30.241183+00:00
-- url     : https://prove2.me/theorems/9f1caf48-9d71-4c3b-b7ae-b348563bf832
-- title:
--   Section 2.2 — the test statistic $T_{\Sigma,y}$, $P_X$, $\hat\Sigma_X$ and the events $G_1,G_2,G_3$
-- statement:
--   For $\Sigma$ and $y,z\in\mathbb R^d$, the **test statistic** is
--   $$T_{\Sigma,y}(z)=\frac{\langle y,z\rangle^2}{y^\top\Sigma y}\quad\text{if }y^\top\Sigma y>0,\qquad T_{\Sigma,y}(z)=0\quad\text{otherwise.}$$
--   For a dataset $X=(x_1,\dots,x_n)$, $P_X$ is the orthogonal projection onto $\operatorname{span}\{x_1,\dots,x_n\}$ and $\hat\Sigma_X=\tfrac1n XX^\top=\tfrac1n\sum_i x_ix_i^\top$ is the empirical covariance. With constants $C,\lambda,\alpha$, the good event is $G=G_1\cap G_2\cap G_3$, where
--
--   1. $G_1$: $\ \tfrac{k}{2n}P_X\preceq\hat\Sigma_X\preceq\tfrac{2k}{n}P_X$;
--   2. $G_2$: $\ y^\top(\Sigma-P_X)y\le 2C\alpha^2k/d$;
--   3. $G_3$: $\ y^\top\Sigma y\ge\lambda^2$.
--
--   These objects separate the data point's score from a fresh point's score, which is what the proof of the sampling lower bound compares.
--
--   **Formalization Note** The Loewner inequalities are stated as positive semidefiniteness of the differences. $P_X$ is the matrix of Mathlib's `starProjection`.
-- source:
--   Gaucher, Linder, Smith, Ullman, Zakynthinou, Dimension-Free Private Mean Estimation is Impossible Without the Covariance, STOC 2027 submission #573 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/573.pdf, §2.2, printed p. 13 (PDF p. 14)

import Mathlib
import Definitions.Def_UnknownCovDP_General_Sampler

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace UnknownCovDP.General

/-!
# The test statistic and the good event

Printed p. 13, PDF p. 14 of Gaucher, Linder, Smith, Ullman, Zakynthinou, STOC 2027 submission #573:
the statistic `T_{Σ,y}`, the projector `P_X`, the empirical covariance `Σ̂_X = (1/n) X Xᵀ`, and the
events `G₁, G₂, G₃`. The Loewner inequalities are written as positive semidefiniteness of the
differences.
-/

/-- The test statistic: `T_{S,y}(z) = ⟨y,z⟩² / (yᵀ S y)` if `yᵀ S y > 0`, and `0` otherwise. -/
noncomputable def testStat {d : ℕ} (S : Mat d) (y z : Vec d) : ℝ :=
  if 0 < quadForm S y then (inner ℝ y z) ^ 2 / quadForm S y else 0

/-- `P_X`: the matrix of the orthogonal projection onto `span {x₁, …, xₙ}`. -/
noncomputable def spanProj {d n : ℕ} (X : Fin n → Vec d) : Mat d :=
  Matrix.of fun i j =>
    (Submodule.span ℝ (Set.range X)).starProjection (EuclideanSpace.single j (1 : ℝ)) i

/-- The empirical covariance `Σ̂_X = (1/n) X Xᵀ = (1/n) ∑ᵢ xᵢ xᵢᵀ`. -/
noncomputable def empCov {d n : ℕ} (X : Fin n → Vec d) : Mat d :=
  (n : ℝ)⁻¹ • ∑ i, Matrix.vecMulVec (X i).ofLp (X i).ofLp

/-- `G₁ : (k/2n) · P_X ⪯ Σ̂_X ⪯ (2k/n) · P_X`. -/
def EventG1 {d n : ℕ} (k : ℕ) (X : Fin n → Vec d) : Prop :=
  (empCov X - ((k : ℝ) / (2 * n)) • spanProj X).PosSemidef ∧
    (((2 * k : ℝ) / n) • spanProj X - empCov X).PosSemidef

/-- `G₂ : yᵀ (S − P_X) y ≤ 2 C α² k / d`. -/
def EventG2 {d n : ℕ} (k : ℕ) (C α : ℝ) (S : Mat d) (X : Fin n → Vec d) (y : Vec d) : Prop :=
  quadForm (S - spanProj X) y ≤ 2 * C * α ^ 2 * k / d

/-- `G₃ : yᵀ S y ≥ lam²`. -/
def EventG3 {d : ℕ} (lam : ℝ) (S : Mat d) (y : Vec d) : Prop :=
  lam ^ 2 ≤ quadForm S y

/-- The event `G = G₁ ∩ G₂ ∩ G₃` on triples `(S, X, y)`. -/
def EventG {d n : ℕ} (k : ℕ) (C lam α : ℝ) (S : Mat d) (X : Fin n → Vec d) (y : Vec d) : Prop :=
  EventG1 k X ∧ EventG2 k C α S X y ∧ EventG3 lam S y

end UnknownCovDP.General


