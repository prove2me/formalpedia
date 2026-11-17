-- Prove2me | Definitions.Def_AggCG_Supplement_ridgeClass
-- name    : AggCG_Supplement_ridgeClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:26:46.437594+00:00
-- url     : https://prove2.me/theorems/900bb5f0-c732-449b-88dd-e1a0cb82ff54
-- title:
--   Scalar ridge validation-loss class
-- statement:
--   A ridge task consists of full-column-rank training data $(X,y)$ and one validation point $(r,t)$. At $\lambda>0$, its fitted coefficients are $(X^\top X+\lambda I)^{-1}X^\top y$ and its loss is $(r^\top\widehat w(\lambda)-t)^2$.
--
--   The scalar ridge class contains these loss functions over all full-rank tasks with a fixed number of coefficients.
-- source:
--   Sharma, STOC 2027 submission (manuscript sha256 f7ea0248…), §N and Theorem N.3, p.78, PDF p.79

import Mathlib

namespace AggCG.Supplement

open Matrix

/-- A scalar-ridge task with `p` coefficients (Sharma, *Computational Complexity of Data-Driven
Configuration for Integer Programming, Clustering, and Learning Algorithms*, STOC 2027 submission
(manuscript sha256 f7ea0248…), §N, p.78, PDF p.79): training data `(X, y)` with `n` samples and one
validation point `(r, t)`. -/
structure RidgeTask (p : ℕ) where
  /-- Number of training samples. -/
  n : ℕ
  /-- Training design. -/
  X : Matrix (Fin n) (Fin p) ℝ
  /-- Training response. -/
  y : Fin n → ℝ
  /-- Validation features. -/
  r : Fin p → ℝ
  /-- Validation target. -/
  t : ℝ

namespace RidgeTask

variable {p : ℕ}

/-- Full column rank training design. -/
def FullRank (τ : RidgeTask p) : Prop := Function.Injective τ.X.mulVec

/-- The ridge fit `ŵ(λ) = (XᵀX + λI)⁻¹ Xᵀy`. -/
noncomputable def fit (τ : RidgeTask p) (lam : ℝ) : Fin p → ℝ :=
  (τ.Xᵀ * τ.X + lam • (1 : Matrix (Fin p) (Fin p) ℝ))⁻¹ *ᵥ (τ.Xᵀ *ᵥ τ.y)

/-- The nonnegative squared validation loss `(rᵀŵ(λ) − t)²`. -/
noncomputable def loss (τ : RidgeTask p) (lam : ℝ) : ℝ := (τ.r ⬝ᵥ τ.fit lam - τ.t) ^ 2

end RidgeTask

/-- The scalar regularization-parameter family `F = {τ ↦ (rᵀŵ(λ) − t)² : λ > 0}` on the domain of all
full-column-rank tasks with `p` coefficients (Theorem N.3, p.78).

**Formalization Note** For `λ > 0` the matrix `XᵀX + λI` is invertible, so the inverse is the actual
inverse. -/
def ridgeClass (p : ℕ) : Set ({τ : RidgeTask p // τ.FullRank} → ℝ) :=
  {g | ∃ lam > 0, ∀ τ, g τ = τ.1.loss lam}

end AggCG.Supplement


