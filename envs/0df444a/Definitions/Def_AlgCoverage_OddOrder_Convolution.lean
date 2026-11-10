-- Prove2me | Definitions.Def_AlgCoverage_OddOrder_Convolution
-- name    : AlgCoverage_OddOrder_Convolution
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:45:31.091717+00:00
-- url     : https://prove2.me/theorems/44d1365a-fb28-457d-893a-a45843ca22bb
-- title:
--   Subprobabilities, Haar probability and convolution on a finite group
-- statement:
--   On a finite group $K$, a **subprobability** is a nonnegative mass function $\mu:K\to\mathbb R$ with total mass $\sum_z\mu(z)\le1$. **Haar probability** is $u_K(z)=|K|^{-1}$. The **convolution** is
--   $$(\mu_1*\mu_2)(z)=\sum_{x\in K}\mu_1(x)\,\mu_2(x^{-1}z),$$
--   the law of the product of independent variables in the stated order.
-- source:
--   Lin, Sharp Second-Order Thresholds for Random Algebraic Coverage, STOC 2027 submission (manuscript sha256 9db96430…), p. 7 (PDF 8), §2.4; p. 22 (PDF 23), §7

import Mathlib

namespace AlgCoverage.OddOrder

/-! Subprobabilities and convolution on a finite group (Lin, §2.4, printed p. 7 / PDF 8, and §7,
printed p. 22 / PDF 23). -/

/-- A subprobability on a finite group `K`: a nonnegative mass function with total mass at most one. -/
def IsSubprob {K : Type*} [Fintype K] (μ : K → ℝ) : Prop :=
  (∀ z, 0 ≤ μ z) ∧ ∑ z, μ z ≤ 1

/-- Haar (uniform) probability `u_K(z) = |K|⁻¹`. -/
noncomputable def haar (K : Type*) [Fintype K] : K → ℝ :=
  fun _ => 1 / (Fintype.card K : ℝ)

/-- Convolution `(μ₁ ∗ μ₂)(z) = ∑_{x ∈ K} μ₁(x) μ₂(x⁻¹ z)` (the law of a product in the stated order). -/
def conv {K : Type*} [Group K] [Fintype K] (μ₁ μ₂ : K → ℝ) : K → ℝ :=
  fun z => ∑ x : K, μ₁ x * μ₂ (x⁻¹ * z)

end AlgCoverage.OddOrder


