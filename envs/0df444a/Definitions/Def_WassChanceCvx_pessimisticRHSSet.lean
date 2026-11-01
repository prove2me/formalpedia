-- Prove2me | Definitions.Def_WassChanceCvx_pessimisticRHSSet
-- name    : WassChanceCvx_pessimisticRHSSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:27:08.004077+00:00
-- url     : https://prove2.me/theorems/b2448086-5990-43d4-93e1-479bba4a96fb
-- title:
--   Feasible region $\mathcal X^p_{\mathrm R}$ of (P-CC) with right-hand-side uncertainty
-- statement:
--   With a constant matrix $A$ (rows $a_1,\dots,a_k$, continuous linear functionals on $E$) and an affine map $b:\mathbb R^n\to\mathbb R^k$,
--
--   $$
--   \mathcal X^p_{\mathrm R}=\Bigl\{x\in\mathbb R^n:\ \inf_{\mathbb Q\in\mathcal P}\mathbb Q\bigl[A\xi\le b(x)\bigr]\ge1-\epsilon\Bigr\},
--   $$
--
--   where $\mathcal P$ is the type-1 Wasserstein ball of radius $\delta$ around $\mathbb P$. This is $\mathcal X^p$ for the constant map $x\mapsto A$; it is the set whose convexity and closedness is the paper's Theorem 1.
--
--   **Formalization Note** Defined as `pessimisticSet` applied to the constant affine map with value $A$.
-- source:
--   Shen, Jiang, Convex Chance-Constrained Programs with Wasserstein Ambiguity, arXiv:2111.02486v2, Theorem 1, p.8

import Mathlib
import Definitions.Def_WassChanceCvx_pessimisticSet

open MeasureTheory

namespace WassChanceCvx

/-- **The feasible region `𝒳^p_R` of the joint (P-CC) with right-hand-side uncertainty.**
Shen, Jiang, arXiv:2111.02486v2, Theorem 1, p.8:
"`𝒳^p_R := {x ∈ ℝⁿ : inf_{ℚ∈𝒫} ℚ[Aξ ≤ b(x)] ≥ 1 − ϵ}`", with a constant matrix `A` and `b(x)` affine.

`pessimisticRHSSet A b P δ ϵ` is `𝒳^p` (`pessimisticSet`) for the constant map `x ↦ A`.

**Formalization Note.** The rows of `A` are `k` continuous linear functionals on `E`
(`ℝ^q` with a norm); `b : ℝⁿ → ℝ^k` is affine. -/
def pessimisticRHSSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    {n k : ℕ} (A : Fin k → StrongDual ℝ E) (b : (Fin n → ℝ) →ᵃ[ℝ] (Fin k → ℝ))
    (P : Measure E) (δ ϵ : ℝ) : Set (Fin n → ℝ) :=
  pessimisticSet (AffineMap.const ℝ (Fin n → ℝ) A) b P δ ϵ

end WassChanceCvx


