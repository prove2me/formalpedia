-- Prove2me | Definitions.Def_GoldenRatioVI_Fixed_IsGRAALRun
-- name    : GoldenRatioVI_Fixed_IsGRAALRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:55:40.073213+00:00
-- url     : https://prove2.me/theorems/12ffa270-69ae-47e9-88e9-dc73f6b2e9fe
-- title:
--   The Golden Ratio Algorithm (GRAAL) (6) with a fixed step $\lambda$
-- statement:
--   Let $\varphi = \frac{\sqrt5+1}{2}$ be the golden ratio, so $\varphi^2 = 1+\varphi$. Let $g:\mathcal E\to(-\infty,+\infty]$, $F:\mathcal E\to\mathcal E$ and $\lambda\in\mathbb R$.
--
--   1. Two sequences $(z^k)_{k\ge0}$, $(\bar z^k)_{k\ge0}$ satisfy the **golden averaging** step if for every $k\ge1$
--   $$\bar z^k = \frac{(\varphi-1)z^k + \bar z^{k-1}}{\varphi}.$$
--   2. They form a **run of the Golden Ratio Algorithm** (GRAAL) with step $\lambda$ if, in addition, for every $k\ge1$
--   $$z^{k+1} = \operatorname{prox}_{\lambda g}\big(\bar z^k - \lambda F(z^k)\big),$$
--   where the proximal step is the argmin predicate for the function $x\mapsto\lambda g(x)$.
--
--   The starting points $z^1$ and $\bar z^0$ are arbitrary; the entry $z^0$ is not used.
--
--   **Formalization Note** Sequences are `ℕ → E` indexed as in the paper. The golden ratio is Mathlib's `Real.goldenRatio` $=(1+\sqrt5)/2$. The function $\lambda g$ is `fun x => (λ : EReal) * g x`.
-- source:
--   Malitsky, Golden Ratio Algorithms for Variational Inequalities, preprint (Optimization Online 6598, 2018), p. 4, Eq. (6)

import Mathlib
import Definitions.Def_GoldenRatioVI_Shared_IsProxPoint

namespace GoldenRatioVI.Fixed

/-- The averaging step of (6): for every `k ≥ 1`,
`z̄ᵏ = ((φ - 1) zᵏ + z̄ᵏ⁻¹) / φ` with `φ = (√5 + 1)/2` the golden ratio. -/
def IsGoldenAveraging {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z zbar : ℕ → E) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    zbar k = Real.goldenRatio⁻¹ • ((Real.goldenRatio - 1) • z k + zbar (k - 1))

/-- A run of the Golden Ratio Algorithm (6) with fixed step `lam`, started from arbitrary
`z¹, z̄⁰` (the entry `z 0` is unused): for every `k ≥ 1`,
`z̄ᵏ = ((φ - 1) zᵏ + z̄ᵏ⁻¹) / φ` and `zᵏ⁺¹ = prox_{λ g}(z̄ᵏ - λ F(zᵏ))`, the latter as the
argmin predicate `IsProxPoint` for the function `x ↦ λ · g x`. -/
def IsGRAALRun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → EReal) (F : E → E) (lam : ℝ) (z zbar : ℕ → E) : Prop :=
  IsGoldenAveraging z zbar ∧
    ∀ k : ℕ, 1 ≤ k →
      GoldenRatioVI.Shared.IsProxPoint (fun x => (lam : EReal) * g x) (zbar k - lam • F (z k)) (z (k + 1))

end GoldenRatioVI.Fixed


