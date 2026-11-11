-- Prove2me | Definitions.Def_IteratedLP_Gaussian_Feasibility
-- name    : IteratedLP_Gaussian_Feasibility
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:20:50.990057+00:00
-- url     : https://prove2.me/theorems/39bea767-4458-4d0a-bd12-6c994f3748e8
-- title:
--   The Gaussian width $\varphi_1$ and the first-round feasibility condition (1.2)
-- statement:
--   Let $G\sim N(0,1)$. For $0<\rho\le1$ the **Gaussian width** is
--   $$\varphi_1(\rho)=\sup\{\mathbb E[GY]:|Y|\le1,\ \mathbb EY^2=\rho^2\},$$
--   where the supremum allows independent randomization: it runs over all joint laws of $(G,Y)$ on $\mathbb R^2$ whose first marginal is $N(0,1)$, with $|Y|\le1$ almost surely and $\mathbb EY^2=\rho^2$ (not only over $Y=f(G)$).
--
--   A pair $(\alpha,\kappa_1)$ satisfies the **first-round feasibility condition** (1.2) if
--   $$\alpha<\sup_{0<\rho\le1}\frac{\varphi_1(\rho)^2}{\mathbb E(\kappa_1-\rho G)_+^2}.$$
--   It ensures that the first LP of ITERATED-LP is feasible with high probability, and it is the hypothesis of Theorem 1.1.
--
--   **Formalization Note.** `gaussWidth ρ` is a real supremum over the subtype of admissible joint laws; for $0<\rho\le1$ this set is nonempty ($Y\equiv\rho$) and $\mathbb E[GY]\le\mathbb E|G|$, so it is the paper's supremum (and $\varphi_1\ge0$). `FirstRoundFeasible α κ₁` is written as "some $\rho\in(0,1]$ has $\alpha\,\mathbb E(\kappa_1-\rho G)_+^2<\varphi_1(\rho)^2$", which is equivalent because the denominator is positive, and which stays correct when the supremum is $+\infty$ (a real `sSup` would return $0$ there).
-- source:
--   Zhang, Li, State Evolution and Universality of Iterated Linear Programs for the Binary Perceptron, arXiv:2611.04294v1, p. 4, eq. (1.2)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace IteratedLP.Gaussian

/-- The randomized competitors in the Gaussian width `φ₁(ρ)` (eq. (1.2), p. 4): joint laws of
`(G, Y)` on `ℝ × ℝ` with `G ∼ N(0,1)`, `|Y| ≤ 1` almost surely and `E Y² = ρ²`. Taking joint
laws (couplings) rather than functions `Y = f(G)` is the "independent randomization" the paper
allows. -/
def widthCouplings (ρ : ℝ) : Set (Measure (ℝ × ℝ)) :=
  {π | IsProbabilityMeasure π ∧ π.map Prod.fst = gaussianReal 0 1 ∧
    (∀ᵐ w ∂π, |w.2| ≤ 1) ∧ ∫ w, w.2 ^ 2 ∂π = ρ ^ 2}

/-- The Gaussian width `φ₁(ρ) = sup {E[G Y] : |Y| ≤ 1, E Y² = ρ²}` (eq. (1.2)). For
`0 < ρ ≤ 1` the competitor set is nonempty (`Y ≡ ρ`) and `E[GY] ≤ E|G|`, so the real supremum
is the paper's. -/
noncomputable def gaussWidth (ρ : ℝ) : ℝ :=
  ⨆ π : widthCouplings ρ, ∫ w, w.1 * w.2 ∂(π : Measure (ℝ × ℝ))

/-- The first-round feasibility condition (1.2):
`α < sup_{0<ρ≤1} φ₁(ρ)² / E(κ₁ - ρG)₊²`, written as "some `ρ ∈ (0,1]` has
`α · E(κ₁ - ρG)₊² < φ₁(ρ)²`". The two are equivalent because the denominator is positive; the
existential form also covers the case where the supremum is `+∞`. -/
def FirstRoundFeasible (α κ₁ : ℝ) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
    α * ∫ g, (max (κ₁ - ρ * g) 0) ^ 2 ∂(gaussianReal 0 1) < gaussWidth ρ ^ 2

end IteratedLP.Gaussian


