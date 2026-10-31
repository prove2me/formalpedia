-- Prove2me | Definitions.Def_RobustRiskOpt_Robust
-- name    : RobustRiskOpt_Robust
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:41:42.533839+00:00
-- url     : https://prove2.me/theorems/d85914d7-43ab-40f5-ac28-d454eef60caf
-- title:
--   Compatibility (Definition 1) and robustness against optimization (Definition 2)
-- statement:
--   Let $\mathcal G$ be a set of measurable functions $\mathbb R^n\to\mathbb R$ and let $(\mathcal Z,\pi)$ be a pseudo-metric space of $n$-random vectors. An objective functional $\rho$ is **compatible** with $(\mathcal G,\mathcal Z,\pi)$ if it maps $\mathcal G(\mathcal Z)=\{g(Z):Z\in\mathcal Z,\ g\in\mathcal G\}$ to $\mathbb R\cup\{+\infty\}$ and
--
--   $$
--   \rho(g(Y))=\rho(g(Z))\quad\text{for all }g\in\mathcal G\text{ and }Y,Z\in\mathcal Z\text{ with }\pi(Y,Z)=0.
--   $$
--
--   A compatible $\rho$ is **robust against optimization** at $X\in\mathcal Z$ for $(\mathcal G,\mathcal Z,\pi)$ if there is an optimizer $g_X\in\mathcal G_X(\rho)$ such that the function $Y\mapsto\rho(g_X(Y))$ is $\pi$-continuous at $Y=X$.
--
--   The idea is that the model $X$ is only a best-of-knowledge approximation of the true vector $Z$: the optimizer is chosen for $X$, and the position that is actually held is $g_X(Z)$. Robustness asks that this position have nearly the value that was optimized.
--
--   **Formalization Note** Continuity is `Tendsto` along the filter of $\pi$-neighbourhoods of $X$ inside $\mathcal Z$, which also covers the value $+\infty$. Compatibility is a separate predicate and is not part of `RobustAgainstOptimization`, so that a statement of non-robustness cannot hold merely because $\rho$ is not compatible.
-- source:
--   Embrechts–Schied–Wang, Robustness in the Optimization of Risk Measures, arXiv:1809.09268v3, 11 Feb 2021, Definitions 1–2, p.8

import Mathlib
import Definitions.Def_RobustRiskOpt_Admissible

open MeasureTheory Filter Topology
open scoped ENNReal

namespace RobustRiskOpt

variable {Ω : Type*} {n : ℕ}

/-- Definition 1, p.8 (Embrechts–Schied–Wang, arXiv:1809.09268v3): an objective functional `ρ` is
*compatible* with `(𝒢, 𝒵, π)` if it maps `𝒢(𝒵)` to `ℝ ∪ {+∞}` and `ρ(g(Y)) = ρ(g(Z))` for all
`g ∈ 𝒢` and `Y, Z ∈ 𝒵` with `π(Y, Z) = 0`. -/
def IsCompatible (𝒢 : Set (E n → ℝ)) (𝒵 : Set (Ω → E n)) (π : (Ω → E n) → (Ω → E n) → ℝ≥0∞)
    (ρ : (Ω → ℝ) → EReal) : Prop :=
  (∀ g ∈ 𝒢, ∀ Z ∈ 𝒵, ρ (g ∘ Z) ≠ ⊥) ∧
    ∀ g ∈ 𝒢, ∀ Y ∈ 𝒵, ∀ Z ∈ 𝒵, π Y Z = 0 → ρ (g ∘ Y) = ρ (g ∘ Z)

/-- Definition 2, p.8 (Embrechts–Schied–Wang, arXiv:1809.09268v3): `ρ` is *robust against
optimization at `X`* for `(𝒢, 𝒵, π)` if there is `g_X ∈ 𝒢_X(ρ)` such that `Y ↦ ρ(g_X(Y))` is
`π`-continuous at `Y = X`.

**Formalization Note** `π`-continuity at `X` on `𝒵` is the `Tendsto` along the filter of
`π`-neighbourhoods of `X` inside `𝒵`. This covers the value `+∞` of `ρ`. Definition 2 speaks of a
compatible `ρ`, but compatibility is deliberately not part of this `Prop`: it is `IsCompatible`,
and a statement of non-robustness asserts it separately, so that "not robust" cannot hold merely
because `ρ` is not compatible. -/
def RobustAgainstOptimization (𝒢 : Set (E n → ℝ)) (𝒵 : Set (Ω → E n))
    (π : (Ω → E n) → (Ω → E n) → ℝ≥0∞) (ρ : (Ω → ℝ) → EReal) (X : Ω → E n) : Prop :=
  ∃ g ∈ optimizers ρ X 𝒢,
    Tendsto (fun Y => ρ (g ∘ Y)) (comap (fun Y => π Y X) (𝓝 0) ⊓ 𝓟 𝒵) (𝓝 (ρ (g ∘ X)))

end RobustRiskOpt


