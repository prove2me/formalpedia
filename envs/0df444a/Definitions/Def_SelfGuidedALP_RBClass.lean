-- Prove2me | Definitions.Def_SelfGuidedALP_RBClass
-- name    : SelfGuidedALP_RBClass
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:22:43.207988+00:00
-- url     : https://prove2.me/theorems/5237bf1a-3139-43b0-bc02-85257abd39ce
-- title:
--   A class of random basis functions $(\Theta,\rho,\varphi)$
-- statement:
--   A **class of random basis functions** consists of a parameter set $\Theta\subseteq\mathbb R^{d+1}$, a sampling density $\rho\ge0$ on $\Theta$ with $\int_\Theta\rho(\theta)\,\mathrm d\theta=1$, and a scalar mapping $\varphi:\mathbb R\to\mathbb R$.
--
--   Every value function approximation of the mission is built from the basis functions of such a class.
--
--   **Formalization Note** The integrals $\mathrm d\theta$ of the paper are read as Lebesgue integrals on $\mathbb R^{d+1}$, so $\rho$ is a density with respect to Lebesgue measure. The regularity of $\varphi$ belongs to Assumption 2, not to the class.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, §2.2, p.8

import Mathlib

open MeasureTheory

namespace SelfGuidedALP

/-- A class of random basis functions on `ℝᵈ`: a parameter set `Θ ⊆ ℝ^{d+1}`, a sampling density
`ρ` on `Θ` with respect to Lebesgue measure, and a scalar mapping `ϕ : ℝ → ℝ`
(Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, §2.2, p.8).

**Formalization Note.** `ρ` is a nonnegative measurable real function with `∫_Θ ρ = 1`. The
integrals `dθ` of the paper are Lebesgue integrals on `ℝ^{d+1}`. The regularity of `ϕ` is not part
of the class; it is in `Assumption2`. -/
structure RBClass (d : ℕ) where
  /-- The parameter set `Θ ⊆ ℝ^{d+1}`; index `0` of `θ` is the intercept coordinate `θ₀`. -/
  Θ : Set (EuclideanSpace ℝ (Fin (d + 1)))
  /-- The sampling density `ρ`. -/
  ρ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ
  /-- The scalar mapping `ϕ`. -/
  ϕ : ℝ → ℝ
  measurableSet_Θ : MeasurableSet Θ
  measurable_ρ : Measurable ρ
  ρ_nonneg : ∀ θ, 0 ≤ ρ θ
  lintegral_ρ : ∫⁻ θ in Θ, ENNReal.ofReal (ρ θ) = 1

end SelfGuidedALP


