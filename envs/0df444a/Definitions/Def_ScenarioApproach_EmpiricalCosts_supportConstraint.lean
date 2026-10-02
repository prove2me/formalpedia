-- Prove2me | Definitions.Def_ScenarioApproach_EmpiricalCosts_supportConstraint
-- name    : ScenarioApproach_EmpiricalCosts_supportConstraint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T18:16:02.32009+00:00
-- url     : https://prove2.me/theorems/1527ebcc-801a-4846-8d28-bc025d5e9bba
-- title:
--   Definitions 5.1, 5.4 — support constraints and fully supported min-max programs
-- statement:
--   Write the scenario program $\min_{\nu}\max_{i}\ell(\nu,\delta_i)$ in epigraph form: minimize $t$ over $(\nu,t)\in\mathbb R^{d-1}\times\mathbb R$ subject to the $m$ constraints $t\ge\ell(\nu,\delta_j)$, $j=1,\dots,m$. Its solution is $(\nu^*,\ell^*)$ with $\ell^*=\max_j\ell(\nu^*,\delta_j)$.
--
--   The constraint of scenario $i$ is a **support constraint** if its removal improves the solution, that is, if some $(\nu,t)$ satisfying all the other constraints has
--
--   $$
--   t<\ell^*=\max_{j=1,\dots,m}\ell(\nu^*,\delta_j).
--   $$
--
--   The problem is **fully supported** if for every $m\ge d$ the number of support constraints of the program with $m$ scenarios equals $d$ with probability $1$ (over the choice of the sample $(\delta_1,\dots,\delta_m)$ drawn independently from $\mathbb P$). Here $d$ is the number of variables $(\nu,t)$ of the epigraph form.
--
--   **Formalization Note** These are the book's Definitions 5.1 and 5.4, stated for the linear-cost program (5.1), transposed to (1.4) through its epigraph reformulation (p. 20): $\theta=(\nu,t)$, cost $c^T\theta=t$, $\Theta_\delta=\{(\nu,t):t\ge\ell(\nu,\delta)\}$. With $\nu$ in `EuclideanSpace ℝ (Fin n)`, $d=n+1$. The count is taken at every solution $\nu$ of the program with the sample, as in the book's convention that the solution is unique.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 57, Definition 5.1; p. 58, Definition 5.4; p. 20 (epigraph reformulation); p. 90

import Mathlib
import Definitions.Def_ScenarioApproach_EmpiricalCosts_scenarioProgram

namespace ScenarioApproach.EmpiricalCosts

/-- Definition 5.1 (support constraint), for the scenario program (1.4) in its epigraph form
`min_{(ν, t)} t` subject to `t ≥ ℓ(ν, δⱼ)`, `j = 1, …, m`, whose solution is
`(νstar, worstCost ℓ ω νstar)`: the constraint of scenario `i` is a support constraint if its
removal improves the solution, i.e. some `(ν, t)` satisfying every other constraint has
`t < max_j ℓ(νstar, δⱼ)`. -/
def IsSupportConstraint {n m : ℕ} {Δ : Type*} (ℓ : EuclideanSpace ℝ (Fin n) → Δ → ℝ)
    (ω : Fin m → Δ) (νstar : EuclideanSpace ℝ (Fin n)) (i : Fin m) : Prop :=
  ∃ ν : EuclideanSpace ℝ (Fin n), ∃ t : ℝ,
    (∀ j : Fin m, j ≠ i → ℓ ν (ω j) ≤ t) ∧ t < worstCost ℓ ω νstar

/-- The number of support constraints of the scenario program (1.4) with sample `ω` and
solution `νstar`. -/
noncomputable def numSupportConstraints {n m : ℕ} {Δ : Type*}
    (ℓ : EuclideanSpace ℝ (Fin n) → Δ → ℝ) (ω : Fin m → Δ) (νstar : EuclideanSpace ℝ (Fin n)) :
    ℕ := by
  classical
  exact (Finset.univ.filter fun i : Fin m => IsSupportConstraint ℓ ω νstar i).card

/-- Definition 5.4 (fully supported problem), for (1.4) with `ν ∈ ℝ^n`, so that the epigraph form
has `d = n + 1` variables: for every `m ≥ d`, with probability 1 over the sample
`(δ₁, …, δ_m)`, the scenario program has exactly `d` support constraints. -/
def FullySupported {n : ℕ} {Δ : Type*} [MeasurableSpace Δ] (P : MeasureTheory.Measure Δ)
    [MeasureTheory.IsProbabilityMeasure P] (ℓ : EuclideanSpace ℝ (Fin n) → Δ → ℝ) : Prop :=
  ∀ m : ℕ, n + 1 ≤ m →
    ∀ᵐ ω ∂(MeasureTheory.Measure.pi fun _ : Fin m => P),
      ∀ ν, IsSolution ℓ ω ν → numSupportConstraints ℓ ω ν = n + 1

end ScenarioApproach.EmpiricalCosts


