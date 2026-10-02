-- Prove2me | Definitions.Def_ScenarioApproach_Nonconvex_scenarioProgram
-- name    : ScenarioApproach_Nonconvex_scenarioProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T18:36:45.518992+00:00
-- url     : https://prove2.me/theorems/25fc9c7a-a328-4b5b-b9e6-15a849a649a0
-- title:
--   Eq. (8.12) — the nonconvex scenario program and its solution
-- statement:
--   Let $\Theta$ be a generic set, $f:\Theta\to\mathbb R$ a real-valued cost, and $\Theta_\delta\subseteq\Theta$, $\delta\in\Delta$, constraint sets; no convexity or other structure is assumed. Given a sample $\delta_1,\dots,\delta_N$, the **scenario program** is
--
--   $$
--   \min_{\theta\in\Theta} f(\theta)\quad\text{subject to}\quad \theta\in\bigcap_{i=1,\dots,N}\Theta_{\delta_i}.
--   $$
--
--   For a subset $I\subseteq\{1,\dots,N\}$ of the constraints, the program **with only the constraints in $I$ in place** has feasible set $\bigcap_{i\in I}\Theta_{\delta_i}$ (all of $\Theta$ when $I=\emptyset$). A point $\theta$ is a **solution** of it if it is feasible and $f(\theta)\le f(\theta')$ for every feasible $\theta'$, and it is **the solution** if moreover every solution equals $\theta$.
--
--   Taking $I=\{1,\dots,N\}$ gives program (8.12) itself; the programs with fewer constraints are needed to define support sets (Definition 8.8).
--
--   **Formalization Note** A sample is `ω : Fin N → Δ` (indices $0,\dots,N-1$) and subsets of constraints are `Finset (Fin N)`. `IsSolutionOn` does not assert uniqueness; `IsUniqueSolutionOn` does. Neither asserts that a solution exists.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 102, Eq. (8.12)

import Mathlib

namespace ScenarioApproach.Nonconvex

/-- Feasible set of program (8.12) with only the constraints indexed by `I` in place:
`⋂_{i ∈ I} Θ_{δᵢ}` inside the generic decision set `Θ`. For `I = Finset.univ` it is the
feasible set of the program with all `N` constraints; for `I = ∅` it is all of `Θ`. -/
def feasibleOn {Θ Δ : Type*} {N : ℕ} (Θδ : Δ → Set Θ) (ω : Fin N → Δ) (I : Finset (Fin N)) :
    Set Θ :=
  {θ | ∀ i ∈ I, θ ∈ Θδ (ω i)}

/-- `θ` is a solution of program (8.12) `min_{θ ∈ Θ} f(θ)` subject to the constraints indexed
by `I`: it is feasible and no feasible point has a smaller cost. -/
def IsSolutionOn {Θ Δ : Type*} {N : ℕ} (f : Θ → ℝ) (Θδ : Δ → Set Θ) (ω : Fin N → Δ)
    (I : Finset (Fin N)) (θ : Θ) : Prop :=
  θ ∈ feasibleOn Θδ ω I ∧ ∀ θ' ∈ feasibleOn Θδ ω I, f θ ≤ f θ'

/-- `θ` is *the* solution of program (8.12) with the constraints indexed by `I`: it is a
solution and every solution equals it. -/
def IsUniqueSolutionOn {Θ Δ : Type*} {N : ℕ} (f : Θ → ℝ) (Θδ : Δ → Set Θ) (ω : Fin N → Δ)
    (I : Finset (Fin N)) (θ : Θ) : Prop :=
  IsSolutionOn f Θδ ω I θ ∧ ∀ θ', IsSolutionOn f Θδ ω I θ' → θ' = θ

end ScenarioApproach.Nonconvex


