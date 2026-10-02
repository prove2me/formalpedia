-- Prove2me | Definitions.Def_ScenarioApproach_Generalization_scenarioProgram
-- name    : ScenarioApproach_Generalization_scenarioProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T17:12:24.608411+00:00
-- url     : https://prove2.me/theorems/a4694856-5639-4ade-9c8f-746a2ce53c35
-- title:
--   Eqs. (3.1), (3.3) — feasible set and solution of the scenario program
-- statement:
--   Fix a cost vector $c\in\mathbb R^d$, a domain $\Theta\subseteq\mathbb R^d$ and constraint sets $\Theta_\delta\subseteq\mathbb R^d$, $\delta\in\Delta$. For a sample $(\delta_1,\dots,\delta_m)$ of $m=0,1,2,\dots$ parameters, the **scenario program** is
--
--   $$
--   \min_{\theta\in\Theta} c^T\theta \quad\text{subject to}\quad \theta\in\bigcap_{i=1,\dots,m}\Theta_{\delta_i}.
--   $$
--
--   Its **feasible set** is $\Theta\cap\bigcap_{i=1}^m\Theta_{\delta_i}$ (equal to $\Theta$ when $m=0$), and a point $\theta$ is a **solution** of the program if it is feasible and $c^T\theta\le c^T\theta'$ for every feasible $\theta'$.
--
--   The program with $m=N$ is the scenario program $\mathrm{SP}_N$ (3.1) whose solution $\theta^*$ is the object of every theorem in this mission; the programs with other values of $m$ enter Assumption 3.6 (existence and uniqueness of the solution for every $m$ and every sample).
--
--   **Formalization Note** A sample of size $m$ is a function `ω : Fin m → Δ` (indices $0,\dots,m-1$ instead of $1,\dots,m$). The cost $c^T\theta$ is the Euclidean inner product `inner ℝ c θ` on `EuclideanSpace ℝ (Fin d)`. `IsSolution` does not assert uniqueness; uniqueness is Assumption 3.6, a hypothesis of the theorems.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 34, Eq. (3.1); p. 38, Eq. (3.3)

import Mathlib

namespace ScenarioApproach.Generalization

/-- Feasible set of the scenario program (3.3) with the `m` sampled constraints
`ω 0, …, ω (m-1)`: `Θ ∩ ⋂ᵢ Θ_{δᵢ}`. For `m = 0` it is `Θ`. -/
def feasibleSet {d m : ℕ} {Δ : Type*} (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d))) (ω : Fin m → Δ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  Θ ∩ ⋂ i, Θδ (ω i)

/-- `θ` is a solution of the scenario program (3.1)/(3.3) `min_{θ ∈ Θ} cᵀθ` subject to
`θ ∈ ⋂ᵢ Θ_{δᵢ}`: it is feasible and no feasible point has a smaller cost. -/
def IsSolution {d m : ℕ} {Δ : Type*} (c : EuclideanSpace ℝ (Fin d))
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (ω : Fin m → Δ) (θ : EuclideanSpace ℝ (Fin d)) : Prop :=
  θ ∈ feasibleSet Θ Θδ ω ∧ ∀ θ' ∈ feasibleSet Θ Θδ ω, inner ℝ c θ ≤ inner ℝ c θ'

end ScenarioApproach.Generalization


