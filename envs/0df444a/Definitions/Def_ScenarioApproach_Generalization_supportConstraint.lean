-- Prove2me | Definitions.Def_ScenarioApproach_Generalization_supportConstraint
-- name    : ScenarioApproach_Generalization_supportConstraint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T17:20:21.489357+00:00
-- url     : https://prove2.me/theorems/7abc0229-0d15-4065-80bc-4968c210ff79
-- title:
--   Definitions 5.1, 5.4 — support constraints and fully supported problems
-- statement:
--   Consider the scenario program with $m$ sampled constraints $\theta\in\Theta_{\delta_1},\dots,\theta\in\Theta_{\delta_m}$, domain $\Theta$, cost $c^T\theta$, and let $\theta^*$ be its solution.
--
--   1. **Support constraint (Definition 5.1).** The constraint $\theta\in\Theta_{\delta_i}$ is a support constraint if its removal improves the solution, that is, if the program without that constraint has a feasible point with strictly smaller cost:
--   $$
--   \exists\,\theta\in\Theta\ \text{with}\ \theta\in\Theta_{\delta_j}\ \text{for all}\ j\ne i\ \text{and}\ c^T\theta<c^T\theta^*.
--   $$
--   2. **Number of support constraints.** The number of indices $i\in\{1,\dots,m\}$ whose constraint is a support constraint.
--   3. **Fully supported problem (Definition 5.4).** The scenario optimization problem, characterized by $c$, $\Theta$, $\{\Theta_\delta,\ \delta\in\Delta\}$ and $\mathbb P$, is fully supported if for every $m\ge d$ the number of support constraints of the program with $m$ constraints is equal to $d$ with probability 1 with respect to the choice of the i.i.d. sample $(\delta_1,\dots,\delta_m)\sim\mathbb P^m$.
--
--   Support constraints are the constraints that actually determine the solution; for convex programs there are at most $d$ of them, and fully supported problems, where there are always exactly $d$, are the case in which the generalization bound of the scenario approach is attained with equality.
--
--   **Formalization Note** Because the solution may be improved to any feasible point of the reduced program, "the removal improves the solution" is stated as the existence of a feasible point of the reduced program with strictly smaller cost than $\theta^*$; this is equivalent to the book's wording whenever the reduced program has a solution. The solution $\theta^*$ is an argument of the definition. In `FullySupported`, "with probability 1" is `∀ᵐ` under the product measure `Measure.pi (fun _ : Fin m => P)`, and the count is required at every solution of the program (under Assumption 3.6 there is exactly one).
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 57, Definition 5.1 and program (5.1); p. 58, Definition 5.4

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_scenarioProgram

namespace ScenarioApproach.Generalization

/-- Definition 5.1 (support constraint). For the scenario program with constraints
`ω 0, …, ω (m-1)` and solution `θstar`, the constraint `θ ∈ Θ_{δᵢ}` is a support constraint if
removing it improves the solution: the program without constraint `i` has a feasible point
(in `Θ` and in every `Θ_{δⱼ}`, `j ≠ i`) whose cost is strictly smaller than `cᵀθstar`. -/
def IsSupportConstraint {d m : ℕ} {Δ : Type*} (c : EuclideanSpace ℝ (Fin d))
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (ω : Fin m → Δ) (θstar : EuclideanSpace ℝ (Fin d)) (i : Fin m) : Prop :=
  ∃ θ ∈ Θ, (∀ j : Fin m, j ≠ i → θ ∈ Θδ (ω j)) ∧ inner ℝ c θ < inner ℝ c θstar

/-- The number of support constraints of the scenario program with constraints `ω` and
solution `θstar`. -/
noncomputable def numSupportConstraints {d m : ℕ} {Δ : Type*} (c : EuclideanSpace ℝ (Fin d))
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (ω : Fin m → Δ) (θstar : EuclideanSpace ℝ (Fin d)) : ℕ := by
  classical
  exact (Finset.univ.filter fun i : Fin m => IsSupportConstraint c Θ Θδ ω θstar i).card

/-- Definition 5.4 (fully supported problem). The problem `(c, Θ, {Θ_δ}, ℙ)` is fully supported
if for every `m ≥ d`, for `ℙ^m`-almost every sample `(δ₁, …, δ_m)`, the scenario program with
these `m` constraints has exactly `d` support constraints (counted at its solution). -/
def FullySupported {d : ℕ} {Δ : Type*} [MeasurableSpace Δ] (c : EuclideanSpace ℝ (Fin d))
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (P : MeasureTheory.Measure Δ) [MeasureTheory.IsProbabilityMeasure P] : Prop :=
  ∀ m : ℕ, d ≤ m →
    ∀ᵐ ω ∂(MeasureTheory.Measure.pi fun _ : Fin m => P),
      ∀ θ, IsSolution c Θ Θδ ω θ → numSupportConstraints c Θ Θδ ω θ = d

end ScenarioApproach.Generalization


