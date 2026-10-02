-- Prove2me | Definitions.Def_ScenarioApproach_Generalization_violation
-- name    : ScenarioApproach_Generalization_violation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T17:06:58.479359+00:00
-- url     : https://prove2.me/theorems/a0932505-3838-427b-b0c6-2d103ad0424f
-- title:
--   Definition 3.1 — violation set and violation probability
-- statement:
--   Let $\Theta_\delta\subseteq\mathbb R^d$, $\delta\in\Delta$, be a family of constraint sets indexed by an uncertain parameter $\delta$ that takes values in a measurable space $\Delta$ carrying a probability $\mathbb P$.
--
--   The **violation set** of a decision $\theta\in\mathbb R^d$ is the set of parameters whose constraint $\theta$ does not satisfy,
--
--   $$
--   \{\delta\in\Delta:\ \theta\notin\Theta_\delta\},
--   $$
--
--   and the **violation probability** (or just **violation**) of $\theta$ is the probability of its violation set,
--
--   $$
--   V(\theta):=\mathbb P\{\delta\in\Delta:\ \theta\notin\Theta_\delta\}.
--   $$
--
--   The violation quantifies how robust a decision is against the uncertain constraints; it involves no optimization. Every generalization result of the scenario approach is a statement about the violation of the scenario solution.
--
--   **Formalization Note** The decision space is `EuclideanSpace ℝ (Fin d)`. The violation is the real number `(P {δ | θ ∉ Θδ δ}).toReal`; for a probability measure it lies in $[0,1]$. When the violation set is not measurable, `P` is evaluated as an outer measure; the theorems of this mission assume the constraint relation is jointly measurable, which makes every violation set measurable.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 33, Definition 3.1

import Mathlib

namespace ScenarioApproach.Generalization

/-- Definition 3.1 (violation set). The violation set of a decision `θ` is the set of
uncertainty instances `δ` whose constraint `Θδ δ` does not contain `θ`. -/
def violationSet {d : ℕ} {Δ : Type*} (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (θ : EuclideanSpace ℝ (Fin d)) : Set Δ :=
  {δ | θ ∉ Θδ δ}

/-- Definition 3.1 (violation probability). `V(θ) := ℙ{δ ∈ Δ : θ ∉ Θ_δ}`, as a real number;
for a probability measure `P` it lies in `[0, 1]`. -/
noncomputable def violation {d : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : MeasureTheory.Measure Δ) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (θ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (P (violationSet Θδ θ)).toReal

end ScenarioApproach.Generalization


