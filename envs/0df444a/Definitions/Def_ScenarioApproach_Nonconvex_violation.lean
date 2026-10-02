-- Prove2me | Definitions.Def_ScenarioApproach_Nonconvex_violation
-- name    : ScenarioApproach_Nonconvex_violation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T18:33:12.134845+00:00
-- url     : https://prove2.me/theorems/dc632961-c48e-436d-a74b-251e929a8f8a
-- title:
--   Definition 3.1 — violation probability of a decision in a generic set
-- statement:
--   Let $\Theta$ be a generic set of decisions, and let $\Theta_\delta\subseteq\Theta$, $\delta\in\Delta$, be a family of constraint sets indexed by an uncertain parameter $\delta$ that takes values in a measurable space $\Delta$ carrying a probability $\mathbb P$.
--
--   The **violation set** of a decision $\theta\in\Theta$ is the set of parameters whose constraint $\theta$ does not satisfy, $\{\delta\in\Delta:\ \theta\notin\Theta_\delta\}$, and the **violation probability** (or **violation**) of $\theta$ is its probability,
--
--   $$
--   V(\theta):=\mathbb P\{\delta\in\Delta:\ \theta\notin\Theta_\delta\}.
--   $$
--
--   The violation measures how robust a decision is against the uncertain constraints. In the nonconvex setting of Section 8.6 it is the same notion as in Chapter 3, with $\Theta$ now an arbitrary set rather than a subset of $\mathbb R^d$.
--
--   **Formalization Note** $\Theta$ is an arbitrary type. The violation is the real number `(P {δ | θ ∉ Θδ δ}).toReal`; for a probability measure it lies in $[0,1]$. The theorems of this mission assume the constraint relation $\{(\theta,\delta):\theta\in\Theta_\delta\}$ is jointly measurable, which makes every violation set measurable.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 33, Definition 3.1 (used over a generic set on p. 102, §8.6)

import Mathlib

namespace ScenarioApproach.Nonconvex

/-- Definition 3.1 (violation set), over a generic decision set `Θ`. The violation set of a
decision `θ` is the set of uncertainty instances `δ` whose constraint `Θδ δ` does not
contain `θ`. -/
def violationSet {Θ Δ : Type*} (Θδ : Δ → Set Θ) (θ : Θ) : Set Δ :=
  {δ | θ ∉ Θδ δ}

/-- Definition 3.1 (violation probability). `V(θ) := ℙ{δ ∈ Δ : θ ∉ Θ_δ}`, as a real number;
for a probability measure `P` it lies in `[0, 1]`. -/
noncomputable def violation {Θ Δ : Type*} [MeasurableSpace Δ]
    (P : MeasureTheory.Measure Δ) (Θδ : Δ → Set Θ) (θ : Θ) : ℝ :=
  (P (violationSet Θδ θ)).toReal

end ScenarioApproach.Nonconvex


