-- Prove2me | Definitions.Def_ScenarioApproach_Removal_scenarioProgram
-- name    : ScenarioApproach_Removal_scenarioProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T05:39:31.27367+00:00
-- url     : https://prove2.me/theorems/b2f70d85-6f07-47b1-9ad3-bdab329bb706
-- title:
--   Scenario program (3.1)/(3.3), the program without the constraints in I (5.9), Assumptions 3.4 and 3.6
-- statement:
--   Fix a domain $\Theta \subseteq \mathbb R^d$, constraint sets $\Theta_\delta \subseteq \mathbb R^d$ for $\delta \in \Delta$, and a cost vector $c \in \mathbb R^d$. For a sample $(\delta_1, \dots, \delta_m)$ the **scenario program** is
--
--   $$
--   \min_{\theta \in \Theta} c^{\mathsf T}\theta \quad \text{subject to } \theta \in \bigcap_{i=1,\dots,m} \Theta_{\delta_i},
--   $$
--
--   and a **solution** is a feasible point of minimal cost. Given a set $I \subseteq \{1,\dots,N\}$ of indexes, the program **without the constraints with index in $I$** is
--
--   $$
--   \min_{\theta \in \Theta} c^{\mathsf T}\theta \quad \text{subject to } \theta \in \bigcap_{i \in \{1,\dots,N\} - I} \Theta_{\delta_i},
--   $$
--
--   with solutions defined in the same way. Two standing assumptions of the book are packaged as predicates:
--
--   1. **Assumption 3.4 (convexity).** $\Theta$ and $\Theta_\delta$, $\delta \in \Delta$, are convex and closed sets.
--   2. **Assumption 3.6 (existence and uniqueness).** For every $m$ and every sample $(\delta_1, \dots, \delta_m)$, the solution of the scenario program with these $m$ constraints exists and is unique.
--
--   These are the objects about which every result of the chapter on constraint removal is stated: $\theta^*$ is the solution of the full program, $\theta^*_I$ the solution of the program without the constraints in $I$.
--
--   **Formalization Note** The feasible sets are $\Theta \cap \bigcap_i \Theta_{\delta_i}$ and $\Theta \cap \bigcap_{i \notin I}\Theta_{\delta_i}$; a solution is a feasible point $\theta$ with $\langle c,\theta\rangle \le \langle c,\theta'\rangle$ for every feasible $\theta'$. Samples of size $m$ are maps `Fin m → Δ`. Assumption 3.6 is required for every $m$ including $m = 0$ (the program on $\Theta$ alone) and for every sample, as on the page; the book's "program (3.1)" in Assumption 3.6 is read as the $m$-constraint program (3.3) introduced just before it.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 34, Eq. (3.1) and Assumption 3.4; p. 38, Eq. (3.3) and Assumption 3.6; p. 64, Eq. (5.9)

import Mathlib

namespace ScenarioApproach.Removal

/-- Feasible set of the scenario program (3.1)/(3.3) with the sample `ω = (δ_1, …, δ_m)`:
`Θ ∩ ⋂_{i} Θ_{δ_i}`. -/
def feasibleSet {d : ℕ} {Δ : Type*} (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d))) {m : ℕ} (ω : Fin m → Δ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  Θ ∩ ⋂ i, Θδ (ω i)

/-- `θ` is a solution of the scenario program (3.1)/(3.3) with sample `ω`: it is feasible and
minimizes the linear cost `⟪c, ·⟫` over the feasible set. -/
def IsSolution {d : ℕ} {Δ : Type*} (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d))) (c : EuclideanSpace ℝ (Fin d)) {m : ℕ}
    (ω : Fin m → Δ) (θ : EuclideanSpace ℝ (Fin d)) : Prop :=
  θ ∈ feasibleSet Θ Θδ ω ∧ ∀ θ' ∈ feasibleSet Θ Θδ ω, inner ℝ c θ ≤ inner ℝ c θ'

/-- Feasible set of the program (5.9): the scenario program with sample `ω = (δ_1, …, δ_N)`
without the constraints whose index lies in `I`, i.e. `Θ ∩ ⋂_{i ∉ I} Θ_{δ_i}`. -/
def feasibleSetWithout {d : ℕ} {Δ : Type*} (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d))) {N : ℕ} (ω : Fin N → Δ) (I : Finset (Fin N)) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  Θ ∩ ⋂ (i : Fin N) (_ : i ∉ I), Θδ (ω i)

/-- `θ` is a solution of program (5.9): feasible for the constraints with index outside `I`, and
a minimizer of `⟪c, ·⟫` over that feasible set. -/
def IsSolutionWithout {d : ℕ} {Δ : Type*} (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d))) (c : EuclideanSpace ℝ (Fin d)) {N : ℕ}
    (ω : Fin N → Δ) (I : Finset (Fin N)) (θ : EuclideanSpace ℝ (Fin d)) : Prop :=
  θ ∈ feasibleSetWithout Θ Θδ ω I ∧
    ∀ θ' ∈ feasibleSetWithout Θ Θδ ω I, inner ℝ c θ ≤ inner ℝ c θ'

/-- Assumption 3.4 (convexity): `Θ` and every `Θ_δ` are convex and closed. -/
def ConvexClosedConstraints {d : ℕ} {Δ : Type*} (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  Convex ℝ Θ ∧ IsClosed Θ ∧ ∀ δ, Convex ℝ (Θδ δ) ∧ IsClosed (Θδ δ)

/-- Assumption 3.6 (existence and uniqueness): for every `m` and every sample
`(δ_1, …, δ_m)`, the scenario program with these `m` constraints has exactly one solution. -/
def ExistsUniqueSolution {d : ℕ} {Δ : Type*} (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d))) (c : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ (m : ℕ) (ω : Fin m → Δ), ∃! θ, IsSolution Θ Θδ c ω θ

end ScenarioApproach.Removal


