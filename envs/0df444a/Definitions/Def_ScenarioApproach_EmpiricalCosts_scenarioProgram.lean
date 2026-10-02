-- Prove2me | Definitions.Def_ScenarioApproach_EmpiricalCosts_scenarioProgram
-- name    : ScenarioApproach_EmpiricalCosts_scenarioProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T17:53:06.419251+00:00
-- url     : https://prove2.me/theorems/48bddd1a-fa48-4f0d-a009-11cdf54cb7f8
-- title:
--   Eq. (1.4) — the min-max scenario program and its solution
-- statement:
--   Let $\ell(\nu,\delta)$ be a real-valued loss depending on a decision $\nu\in\mathbb R^{d-1}$ and an uncertain parameter $\delta$ ranging over a set $\Delta$. Given a sample $(\delta_1,\dots,\delta_m)$ of $m\ge1$ scenarios, the **scenario program** is the min-max problem
--
--   $$
--   \min_{\nu\in\mathbb R^{d-1}}\ \Big[\max_{i=1,\dots,m}\ \ell(\nu,\delta_i)\Big].
--   $$
--
--   The **worst-case cost** of a decision $\nu$ on the sample is $\max_{i=1,\dots,m}\ell(\nu,\delta_i)$, and $\nu$ is a **solution** of the program if no decision has a smaller worst-case cost. With $m=N$ this is the program $\mathrm{SP}_N$ of the book; its solution is denoted $\nu^*$ and its optimal value $\ell^*=\max_i\ell(\nu^*,\delta_i)$.
--
--   The program is the basic object of every result in this mission: the empirical costs, their risks and the support constraints are all read off its solution.
--
--   **Formalization Note** The decision space is `EuclideanSpace ℝ (Fin n)` with $n=d-1$, so the book's $d$ is $n+1$. A sample of size $m$ is `ω : Fin m → Δ`. The worst-case cost is the supremum `⨆ i, ℓ ν (ω i)`, which for $m\ge1$ is the maximum over a finite nonempty index set; for $m=0$ it is the junk value $0$, and the theorems only use programs with $m\ge1$. `IsSolution` does not assert uniqueness; existence and uniqueness are hypotheses of the theorems.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 7, Eq. (1.4); p. 6 (standing convexity assumption)

import Mathlib

namespace ScenarioApproach.EmpiricalCosts

/-- The worst-case cost `max_{i=1,…,m} ℓ(ν, δᵢ)` of the decision `ν` on the sample
`ω 0, …, ω (m-1)`, the objective of the scenario program (1.4). For `m ≥ 1` the supremum is a
maximum over a finite nonempty index set; for `m = 0` it is the junk value `0`, and this mission
only evaluates it for `m ≥ 1`. -/
noncomputable def worstCost {n m : ℕ} {Δ : Type*} (ℓ : EuclideanSpace ℝ (Fin n) → Δ → ℝ)
    (ω : Fin m → Δ) (ν : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⨆ i, ℓ ν (ω i)

/-- `ν` is a solution of the scenario program (1.4) `min_{ν ∈ ℝ^{d-1}} max_{i=1,…,m} ℓ(ν, δᵢ)`
with the sample `ω`: no decision has a smaller worst-case cost. -/
def IsSolution {n m : ℕ} {Δ : Type*} (ℓ : EuclideanSpace ℝ (Fin n) → Δ → ℝ)
    (ω : Fin m → Δ) (ν : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ ν' : EuclideanSpace ℝ (Fin n), worstCost ℓ ω ν ≤ worstCost ℓ ω ν'

end ScenarioApproach.EmpiricalCosts


