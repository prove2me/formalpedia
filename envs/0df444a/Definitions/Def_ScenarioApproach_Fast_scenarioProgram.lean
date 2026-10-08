-- Prove2me | Definitions.Def_ScenarioApproach_Fast_scenarioProgram
-- name    : ScenarioApproach_Fast_scenarioProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T04:24:41.803794+00:00
-- url     : https://prove2.me/theorems/8e383ef3-81a1-47a6-ade7-e480de206a32
-- title:
--   Eq. (1.4) — the min-max scenario program and its solution
-- statement:
--   Let $\ell(\nu,\delta)$ be a real-valued loss depending on a decision $\nu\in\mathbb R^{d-1}$ and on an uncertain parameter $\delta\in\Delta$. Given $m\ge 1$ scenarios $\delta_1,\dots,\delta_m\in\Delta$, the **worst-case cost** of a decision $\nu$ on the scenarios is
--
--   $$
--   \max_{i=1,\dots,m}\ \ell(\nu,\delta_i),
--   $$
--
--   and the **scenario program with $m$ scenarios** is
--
--   $$
--   \min_{\nu\in\mathbb R^{d-1}}\ \Big[\max_{i=1,\dots,m}\ \ell(\nu,\delta_i)\Big].
--   $$
--
--   A decision $\nu$ is a **solution** of the program when its worst-case cost is no larger than that of any other decision $\nu'$. The solution is denoted $\nu^*$ and the optimal value $\ell^*=\max_{i}\ell(\nu^*,\delta_i)$.
--
--   This is the basic data-driven min-max design of the book; every result of this mission is a statement about the solution of this program, with $m=N$ or $m=N_1$ scenarios.
--
--   **Formalization Note** The decision space $\mathbb R^{d-1}$ is `EuclideanSpace ℝ (Fin n)`, so the book's $d$ is $n+1$ (the decision plus the epigraph variable $\ell$). A sample of $m$ scenarios is `ω : Fin m → Δ`; the maximum is `Finset.sup'` over the nonempty index set, which requires `NeZero m`: the program with no scenario is not defined. `IsSolution` does not assert uniqueness; existence and uniqueness (Assumption 3.6) are hypotheses of the theorems.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 7, Eq. (1.4)

import Mathlib

namespace ScenarioApproach.Fast

/-- The worst-case cost `max_{i=1,…,m} ℓ(ν, δᵢ)` of the decision `ν` on the sample
`ω = (δ₁, …, δ_m)`, the objective of the scenario program (1.4). The sample must be
nonempty (`NeZero m`), so the maximum is taken over a nonempty finite set. -/
noncomputable def scenarioCost {n m : ℕ} [NeZero m] {Δ : Type*}
    (ℓ : EuclideanSpace ℝ (Fin n) → Δ → ℝ) (ω : Fin m → Δ)
    (ν : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => ℓ ν (ω i))

/-- `ν` is a solution of the scenario program (1.4)
`min_{ν ∈ ℝ^{d-1}} max_{i=1,…,m} ℓ(ν, δᵢ)` with the `m` scenarios `ω`: no decision has a
smaller worst-case cost on the sample. Its optimal value is `scenarioCost ℓ ω ν`. -/
def IsSolution {n m : ℕ} [NeZero m] {Δ : Type*}
    (ℓ : EuclideanSpace ℝ (Fin n) → Δ → ℝ) (ω : Fin m → Δ)
    (ν : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ ν' : EuclideanSpace ℝ (Fin n), scenarioCost ℓ ω ν ≤ scenarioCost ℓ ω ν'

end ScenarioApproach.Fast


