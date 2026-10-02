-- Prove2me | Definitions.Def_ScenarioApproach_EmpiricalCosts_nondegenerate
-- name    : ScenarioApproach_EmpiricalCosts_nondegenerate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T18:03:55.937812+00:00
-- url     : https://prove2.me/theorems/aaf8638d-3397-4a75-92e9-0d2265d79fd1
-- title:
--   Definition 8.3 — nondegeneracy of the empirical costs
-- statement:
--   Let the decision space be $\mathbb R^{d-1}$ and let $\mathbb P$ be a probability on $\Delta$. The scenario program is **nondegenerate** if for every sample size $N\ge d$, with probability $1$ over the independent sample $(\delta_1,\dots,\delta_N)$ drawn from $\mathbb P$, the empirical costs of its solution from index $d$ onward are all different:
--
--   $$
--   \ell^*_d\ne\ell^*_{d+1}\ne\cdots\ne\ell^*_N .
--   $$
--
--   Only empirical costs from $\ell^*_d$ onward are considered because some of the other costs have the same value by construction (several scenarios attain the maximum at $\nu^*$). Since the empirical costs are sorted, the condition says $\ell^*_d>\ell^*_{d+1}>\cdots>\ell^*_N$.
--
--   **Formalization Note** With $d=n+1$, the condition is required for every sample size $m\ge n+1$ (not only for the $N$ of a theorem), as in the book; for each such $m$ it says that for $\mathbb P^m$-almost every sample and every solution $\nu$ of the program, adjacent empirical costs $\ell^*_k,\ell^*_{k+1}$ with $d\le k<m$ differ.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 90, Definition 8.3 and footnote 22

import Mathlib
import Definitions.Def_ScenarioApproach_EmpiricalCosts_scenarioProgram
import Definitions.Def_ScenarioApproach_EmpiricalCosts_empiricalCost

namespace ScenarioApproach.EmpiricalCosts

/-- Definition 8.3 (nondegeneracy), for the scenario program (1.4) with `ν ∈ ℝ^n`, i.e. `d = n + 1`:
for every sample size `m ≥ d`, with probability 1 (over the i.i.d. sample `(δ₁, …, δ_m)`), the
empirical costs of the solution satisfy `ℓ*_d ≠ ℓ*_{d+1} ≠ ⋯ ≠ ℓ*_m`. -/
def Nondegenerate {n : ℕ} {Δ : Type*} [MeasurableSpace Δ] (P : MeasureTheory.Measure Δ)
    [MeasureTheory.IsProbabilityMeasure P] (ℓ : EuclideanSpace ℝ (Fin n) → Δ → ℝ) : Prop :=
  ∀ m : ℕ, n + 1 ≤ m →
    ∀ᵐ ω ∂(MeasureTheory.Measure.pi fun _ : Fin m => P),
      ∀ ν, IsSolution ℓ ω ν →
        ∀ k : ℕ, n + 1 ≤ k → k < m → empiricalCost ℓ ω ν k ≠ empiricalCost ℓ ω ν (k + 1)

end ScenarioApproach.EmpiricalCosts


