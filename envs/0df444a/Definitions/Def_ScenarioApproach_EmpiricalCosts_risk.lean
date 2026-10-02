-- Prove2me | Definitions.Def_ScenarioApproach_EmpiricalCosts_risk
-- name    : ScenarioApproach_EmpiricalCosts_risk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T17:59:52.734348+00:00
-- url     : https://prove2.me/theorems/18f099bb-a01e-4ab9-a2e0-3420ca075097
-- title:
--   Definition 8.2 — risk of a cost level and of the k-th empirical cost
-- statement:
--   Let $\mathbb P$ be a probability on $\Delta$. For a decision $\nu\in\mathbb R^{d-1}$ and a level $\ell\in\mathbb R$, the **risk** associated with $(\nu,\ell)$ is the probability that a new scenario incurs a cost above $\ell$:
--
--   $$
--   R(\nu,\ell)=\mathbb P\{\delta\in\Delta:\ \ell(\nu,\delta)>\ell\}.
--   $$
--
--   The risk of the $k$-th empirical cost is $R_k=R(\nu^*,\ell^*_k)$.
--
--   Since the empirical costs decrease in $k$, the risks increase: $R_1\le R_2\le\cdots\le R_N$. The risk $R_1=R(\nu^*,\ell^*)$ is the violation probability of the epigraph solution $(\nu^*,\ell^*)$.
--
--   **Formalization Note** The risk is the real number `(P {δ | c < ℓ ν δ}).toReal`, in $[0,1]$ for a probability measure. `empiricalRisk P ℓ ω ν k` is $R(\nu,\ell^*_k)$ for the empirical costs of $\nu$ on the sample `ω`; the theorems apply it at $\nu=\nu^*$.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 90, Definition 8.2

import Mathlib
import Definitions.Def_ScenarioApproach_EmpiricalCosts_empiricalCost

namespace ScenarioApproach.EmpiricalCosts

/-- Definition 8.2 (risk). For `ν ∈ ℝ^{d-1}` and a level `c ∈ ℝ`, the risk associated with
`(ν, c)` is `R(ν, c) = ℙ{δ ∈ Δ : ℓ(ν, δ) > c}`, as a real number in `[0, 1]`. -/
noncomputable def risk {n : ℕ} {Δ : Type*} [MeasurableSpace Δ] (P : MeasureTheory.Measure Δ)
    (ℓ : EuclideanSpace ℝ (Fin n) → Δ → ℝ) (ν : EuclideanSpace ℝ (Fin n)) (c : ℝ) : ℝ :=
  (P {δ | c < ℓ ν δ}).toReal

/-- Definition 8.2 (risk of the `k`-th empirical cost): `R_k = R(ν, ℓ*_k)`, where `ℓ*_k` is the
`k`-th largest of the costs `ℓ(ν, δᵢ)` on the sample `ω`. The book takes `ν = ν*`. -/
noncomputable def empiricalRisk {n m : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : MeasureTheory.Measure Δ) (ℓ : EuclideanSpace ℝ (Fin n) → Δ → ℝ) (ω : Fin m → Δ)
    (ν : EuclideanSpace ℝ (Fin n)) (k : ℕ) : ℝ :=
  risk P ℓ ν (empiricalCost ℓ ω ν k)

end ScenarioApproach.EmpiricalCosts


