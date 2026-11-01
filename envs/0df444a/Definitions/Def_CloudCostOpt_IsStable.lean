-- Prove2me | Definitions.Def_CloudCostOpt_IsStable
-- name    : CloudCostOpt_IsStable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:07:19.311982+00:00
-- url     : https://prove2.me/theorems/fcc88505-9b12-40f1-b3cd-228270399d63
-- title:
--   Stable policies $\Pi$
-- statement:
--   A policy $\pi$ is **stable**, $\pi\in\Pi$, if the limits
--
--   $$
--   \bar m_j^{\pi}=\lim_{T\to\infty}\frac1T\sum_{t=1}^{T}\mathbb E[m^{\pi}_{j,t}]\quad\text{and}\quad\bar x_i^{\pi}(s,l)=\lim_{T\to\infty}\frac1T\sum_{t=1}^{T}\mathbb E[x^{\pi}_{i,t}(s,l)]
--   $$
--
--   exist (as finite numbers) for every $j$ and every $(i,s,l)$.
--
--   **Formalization Note** Expectations are lower Lebesgue integrals in $[0,\infty]$; "exists" is convergence to a finite limit.
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §1, p.5 (Stable Policies)

import Mathlib
import Definitions.Def_CloudCostOpt_stateAt
import Definitions.Def_CloudCostOpt_sampleMeasure

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **Stable policies `Π`** (p.5): the Cesàro averages of `E[m_{j,t}]` converge (to a finite
limit `m̄_j`) for every `j`, and those of `E[x_{i,t}(s, l)]` converge (to a finite `x̄ᵢ(s, l)`) for
every `(i, s, l)`.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §1, p.5 ("Stable Policies").

Formalization Note: the expectations are lower Lebesgue integrals in `ℝ≥0∞`; "exists" is
convergence to a finite limit `c : ℝ≥0`. -/
def IsStable (S : System) (lam : Fin S.I → ℝ≥0) (π : Policy S) : Prop :=
  (∀ j : Fin S.J, ∃ c : ℝ≥0, Tendsto (fun T : ℕ =>
      (∑ n ∈ Finset.range T, ∫⁻ ω, (π.m n (history S π ω n) j : ℝ≥0∞) ∂(sampleMeasure S lam)) /
        (T : ℝ≥0∞)) atTop (𝓝 (c : ℝ≥0∞))) ∧
  (∀ (i : Fin S.I) (s l : ℕ), ∃ c : ℝ≥0, Tendsto (fun T : ℕ =>
      (∑ n ∈ Finset.range T, ∫⁻ ω, (stateAt S π ω n i s l : ℝ≥0∞) ∂(sampleMeasure S lam)) /
        (T : ℝ≥0∞)) atTop (𝓝 (c : ℝ≥0∞)))

end CloudCostOpt


