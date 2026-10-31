-- Prove2me | Definitions.Def_PlugInRisk_SatisfiesA3
-- name    : PlugInRisk_SatisfiesA3
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:41.767156+00:00
-- url     : https://prove2.me/theorems/0e21d301-8e48-4f82-83f3-700774c5ebb5
-- title:
--   Assumption A.3 (pointwise and $L^2$ separability)
-- statement:
--   A class $\mathcal F$ of functions $\mathcal X\to\mathbb R$ satisfies **Assumption A.3** for the law $\mu$ if there is a countable subset $\mathcal F'\subset\mathcal F$ such that every $f\in\mathcal F$ is the limit of a sequence $(f_n)$ in $\mathcal F'$ both pointwise and in $L^2(\mu)$.
--
--   It guarantees that suprema of empirical processes over $\mathcal F$ equal suprema over the countable $\mathcal F'$, hence are measurable.
--
--   **Formalization Note** The standing requirement that $\mathcal F$ consist of measurable, $\mu$-square integrable functions is stated separately wherever the predicate is used.
-- source:
--   Bartl & Tangpi, Non-asymptotic convergence rates for the plug-in estimation of risk measures, arXiv:2003.10479v2, Assumption A.3, p.34

import Mathlib

open MeasureTheory Filter Topology

namespace PlugInRisk

/-- **Assumption A.3** (Bartl & Tangpi, arXiv:2003.10479v2, App. A.2, p.34): "There is a countable
set ℱ′ ⊂ ℱ such that, for every f ∈ ℱ there is a sequence (f_n)_n in ℱ′ such that f_n → f
pointwise and in L²(μ)."

**Formalization Note** The standing requirement of p.34 that `ℱ` be "a set of measurable,
μ-square integrable functions from 𝒳 to ℝ" is not part of this predicate; every statement using
it states it as a separate hypothesis (or conclusion). Convergence in `L²(μ)` is
`eLpNorm (f_n − f) 2 μ → 0`. -/
def SatisfiesA3 {𝒳 : Type*} [MeasurableSpace 𝒳] (μ : Measure 𝒳) (ℱ : Set (𝒳 → ℝ)) : Prop :=
  ∃ ℱ' ⊆ ℱ, ℱ'.Countable ∧ ∀ f ∈ ℱ, ∃ u : ℕ → 𝒳 → ℝ, (∀ n, u n ∈ ℱ') ∧
    (∀ x, Tendsto (fun n => u n x) atTop (𝓝 (f x))) ∧
    Tendsto (fun n => eLpNorm (u n - f) 2 μ) atTop (𝓝 0)

end PlugInRisk


