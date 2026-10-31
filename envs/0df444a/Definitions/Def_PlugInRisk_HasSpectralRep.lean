-- Prove2me | Definitions.Def_PlugInRisk_HasSpectralRep
-- name    : PlugInRisk_HasSpectralRep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:26:31.033983+00:00
-- url     : https://prove2.me/theorems/eb89592d-7f77-48af-83a4-3c96e33dab58
-- title:
--   Spectral representation (4.1) of a risk measure
-- statement:
--   A set $\mathcal M$ of probability measures on $[0,1)$ and a penalty $\beta:\mathcal M\to[0,\infty)$ **represent** the risk measure $\rho$ on $L^p$ if for every $X\in L^p$ each $u\mapsto\mathrm{AVaR}_u(X)$ is $\gamma$-integrable, $\gamma\in\mathcal M$, and
--
--   $$
--   \rho(X)=\sup_{\gamma\in\mathcal M}\Bigl(\int_{[0,1)}\mathrm{AVaR}_u(X)\,\gamma(du)-\beta(\gamma)\Bigr).
--   $$
--
--   **Formalization Note** Measures on $[0,1)$ are probability measures on $\mathbb R$ with no mass outside $[0,1)$. The supremum is a least upper bound (`IsLUB`), so the set of values is nonempty. Convexity of $\mathcal M$ and $\beta$ is not part of this predicate.
-- source:
--   Bartl & Tangpi, Non-asymptotic convergence rates for the plug-in estimation of risk measures, arXiv:2003.10479v2, display (4.1), p.17

import Mathlib
import Definitions.Def_PlugInRisk_avar

open MeasureTheory
open scoped ENNReal

namespace PlugInRisk

/-- **Spectral representation** (Bartl & Tangpi, arXiv:2003.10479v2, display (4.1), p.17):
`ρ(X) = sup_{γ∈𝓜} ( ∫_{[0,1)} AVaR_u(X) γ(du) − β(γ) )` for `X ∈ Lᵖ`, where "𝓜 is a subset of
probability measures on [0, 1) armed with its Borel σ-field, β : 𝓜 → [0, ∞)".

`HasSpectralRep p ρ 𝓜 β` says that `(𝓜, β)` represents `ρ` on `Lᵖ` in this way.

**Formalization Note** Probability measures on `[0, 1)` are probability measures on `ℝ` giving
zero mass to the complement of `[0, 1)`. `β` is a function on all measures, of which only its
values on `𝓜` matter. For each `X ∈ Lᵖ` the map `u ↦ AVaR_u(X)` is required to be
`γ`-integrable for every `γ ∈ 𝓜` (the integrals in (4.1) are finite, since each is at most
`ρ(X) + β(γ)` and `AVaR_u(X) ≥ E[X]`), and the supremum is stated with `IsLUB`, which also makes
the set nonempty and avoids the junk value of a real `⨆`. The convexity of `𝓜` and `β` asserted
on p.17 is not part of this predicate. -/
def HasSpectralRep (p : ℝ≥0∞) (ρ : (unitInterval → ℝ) → ℝ) (𝓜 : Set (Measure ℝ))
    (β : Measure ℝ → ℝ) : Prop :=
  (∀ γ ∈ 𝓜, IsProbabilityMeasure γ ∧ γ (Set.Ico 0 1)ᶜ = 0) ∧
  (∀ γ ∈ 𝓜, 0 ≤ β γ) ∧
  ∀ X : unitInterval → ℝ, MemLp X p volume →
    (∀ γ ∈ 𝓜, Integrable (fun u => avar (volume.map X) u) γ) ∧
    IsLUB {y : ℝ | ∃ γ ∈ 𝓜, y = ∫ u, avar (volume.map X) u ∂γ - β γ} (ρ X)

end PlugInRisk


