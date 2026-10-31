-- Prove2me | Definitions.Def_PlugInRisk_hedgedRisk
-- name    : PlugInRisk_hedgedRisk
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:26:19.193012+00:00
-- url     : https://prove2.me/theorems/355d96ee-ce71-4165-885e-8c2de41337d1
-- title:
--   Minimal risk with hedging $\pi^\nu(F)$
-- statement:
--   Let $\mathcal X$ be a measurable space, $F:\mathcal X\to\mathbb R$ a position, $G_1,\dots,G_e:\mathcal X\to\mathbb R$ options traded at price zero and $\mathcal G\subset\mathbb R^e$ a set of admissible strategies. For a law $\nu$ on $\mathcal X$,
--
--   $$
--   \pi^\nu(F):=\inf_{g\in\mathcal G}\rho^\nu\Bigl(F+\sum_{i=1}^e g_iG_i\Bigr),
--   $$
--
--   the minimal risk the agent can reach by trading. With $\mathcal G=\{0\}$ it is $\rho^\nu(F)$.
--
--   **Formalization Note** The infimum is a real infimum over $\mathcal G$; for empty $\mathcal G$ Lean returns $0$, so statements using it assume $\mathcal G$ nonempty.
-- source:
--   Bartl & Tangpi, Non-asymptotic convergence rates for the plug-in estimation of risk measures, arXiv:2003.10479v2, §2, p.6

import Mathlib
import Definitions.Def_PlugInRisk_lawRisk

open MeasureTheory

namespace PlugInRisk

/-- **Minimal risk with hedging** `π^ν(F)` (Bartl & Tangpi, arXiv:2003.10479v2, §2, p.6):
`π^μ(F) := inf_{g∈𝒢} ρ^μ(F + Σ_{i=1}^e g_i G_i)`, where `G₁, …, G_e : 𝒳 → ℝ` are options
traded at price zero and `𝒢 ⊂ ℝᵉ` is the set of admissible trading strategies.

**Formalization Note** Strategies are vectors `g : Fin e → ℝ`, options a family
`G : Fin e → 𝒳 → ℝ`, and `g · G = ∑ i, g i * G i`. The infimum is the real `⨅` over the subtype
`𝒢`; for empty `𝒢` Lean returns `0` (the paper's value would be `+∞`), so every statement using
`hedgedRisk` assumes `𝒢` nonempty, and for bounded `F`, `G`, `𝒢` the family is bounded below. -/
noncomputable def hedgedRisk {𝒳 : Type*} [MeasurableSpace 𝒳] {e : ℕ}
    (ρ : (unitInterval → ℝ) → ℝ) (ν : Measure 𝒳) (F : 𝒳 → ℝ) (G : Fin e → 𝒳 → ℝ)
    (𝒢 : Set (Fin e → ℝ)) : ℝ :=
  ⨅ g : 𝒢, lawRisk ρ (ν.map (fun x => F x + ∑ i, (g : Fin e → ℝ) i * G i x))

end PlugInRisk


