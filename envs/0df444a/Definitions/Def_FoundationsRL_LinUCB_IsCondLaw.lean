-- Prove2me | Definitions.Def_FoundationsRL_LinUCB_IsCondLaw
-- name    : FoundationsRL_LinUCB_IsCondLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:19:16.651984+00:00
-- url     : https://prove2.me/theorems/b0696be4-15c3-4d07-9c83-853da837f3a2
-- title:
--   Regular conditional law of a random variable given a σ-algebra
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $\mathcal H$ a σ-algebra on $\Omega$, $Y$ a random variable with values in a measurable space $E$, and $\kappa$ a family of measures on $E$ indexed by $\Omega$. We say that $\kappa$ is a **regular conditional law** of $Y$ given $\mathcal H$ if every $\kappa_\omega$ is a probability measure, $\omega\mapsto\kappa_\omega(B)$ is $\mathcal H$-measurable for every measurable $B\subseteq E$, and
--
--   $$
--   P\bigl(A\cap\{Y\in B\}\bigr)=\int_A \kappa_\omega(B)\,P(d\omega)
--   $$
--
--   for all $A\in\mathcal H$ and all measurable $B$.
--
--   This is the precise meaning of the phrase "$Y\sim\kappa$ conditionally on $\mathcal H$", which the contextual bandit protocol uses for both the action and the reward.
--
--   **Formalization Note** The notion is stated by its defining identity, without conditional expectations, so it needs no integrability assumption.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §3, pp. 38–39 (conditional laws in the protocol and in Assumption 2)

import Mathlib

open MeasureTheory

namespace FoundationsRL.LinUCB

/-- `κ` is a regular conditional law of the random variable `Y` given the σ-algebra `𝓗`: each
`κ ω` is a probability measure, `ω ↦ κ ω B` is `𝓗`-measurable, and
`P(A ∩ {Y ∈ B}) = ∫_A κ ω B dP` for every `𝓗`-measurable `A` and measurable `B`. This is the
meaning of "`Y ∼ κ` conditionally on `𝓗`" used in the protocol of Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §3, pp. 38–39.

**Formalization Note.** Stated by the defining equation, without `condExp`, so it needs no
integrability assumption and applies to any measurable codomain `E`. -/
structure IsCondLaw {Ω E : Type*} [MeasurableSpace E] (𝓗 : MeasurableSpace Ω)
    {mΩ : MeasurableSpace Ω} (P : Measure Ω) (Y : Ω → E) (κ : Ω → Measure E) : Prop where
  /-- Each conditional law is a probability measure. -/
  isProb : ∀ ω, IsProbabilityMeasure (κ ω)
  /-- `ω ↦ κ ω B` is `𝓗`-measurable. -/
  measurable_apply : ∀ B, MeasurableSet B → Measurable[𝓗] fun ω => κ ω B
  /-- The disintegration identity. -/
  setLIntegral : ∀ B, MeasurableSet B → ∀ A, MeasurableSet[𝓗] A →
    P (A ∩ Y ⁻¹' B) = ∫⁻ ω in A, κ ω B ∂P

end FoundationsRL.LinUCB


