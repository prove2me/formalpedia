-- Prove2me | Definitions.Def_RiskDistMDP_DPP_Assumption26
-- name    : RiskDistMDP_DPP_Assumption26
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:53:21.726357+00:00
-- url     : https://prove2.me/theorems/ec9f2fe7-1d77-497a-acb2-3aa2e9f4c829
-- title:
--   Assumption 2.6 — measurability and bounds of $\sigma_{t,x}$
-- statement:
--   The paper uses a risk measure $\sigma_0$ at time $0$ and a family $(\sigma_{t,x})_{(t,x)\in\mathbb N\times\mathbb X}$, each satisfying Definition 2.3. **Assumption 2.6** requires, for every $t\in\mathbb N$:
--
--   1. for every compact $K\subset\mathbb R$, the map $(x,\mu)\in\mathbb X\times\mathcal P(K)\mapsto\sigma_{t,x}(\mu)\in(-\infty,\infty]$ is $\mathcal B(\mathbb X)\otimes\mathcal B(\mathcal P(K))$-measurable;
--   2. there is $b_t\ge0$ with $|\sigma_{t,x}(\delta_0)|\le b_t$ for all $x\in\mathbb X$.
--
--   The family is **normalized** if $\sigma_{t,x}(\delta_0)=0$ for every $(t,x)$, i.e. $b_t=0$. Neither condition concerns $\sigma_0$.
--
--   The module also defines `IsRiskFamily` (Definition 2.3 for $\sigma_0$ and every $\sigma_{t,x}$), `SigmaMeasurable`, `SigmaBounded` (the two halves, with the constants $b_t$ named) and `FamilyNormalized`.
--
--   **Formalization Note** $\mathcal P(K)$ is the set of probability measures on $\mathbb R$ carried by $K$, with the trace of the Giry (evaluation) σ-algebra; the paper identifies it with the Borel σ-algebra (p.5, Lemma B.5).
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, Assumption 2.6, p. 8; §2.4, pp. 8–9

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_IsDistRiskMeasure

set_option autoImplicit false

open MeasureTheory Set

namespace RiskDistMDP.DPP

/-- The risk measures of arXiv:2203.09612v4, §2.4, p.8: `σ₀` and `(σ_{t,x})_{(t,x) ∈ ℕ × 𝕏}`
each satisfy Definition 2.3 (with the corrected axiom (iii), see `IsDistRiskMeasure`).

**Formalization Note** `σ t x` is `σ_{t,x}`; it is constrained only for `t ≥ 1` (the paper's
`ℕ = {1,2,…}`). `σ₀` has no state argument. -/
def IsRiskFamily {𝕏 : Type*} (σ0 : Measure ℝ → EReal) (σ : ℕ → 𝕏 → Measure ℝ → EReal) : Prop :=
  IsDistRiskMeasure σ0 ∧ ∀ t, 1 ≤ t → ∀ x, IsDistRiskMeasure (σ t x)

/-- First half of Assumption 2.6 (arXiv:2203.09612v4, p.8): for every `t ∈ ℕ` and compact
`K ⊂ ℝ`, `(x, μ) ∈ 𝕏 × 𝒫(K) ↦ σ_{t,x}(μ) ∈ (−∞, ∞]` is `ℬ(𝕏) ⊗ ℬ(𝒫(K))`-measurable.

**Formalization Note** `𝒫(K)` is the set of probability measures on `ℝ` carried by `K`, as a
subtype of `Measure ℝ` with the trace of the Giry (evaluation) σ-algebra; the paper identifies it
with the Borel σ-algebra of the weak topology (§2, p.5, Lemma B.5). Measurability into `EReal` is for
`ℬ(ℝ̄)`. -/
def SigmaMeasurable {𝕏 : Type*} [MeasurableSpace 𝕏] (σ : ℕ → 𝕏 → Measure ℝ → EReal) : Prop :=
  ∀ t, 1 ≤ t → ∀ K : Set ℝ, IsCompact K →
    Measurable (fun p : 𝕏 × {μ : Measure ℝ // IsProbabilityMeasure μ ∧ μ Kᶜ = 0} =>
      σ t p.1 (p.2 : Measure ℝ))

/-- Second half of Assumption 2.6 (arXiv:2203.09612v4, p.8), with the constants named: for each
`t ∈ ℕ`, `b t ≥ 0` and `|σ_{t,x}(δ₀)| ≤ b t` for all `x ∈ 𝕏`. -/
def SigmaBounded {𝕏 : Type*} (σ : ℕ → 𝕏 → Measure ℝ → EReal) (b : ℕ → ℝ) : Prop :=
  ∀ t, 1 ≤ t → 0 ≤ b t ∧ ∀ x, -((b t : ℝ) : EReal) ≤ σ t x (Measure.dirac 0) ∧
    σ t x (Measure.dirac 0) ≤ ((b t : ℝ) : EReal)

/-- **Assumption 2.6** (arXiv:2203.09612v4, p.8): `σ_{t,x}` is jointly measurable on `𝕏 × 𝒫(K)`
for every compact `K` (`SigmaMeasurable`), and for each `t ∈ ℕ` there is `b_t ≥ 0` with
`|σ_{t,x}(δ₀)| ≤ b_t` for all `x` (`SigmaBounded`). -/
def Assumption26 {𝕏 : Type*} [MeasurableSpace 𝕏] (σ : ℕ → 𝕏 → Measure ℝ → EReal) : Prop :=
  SigmaMeasurable σ ∧ ∃ b : ℕ → ℝ, SigmaBounded σ b

/-- `(σ_{t,x})_{(t,x) ∈ ℕ × 𝕏}` is **normalized** (arXiv:2203.09612v4, p.9) if `σ_{t,x}(δ₀) = 0`
for every `(t, x) ∈ ℕ × 𝕏`. It says nothing about `σ₀`. -/
def FamilyNormalized {𝕏 : Type*} (σ : ℕ → 𝕏 → Measure ℝ → EReal) : Prop :=
  ∀ t, 1 ≤ t → ∀ x, Normalized (σ t x)

end RiskDistMDP.DPP


