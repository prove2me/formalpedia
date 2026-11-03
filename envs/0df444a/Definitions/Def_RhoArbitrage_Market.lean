-- Prove2me | Definitions.Def_RhoArbitrage_Market
-- name    : RhoArbitrage_Market
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:24:52.041196+00:00
-- url     : https://prove2.me/theorems/4acc48c0-037c-46a5-945b-063b9ac37023
-- title:
--   The one-period market, returns $X_\pi$, $\mathcal X$, $\Pi_\nu$ and the standing assumptions
-- statement:
--   A **one-period market** $(S^0,S)$ has a riskless asset with $S^0_0=1$ and $S^0_1=1+r$, and risky assets $S^1,\dots,S^d$ with prices $S^i_0$ at time $0$ and $S^i_1$ at time $1$. The **return** of asset $i$ and its expectation are
--
--   $$
--   R^i:=\frac{S^i_1-S^i_0}{S^i_0},\qquad \mu^i:=\mathbb E[R^i].
--   $$
--
--   A portfolio is a vector $\pi\in\mathbb R^d$ of fractions of wealth. Its **excess return** over $r$, the space of excess returns and the set of portfolios with expected excess return $\nu$ are
--
--   $$
--   X_\pi:=\pi\cdot(R-r\mathbf 1),\qquad \mathcal X:=\{X_\pi:\pi\in\mathbb R^d\},\qquad \Pi_\nu:=\{\pi\in\mathbb R^d:\mathbb E[X_\pi]=\nu\}.
--   $$
--
--   The **standing assumptions** are:
--
--   1. $r>-1$;
--   2. $S^1_0,\dots,S^d_0>0$;
--   3. $S^1_1,\dots,S^d_1\in L$;
--   4. the market is **nonredundant**: $\sum_{i=0}^d\vartheta^iS^i=0$ $\mathbb P$-a.s. implies $\vartheta^i=0$ for all $i$;
--   5. the risky returns are **nondegenerate**: $\mu^i\ne r$ for at least one $i\in\{1,\dots,d\}$.
--
--   These objects are the setting of every result of the mission.
--
--   **Formalization Note** The riskless asset is determined by $r$ and is not a field. Nonredundancy is read for the price process, so the combination must vanish at time $0$ and $\mathbb P$-a.s. at time $1$; under $S^i_0>0$ this is equivalent to "$X_\pi=0$ $\mathbb P$-a.s. implies $\pi=0$".
-- source:
--   Herdegen, Khan, ρ-arbitrage and ρ-consistent pricing for star-shaped risk measures, arXiv:2202.07610v3, §2.2, pp.5–6, displays (2.2), (2.3)

import Mathlib

open MeasureTheory

namespace RhoArbitrage

/-- **The one-period market `(S⁰, S)`.** Herdegen–Khan, arXiv:2202.07610v3, §2.2, p.5: a one-period
`(1+d)`-dimensional market with riskless asset `S⁰_0 = 1`, `S⁰_1 = 1 + r` and risky assets
`S¹, …, S^d`.

**Formalization Note.** The riskless asset is determined by `r` and is not a field. `S0 i` is the
time-`0` price `S^{i+1}_0` of a risky asset and `S1 i` its time-`1` price `S^{i+1}_1`; risky assets
are indexed by `Fin d`, not `{1, …, d}`. The standing assumptions of §2.2 are `Market.Standing`. -/
structure Market (Ω : Type*) where
  /-- The number of risky assets. -/
  d : ℕ
  /-- The riskless rate. -/
  r : ℝ
  /-- Prices of the risky assets at time `0`. -/
  S0 : Fin d → ℝ
  /-- Prices of the risky assets at time `1`. -/
  S1 : Fin d → Ω → ℝ

namespace Market

variable {Ω : Type*}

/-- The relative return `Rⁱ := (Sⁱ_1 - Sⁱ_0) / Sⁱ_0` of a risky asset. Herdegen–Khan,
arXiv:2202.07610v3, §2.2, p.5. -/
noncomputable def R (M : Market Ω) (i : Fin M.d) (ω : Ω) : ℝ :=
  (M.S1 i ω - M.S0 i) / M.S0 i

/-- The expected return `μⁱ := E[Rⁱ]` of a risky asset. Herdegen–Khan, arXiv:2202.07610v3, §2.2,
p.5. -/
noncomputable def mu [MeasurableSpace Ω] (P : Measure Ω) (M : Market Ω) (i : Fin M.d) : ℝ :=
  ∫ ω, M.R i ω ∂P

/-- The excess return `X_π := π · (R - r𝟏)` of a portfolio `π ∈ ℝ^d`. Herdegen–Khan,
arXiv:2202.07610v3, §2.2, p.6, display (2.2). -/
noncomputable def X (M : Market Ω) (π : Fin M.d → ℝ) (ω : Ω) : ℝ :=
  ∑ i, π i * (M.R i ω - M.r)

/-- The space of excess returns `𝒳 := {X_π : π ∈ ℝ^d}`. Herdegen–Khan, arXiv:2202.07610v3, §2.2,
p.6. -/
def excessSpace (M : Market Ω) : Set (Ω → ℝ) := Set.range M.X

/-- The set `Π_ν := {π ∈ ℝ^d : E[X_π] = ν}` of portfolios with expected excess return `ν`.
Herdegen–Khan, arXiv:2202.07610v3, §2.2, p.6, display (2.3). -/
def Pi [MeasurableSpace Ω] (P : Measure Ω) (M : Market Ω) (ν : ℝ) : Set (Fin M.d → ℝ) :=
  {π | ∫ ω, M.X π ω ∂P = ν}

/-- **Standing assumptions on the market.** Herdegen–Khan, arXiv:2202.07610v3, §2.2, p.5:
`r > -1`; `S¹_0, …, S^d_0 > 0`; `S¹_1, …, S^d_1 ∈ L`; the market is *nonredundant*
(`∑_{i=0}^d ϑⁱ Sⁱ = 0` `P`-a.s. implies `ϑⁱ = 0` for all `i`); and the risky returns are
*nondegenerate* (`μⁱ ≠ r` for at least one `i`).

**Formalization Note.** Nonredundancy is read for the price process: the combination `∑ ϑⁱSⁱ`
vanishes at time `0` and `P`-a.s. at time `1`. This is the weaker assumption of the two possible
readings (the reading at time `1` alone implies it). Under `S0 i > 0` it is equivalent to
"`X_π = 0` `P`-a.s. implies `π = 0`". -/
structure Standing [MeasurableSpace Ω] (P : Measure Ω) (L : Set (Ω → ℝ)) (M : Market Ω) :
    Prop where
  /-- `r > -1`. -/
  r_gt : -1 < M.r
  /-- `Sⁱ_0 > 0`. -/
  S0_pos : ∀ i, 0 < M.S0 i
  /-- `Sⁱ_1 ∈ L`. -/
  S1_mem : ∀ i, M.S1 i ∈ L
  /-- The market is nonredundant. -/
  nonredundant : ∀ (ϑ₀ : ℝ) (ϑ : Fin M.d → ℝ), ϑ₀ + ∑ i, ϑ i * M.S0 i = 0 →
    (∀ᵐ ω ∂P, ϑ₀ * (1 + M.r) + ∑ i, ϑ i * M.S1 i ω = 0) → ϑ₀ = 0 ∧ ϑ = 0
  /-- The risky returns are nondegenerate. -/
  nondegenerate : ∃ i, M.mu P i ≠ M.r

end Market

end RhoArbitrage


