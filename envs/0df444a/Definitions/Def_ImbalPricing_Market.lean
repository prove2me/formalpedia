-- Prove2me | Definitions.Def_ImbalPricing_Market
-- name    : ImbalPricing_Market
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:35:47.140989+00:00
-- url     : https://prove2.me/theorems/1c66bae3-3d8d-40d7-9622-1a5480687e8b
-- title:
--   The two-stage electricity market with strategic low-cost generators: standing assumptions, offers, commitments and adjustments
-- statement:
--   This module sets up the two-stage market of §3.1 of the paper.
--
--   **Data.** There are $N$ low-cost generators (LCGs), indexed by $i$, and one nonstrategic high-cost generator (HCG). A probability space $(\Omega,\mu)$ carries the demand forecast error $\epsilon$ (the realized demand is $1+\epsilon$, expected demand being normalized to $1$) and the production forecast errors $\nu^i$ (LCG $i$ produces $\gamma^i(1+\nu^i)$, where $\gamma^i$ is its expected production). The HCG's marginal-cost slopes are $\alpha_1$ (Stage 1) and $\alpha_2$ (Stage 2). The LCGs' **market share** is $\gamma=\sum_{i=1}^N\gamma^i$.
--
--   **Standing assumptions** (pp.5–7):
--   1. $N\ge1$ and $\gamma^i>0$ for every $i$;
--   2. $\gamma\le1$;
--   3. $\alpha_2\ge\alpha_1\ge0$;
--   4. $\mu$ is a probability measure;
--   5. $\mathbb E[\epsilon]=0$, $\mathbb E[\nu^i]=0$, and $\epsilon$ and every $\nu^i$ are square integrable.
--
--   No joint condition is imposed: $\epsilon,\nu^1,\dots,\nu^N$ may be arbitrarily correlated.
--
--   **Offers and quantities** (p.7). LCG $i$ chooses an offer quantity adjustment $d^i$ in its strategy set $[-1,\,1/\gamma-1]$. At the offer profile $d=(d^1,\dots,d^N)$:
--
--   $$L_1^i=\gamma^i(1+d^i),\quad L_1=\sum_{i=1}^NL_1^i,\quad H_1=1-L_1,\quad p_1=\alpha_1H_1,$$
--   $$L_2^i=\gamma^i(\nu^i-d^i),\quad L_2=\sum_{i=1}^NL_2^i,\quad H_2=\epsilon-L_2.$$
--
--   Here $L_1^i$ is LCG $i$'s Stage-1 commitment, $H_1$ the HCG's Stage-1 schedule, $p_1=MC_1$ the Stage-1 price (Eq. (7)), $L_2^i$ LCG $i$'s Stage-2 adjustment and $H_2$ the HCG's Stage-2 adjustment. The Stage-1 quantities are deterministic; the Stage-2 quantities are random.
--
--   **Formalization Note** LCGs are indexed by `Fin N`. The paper assumes $\epsilon\ge-1$, $\nu^i\ge-1$ and boundedness, which only keep realized quantities nonnegative; they are replaced by square integrability, which every bounded random variable has. $\gamma^i>0$ is read from the model (Eq. (10) divides by $\gamma^i$).
-- source:
--   Ghiassi-Farrokhfal, Belo, Hesamzadeh, Bunn, Optimal Electricity Imbalance Pricing for the Emerging Penetration of Renewable and Low-Cost Generators, Manufacturing & Service Operations Management, Articles in Advance (2023), doi:10.1287/msom.2021.0555, §3.1.1–3.1.4, pp.5–7 (PDF pp.7–9); Eq. (7), p.8 (PDF p.10)

import Mathlib

open MeasureTheory

namespace ImbalPricing

/-- **The two-stage electricity market**, Ghiassi-Farrokhfal, Belo, Hesamzadeh, Bunn, *Optimal
Electricity Imbalance Pricing …*, MSOM Articles in Advance (2023), §3.1, pp.5–7 (PDF pp.7–9).

* `μ` is the probability law on the sample space `Ω`;
* `γ i` is the expected production `γⁱ` of low-cost generator (LCG) `i`, normalized to the
  expected demand (p.6);
* `α₁`, `α₂` are the slopes of the HCG's marginal costs in Stage 1 and Stage 2 (p.5);
* `ε` is the demand forecast error: the realized demand is `1 + ε` (p.5);
* `ν i` is the production forecast error of LCG `i`: its realized production is
  `γⁱ (1 + νⁱ)` (p.6).

The standing assumptions of §3.1 are collected in `Market.Standing`.

**Formalization Note.** The `N ≥ 1` LCGs are indexed by `Fin N`. -/
structure Market (Ω : Type*) [MeasurableSpace Ω] (N : ℕ) where
  μ : Measure Ω
  γ : Fin N → ℝ
  α₁ : ℝ
  α₂ : ℝ
  ε : Ω → ℝ
  ν : Fin N → Ω → ℝ

variable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}

namespace Market

/-- The market share of the LCGs, `γ = ∑_{i=1}^N γⁱ` (p.6). -/
def share (M : Market Ω N) : ℝ := ∑ i, M.γ i

/-- **Standing assumptions of §3.1**, MSOM Articles in Advance (2023), pp.5–7 (PDF pp.7–9):

1. `N ≥ 1` LCGs (p.5), each with expected production `γⁱ > 0`;
2. market share `γ = ∑ γⁱ ≤ 1` ("We restrict our focus to γ ≤ 1", p.6);
3. `α₂ ≥ α₁ ≥ 0` (p.5);
4. `μ` is a probability measure;
5. `ε` and every `νⁱ` are unbiased, `E[ε] = 0`, `E[νⁱ] = 0` (pp.5–6), and square integrable.

No joint condition is imposed on `ε, ν¹, …, νᴺ`: they may be arbitrarily correlated.

**Formalization Note.** `γⁱ > 0` is read from the model (Eq. (10) divides by `γⁱ`). The paper
assumes `ε ≥ −1`, `νⁱ ≥ −1` and boundedness; these only keep realized quantities nonnegative and
are replaced by square integrability (`MemLp · 2 μ`), which every bounded random variable has. -/
structure Standing (M : Market Ω N) : Prop where
  N_pos : 0 < N
  γ_pos : ∀ i, 0 < M.γ i
  share_le_one : M.share ≤ 1
  α₁_nonneg : 0 ≤ M.α₁
  α₁_le_α₂ : M.α₁ ≤ M.α₂
  isProb : IsProbabilityMeasure M.μ
  ε_memLp : MemLp M.ε 2 M.μ
  ν_memLp : ∀ i, MemLp (M.ν i) 2 M.μ
  ε_mean : ∫ ω, M.ε ω ∂M.μ = 0
  ν_mean : ∀ i, ∫ ω, M.ν i ω ∂M.μ = 0

/-- The strategy set of every LCG: `dⁱ ∈ [−1, (1/γ) − 1]` (§3.1.4, p.7). -/
def offerBox (M : Market Ω N) : Set ℝ := Set.Icc (-1) (1 / M.share - 1)

/-- Stage-1 commitment of LCG `i` at the offer profile `d`: `L₁ⁱ = γⁱ (1 + dⁱ)` (p.7). -/
def L1i (M : Market Ω N) (d : Fin N → ℝ) (i : Fin N) : ℝ := M.γ i * (1 + d i)

/-- Total Stage-1 commitment of the LCGs: `L₁ = ∑_{i=1}^N γⁱ (1 + dⁱ)` (p.7). -/
def L1 (M : Market Ω N) (d : Fin N → ℝ) : ℝ := ∑ i, M.L1i d i

/-- HCG's Stage-1 schedule: `H₁ = 1 − L₁` (p.7). -/
def H1 (M : Market Ω N) (d : Fin N → ℝ) : ℝ := 1 - M.L1 d

/-- Stage-1 price: `p₁ = MC₁ = α₁ H₁` (Eqs. (1), (7), pp.6, 8). -/
def p1 (M : Market Ω N) (d : Fin N → ℝ) : ℝ := M.α₁ * M.H1 d

/-- Stage-2 adjustment of LCG `i`: `L₂ⁱ = γⁱ (νⁱ − dⁱ)` (p.7). -/
def L2i (M : Market Ω N) (d : Fin N → ℝ) (i : Fin N) (ω : Ω) : ℝ :=
  M.γ i * (M.ν i ω - d i)

/-- Total Stage-2 adjustment of the LCGs: `L₂ = ∑_{i=1}^N γⁱ (νⁱ − dⁱ)` (p.7). -/
def L2 (M : Market Ω N) (d : Fin N → ℝ) (ω : Ω) : ℝ := ∑ i, M.L2i d i ω

/-- HCG's Stage-2 adjustment: `H₂ = ε − L₂` (p.7). -/
def H2 (M : Market Ω N) (d : Fin N → ℝ) (ω : Ω) : ℝ := M.ε ω - M.L2 d ω

end Market

end ImbalPricing


