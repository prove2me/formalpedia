-- Prove2me | Definitions.Def_LiqPremiaEq_IsFrictionalEquilibrium
-- name    : LiqPremiaEq_IsFrictionalEquilibrium
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:03:50.910248+00:00
-- url     : https://prove2.me/theorems/2aa5d3e3-1a8d-4502-976e-5edc8619f149
-- title:
--   Radner equilibrium with transaction costs
-- statement:
--   A process $S$ is a **price process** (2.2) if $dS_t=\mu_t\,dt+\sigma_t\,dW_t$ on $[0,T]$, $S_T=\mathfrak S$, with $\mu\in\mathbb H^4(\mathbb R^K)$ and $\sigma\in\mathbb H^4(\mathbb R^{K\times D})$.
--
--   A price process $S$ with trading rates $\dot\varphi^1,\dots,\dot\varphi^N$ is a **Radner equilibrium with transaction costs** if
--
--   1. (individual optimality) each $\dot\varphi^n$ is optimal for agent $n$'s frictional problem (4.1), and
--   2. (market clearing) $\sum_{n=1}^N\varphi^n_t=s$ for all $t\in[0,T]$, where $\varphi^n_t=\varphi^n_{0-}+\int_0^t\dot\varphi^n_u\,du$ and $s\in\mathbb R^K$ is the supply.
--
--   This is Definition 3.1 with the frictional problem (4.1) in place of the frictionless one (3.1), as used in Lemma 4.2 and Theorem 4.5.
--
--   **Formalization Note** Agents are `Fin (M + 1)`. Market clearing holds almost surely, simultaneously for all $t\le T$; the terminal condition holds almost surely.
-- source:
--   Muhle-Karbe–Shi–Yang, An Equilibrium Model for the Cross-Section of Liquidity Premia, arXiv:2011.13625v1, eq. (2.2), p.4; Definition 3.1, p.4; eq. (4.1), p.5; Lemma 4.2, p.7

import Mathlib
import Definitions.Def_LiqPremiaEq_IsHp
import Definitions.Def_LiqPremiaEq_HasItoDynamics
import Definitions.Def_LiqPremiaEq_IsOptimalRate

open MeasureTheory
open scoped NNReal

namespace LiqPremiaEq

/-- `S` is a **price process** (2.2) with expected returns `μ ∈ H⁴(ℝᴷ)` and volatility
`σ ∈ H⁴(ℝ^{K×D})`: `dS_t = μ_t dt + σ_t dW_t` on `[0, T]` and `S_T = 𝔖` almost surely.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, eq. (2.2) and the sentence after it, p.4. -/
def IsPriceProcess {Ω : Type*} [mΩ : MeasurableSpace Ω] {K D : ℕ}
    (𝓕 : MeasureTheory.Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (W : ℝ≥0 → Ω → Fin D → ℝ) (𝔖 : Ω → Fin K → ℝ) (S μ : ℝ≥0 → Ω → Fin K → ℝ)
    (σ : ℝ≥0 → Ω → Matrix (Fin K) (Fin D) ℝ) : Prop :=
  HasItoDynamics 𝓕 P T W S μ σ ∧ (∀ᵐ ω ∂P, S T ω = 𝔖 ω) ∧
    IsHp 𝓕 P T 4 μ ∧ IsHpMat 𝓕 P T 4 σ

/-- A **Radner equilibrium with transaction costs**: `S` is a price process (2.2) with drift `μ`
and volatility `σ`, and the trading rates `φ̇¹, …, φ̇ᴺ`
1. are optimal for the frictional problems (4.1) of the agents `n = 1, …, N` (individual
   optimality), and
2. clear the market: `∑ₙ φⁿ_t = s` for all `t ∈ [0, T]`, where `φⁿ_t = φⁿ_{0−} + ∫₀ᵗ φ̇ⁿ_u du`.

Agent `n` has risk aversion `γⁿ`, initial position `φⁿ_{0−}` and endowment volatility `ξⁿ`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Definition 3.1, p.4, with the frictional problem (4.1)
(p.5) in place of (3.1), as in Lemma 4.2 (p.7) and Theorem 4.5 (p.8).

**Formalization Note** Agents are `Fin (M + 1)` (`N = M + 1`). Market clearing is required
almost surely, simultaneously for all `t ∈ [0, T]`. -/
def IsFrictionalEquilibrium {Ω : Type*} [mΩ : MeasurableSpace Ω] {M K D : ℕ}
    (𝓕 : MeasureTheory.Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (W : ℝ≥0 → Ω → Fin D → ℝ) (γ : Fin (M + 1) → ℝ) (Λ : Matrix (Fin K) (Fin K) ℝ)
    (s : Fin K → ℝ) (φ0m : Fin (M + 1) → Fin K → ℝ) (ξp : Fin (M + 1) → ℝ≥0 → Ω → Fin D → ℝ)
    (𝔖 : Ω → Fin K → ℝ) (S μ : ℝ≥0 → Ω → Fin K → ℝ) (σ : ℝ≥0 → Ω → Matrix (Fin K) (Fin D) ℝ)
    (rates : Fin (M + 1) → ℝ≥0 → Ω → Fin K → ℝ) : Prop :=
  IsPriceProcess 𝓕 P T W 𝔖 S μ σ ∧
    (∀ n, IsOptimalRate 𝓕 P T (γ n) Λ (φ0m n) (ξp n) μ σ (rates n)) ∧
    (∀ᵐ ω ∂P, ∀ t ≤ T, ∑ n, position (φ0m n) (rates n) t ω = s)

end LiqPremiaEq


