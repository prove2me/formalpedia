-- Prove2me | Definitions.Def_RobustSAA_Discrete_Supplement_DiscreteDual
-- name    : RobustSAA_Discrete_Supplement_DiscreteDual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T19:38:54.43086+00:00
-- url     : https://prove2.me/theorems/0a5f8d4f-f347-4fd6-9b4e-edc3d0719275
-- title:
--   §3.1, Theorem 8 — worst-case expectation on a known finite support and the $\chi^2$ / G-test conic programs
-- statement:
--   Let the support be $\Xi=\{\hat\xi^1,\dots,\hat\xi^n\}$, labelled by $j=1,\dots,n$, and let $c_j=c(x;\hat\xi^j)$ be the cost values at a fixed decision $x$. With $p_0(j)=F_0(\{\hat\xi^j\})$ and the empirical frequencies $\hat p_N(j)$ of the published `RobustSAA.Discrete.Setting`:
--
--   1. The worst-case expectation over a set $\mathcal G$ of laws, $C(x;\mathcal G)=\sup_{F_0\in\mathcal G}\sum_j p_0(j)c_j$ (in the extended reals).
--   2. The objective values $r+q^2s-\sum_j\hat p_N(j)t_j$ of the second-order-cone program of Theorem 8 for Pearson's $\chi^2$ test, over $r\in\mathbb R$, $s\ge0$, $t\in\mathbb R^n$, $y\in\mathbb R^n_+$, $c\in\mathbb R^n$ with $s+r\ge c_j$, $2s+t_j\le y_j$, $(2s-c_j+r,\,r-c_j,\,y_j)\in C^3_{SOC}$ and $c_j\ge c(x;\hat\xi^j)$.
--   3. The objective values $r+\tfrac12q^2s-\sum_j\hat p_N(j)t_j$ of the exponential-cone program (27) for the G-test, over $r\in\mathbb R$, $s\ge0$, $t,c\in\mathbb R^n$ with $(t_j,s,s+r-c_j)\in C_{XC}$ and $c_j\ge c(x;\hat\xi^j)$.
--
--   Here $q=Q_{X_N}(\alpha)$, respectively $q=Q_{G_N}(\alpha)$, is the threshold of the test.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, §3.1 p. 8; Theorem 8 and (27), p. 16

import Mathlib
import Definitions.Def_RobustSAA_Discrete_Setting
import Definitions.Def_RobustSAA_Discrete_Supplement_Cones

namespace RobustSAA.Discrete.Supplement

open MeasureTheory RobustSAA.Discrete
open scoped BigOperators

/-- Worst-case expectation (4) over a set `𝒢` of distributions on the known finite support
`Ξ = {ξ̂¹, …, ξ̂ⁿ}` (labels `Fin n`), for the cost values `cⱼ = c(x; ξ̂ʲ)`:
`C(x; 𝒢) = sup_{F₀ ∈ 𝒢} Σⱼ p₀(j) cⱼ` (in `EReal`; `−∞` for the empty set). -/
noncomputable def discWorstCase {n : ℕ} (𝒢 : Set (ProbabilityMeasure (Fin n)))
    (cost : Fin n → ℝ) : EReal :=
  ⨆ F₀ ∈ 𝒢, ((∑ j, pvec F₀ j * cost j : ℝ) : EReal)

/-- Objective values of the second-order-cone program of Theorem 8 for Pearson's `χ²` test
(p. 16), with threshold `q = Q_{X_N}(α)` and cost values `cost j = c(x; ξ̂ʲ)`:
`r + q² s − Σⱼ p̂_N(j) tⱼ` over `r ∈ ℝ, s ∈ ℝ₊, t ∈ ℝⁿ, y ∈ ℝⁿ₊, c ∈ ℝⁿ` with
`s + r ≥ cⱼ`, `2s + tⱼ ≤ yⱼ`, `(2s − cⱼ + r, r − cⱼ, yⱼ) ∈ C³_SOC`, `cⱼ ≥ c(x; ξ̂ʲ)`. -/
def chiDualValues {n N : ℕ} (q : ℝ) (smp : Fin N → Fin n) (cost : Fin n → ℝ) : Set ℝ :=
  {v | ∃ (r s : ℝ) (t y c : Fin n → ℝ), 0 ≤ s ∧ (∀ j, 0 ≤ y j) ∧
    (∀ j, c j ≤ s + r) ∧ (∀ j, 2 * s + t j ≤ y j) ∧
    (∀ j, (2 * s - c j + r, r - c j, y j) ∈ soc3) ∧ (∀ j, cost j ≤ c j) ∧
    v = r + q ^ 2 * s - ∑ j, phat smp j * t j}

/-- Objective values of the exponential-cone program (27) of Theorem 8 for the G-test (p. 16),
with threshold `q = Q_{G_N}(α)`: `r + ½ q² s − Σⱼ p̂_N(j) tⱼ` over `r ∈ ℝ, s ∈ ℝ₊, t ∈ ℝⁿ,
c ∈ ℝⁿ` with `(tⱼ, s, s + r − cⱼ) ∈ C_XC` and `cⱼ ≥ c(x; ξ̂ʲ)`. -/
def gDualValues {n N : ℕ} (q : ℝ) (smp : Fin N → Fin n) (cost : Fin n → ℝ) : Set ℝ :=
  {v | ∃ (r s : ℝ) (t c : Fin n → ℝ), 0 ≤ s ∧
    (∀ j, (t j, s, s + r - c j) ∈ expCone) ∧ (∀ j, cost j ≤ c j) ∧
    v = r + (1 / 2) * q ^ 2 * s - ∑ j, phat smp j * t j}

end RobustSAA.Discrete.Supplement


