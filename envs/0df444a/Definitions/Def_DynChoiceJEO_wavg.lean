-- Prove2me | Definitions.Def_DynChoiceJEO_wavg
-- name    : DynChoiceJEO_wavg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:38:41.903278+00:00
-- url     : https://prove2.me/theorems/43dea568-0bb5-4c0c-a89a-d97310a7b7bb
-- title:
--   Weighted average $\bar x^\theta_T=\frac1{\Theta_T}\sum_{t\in[T]}\theta_t x_t$
-- statement:
--   Given points $v_1,\dots,v_T\in\mathbb R^n$ and real weights $\theta_1,\dots,\theta_T$, write $\Theta_T:=\sum_{t\in[T]}\theta_t$ and
--
--   $$\bar v^\theta_T:=\frac1{\Theta_T}\sum_{t\in[T]}\theta_t v_t .$$
--
--   Applied to a primal sequence $x_t\in\mathbb R^N$ it gives $\bar x^\theta_T$, and to a dual sequence $y_t\in\mathbb R^k$ it gives $\bar y^\theta_T$, the aggregated primal-dual pair of the paper's framework.
--
--   **Formalization Note** $[T]$ is `Fin T` (0-based) and $\mathbb R^n$ is `Fin n → ℝ`. For $\Theta_T=0$ Lean returns $0$; every theorem using the average assumes $\Theta_T>0$.
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Dynamic Data-Driven Estimation of Non-Parametric Choice Models, arXiv:1702.05702v5, eq. (10), p.10

import Mathlib

namespace DynChoiceJEO

/-- **Weighted average `x̄_T^θ = (1/Θ_T) ∑_{t∈[T]} θ_t x_t`.**
Ho-Nguyen & Kılınç-Karzan, *Dynamic Data-Driven Estimation of Non-Parametric Choice Models*, arXiv:1702.05702v5, eq. (10), p.10: "Θ_T := ∑_{t∈[T]} θ_t, x̄_T^θ := (1/Θ_T) ∑_{t∈[T]} θ_t x_t,
ȳ_T^θ := (1/Θ_T) ∑_{t∈[T]} θ_t y_t".

`wavg θ v` is `(∑ t, θ t)⁻¹ • ∑ t, θ t • v t` for weights `θ : Fin T → ℝ` and points
`v : Fin T → ℝⁿ`. The same definition gives both `x̄_T^θ` (with `n = N`) and `ȳ_T^θ` (with
`n = k`).

**Formalization Note** The time index set `[T] = {1,…,T}` is `Fin T` (0-based). `ℝⁿ` is
`Fin n → ℝ`. When `Θ_T = 0` Lean's `0⁻¹ = 0` makes the average `0`; every theorem using it
assumes `Θ_T > 0`. -/
noncomputable def wavg {n T : ℕ} (θ : Fin T → ℝ) (v : Fin T → Fin n → ℝ) : Fin n → ℝ :=
  (∑ t, θ t)⁻¹ • ∑ t, θ t • v t

end DynChoiceJEO


