-- Prove2me | Definitions.Def_DantzigSelector_Oracle_Model
-- name    : DantzigSelector_Oracle_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:29:54.671977+00:00
-- url     : https://prove2.me/theorems/32d6c94d-2438-40ca-8045-2478a5179376
-- title:
--   Ideal mean squared error (1.11) and the constants $C_0$, $C_2$ of (1.14)
-- statement:
--   This module fixes the objects specific to Candès and Tao's oracle inequality for the Dantzig selector (Theorem 1.2). The design matrix, unit-normed columns, sparsity, the Dantzig selector (1.7)–(1.8), the restricted norms and the top block of Lemma 3.1 are the shared definitions of `DantzigSelector.Sparse.Model`; the restricted isometry constant $\delta_S$ and the restricted orthogonality constant $\theta_{S,S'}$ are the published definitions of the *Decoding by Linear Programming* series.
--
--   1. **Ideal MSE** ((1.11), p. 7): for $\beta\in\mathbb R^p$ and a noise level $\sigma$, the proxy for the ideal risk
--   $$\sum_{i=1}^p\min(\beta_i^2,\sigma^2).$$
--   2. **Constants** ((1.14), p. 9): for reals $\delta,\theta$,
--   $$C_0=2\sqrt2\Big(1+\frac{1-\delta^2}{1-\delta-\theta}\Big)+\Big(1+\frac1{\sqrt2}\Big)\frac{(1+\delta)^2}{1-\delta-\theta},\qquad C_2=\frac{2C_0}{1-\delta-\theta}+\frac{2\theta(1+\delta)}{(1-\delta-\theta)^2}+\frac{1+\delta}{1-\delta-\theta}.$$
--   The paper evaluates them at $\delta=\delta_{2S}$ and $\theta=\theta_{S,2S}$.
--
--   These are the quantities in which the oracle inequality (1.13) is stated.
--
--   **Formalization Note** $C_0$ and $C_2$ take $\delta,\theta$ as real arguments; every theorem of the mission passes the published $\delta_{2S}$ and $\theta_{S,2S}$ of $X$ and only uses them where $\delta+\theta<1$, so the denominators are positive (Lean's $x/0=0$ is never reached). Vectors are functions `Fin p → ℝ`.
-- source:
--   Candès & Tao, The Dantzig Selector: Statistical Estimation When p Is Much Larger than n, arXiv:math/0506081v3, p. 3 (S-sparse), p. 4, Eqs. (1.7)-(1.8) and unit-normed columns, p. 7, Eq. (1.11), p. 9, Eq. (1.14), p. 15 (Section 3 preamble), p. 17 (Lemma 3.1)

import Mathlib
import Definitions.Def_CandesTao_Decoding_Norms
import Definitions.Def_CandesTao_Decoding_RestrictedIsometry
import Definitions.Def_DantzigSelector_Sparse_Model

namespace DantzigSelector.Oracle

open CandesTao.Decoding

/-- Candès–Tao (2007), (1.11), p. 7: the ideal mean squared error `∑_{i=1}^p min(β_i², σ²)`. -/
noncomputable def idealMSE {p : ℕ} (β : Fin p → ℝ) (σ : ℝ) : ℝ :=
  ∑ i, min (β i ^ 2) (σ ^ 2)

/-- Candès–Tao (2007), (1.14), p. 9: the constant
`C0 = 2√2 (1 + (1 − δ²)/(1 − δ − θ)) + (1 + 1/√2) (1 + δ)²/(1 − δ − θ)`, to be evaluated at
`δ = δ_{2S}`, `θ = θ_{S,2S}`. -/
noncomputable def C0 (δ θ : ℝ) : ℝ :=
  2 * Real.sqrt 2 * (1 + (1 - δ ^ 2) / (1 - δ - θ)) +
    (1 + 1 / Real.sqrt 2) * (1 + δ) ^ 2 / (1 - δ - θ)

/-- Candès–Tao (2007), (1.14), p. 9: the constant
`C2 = 2 C0/(1 − δ − θ) + 2 θ(1 + δ)/(1 − δ − θ)² + (1 + δ)/(1 − δ − θ)`, to be evaluated at
`δ = δ_{2S}`, `θ = θ_{S,2S}`. -/
noncomputable def C2 (δ θ : ℝ) : ℝ :=
  2 * C0 δ θ / (1 - δ - θ) + 2 * θ * (1 + δ) / (1 - δ - θ) ^ 2 + (1 + δ) / (1 - δ - θ)

end DantzigSelector.Oracle


