-- Prove2me | Definitions.Def_StochLinOpt_UpperBound_analysisQuantities
-- name    : StochLinOpt_UpperBound_analysisQuantities
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:28:27.694915+00:00
-- url     : https://prove2.me/theorems/d933141c-3e8d-419c-a384-558c0b9e80f4
-- title:
--   Section 5 quantities: widths $w_t$, regret $R_T$, $Z_t$, $E_t$ and $M_t$
-- statement:
--   This file defines the quantities used in the analysis of ConfidenceBall₂ (Section 5 of Dani, Hayes and Kakade), for decisions $x_t$, losses $\ell_t$, a mean vector $\mu\in\mathbb R^n$, an optimal decision $x^*$ and the parameter $\delta$, with $A_t$, $\hat\mu_t$, $\beta_t$ as in Algorithm 3.1.
--
--   1. **Normalized width** (PDF p. 7): $w_t=\sqrt{x_t^\top A_t^{-1}x_t}$.
--   2. **Cumulative regret** (PDF p. 3): $R_T=\sum_{t=1}^T(\mu^\top x_t-\mu^\top x^*)$, with $R_0=0$.
--   3. **Estimation error** (PDF p. 8): $Z_t=(\hat\mu_t-\mu)^\top A_t(\hat\mu_t-\mu)$.
--   4. **Escape indicator** (PDF p. 9): $E_t=\mathbb 1\{Z_\tau\le\beta_\tau\text{ for all }1\le\tau\le t\}$.
--   5. **Martingale increment** (PDF p. 9, Lemma 13): with noise $\eta_t=\ell_t-\mu^\top x_t$, $$M_t=2\eta_tE_t\,\frac{x_t^\top(\hat\mu_t-\mu)}{1+w_t^2}.$$
--
--   The regret is the quantity the mission bounds; $w_t$ drives the potential argument, and $Z_t$, $E_t$, $M_t$ drive the confidence argument.
--
--   **Formalization Note** Rounds are indexed from $1$ in `ℕ`. $E_t$ is the real number $1$ or $0$. $A_t$ is positive definite, so $w_t$ is the square root of a nonnegative number.
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, PDF p. 3 (regret R_T), PDF p. 7 (w_t), PDF p. 8 (Z_t), PDF p. 9 (E_t and Lemma 13, M_t)

import Mathlib
import Definitions.Def_StochLinOpt_UpperBound_confidenceBall2

open Matrix

namespace StochLinOpt.UpperBound

/-- The normalized width `w_t = √(x_tᵀ A_t⁻¹ x_t)`. -/
noncomputable def width {n : ℕ} (x : ℕ → Fin n → ℝ) (t : ℕ) : ℝ :=
  Real.sqrt (x t ⬝ᵥ ((designMatrix x t)⁻¹ *ᵥ x t))

/-- The cumulative regret `R_T = ∑_{t=1}^T (µ ⬝ᵥ x_t - µ ⬝ᵥ x*)` (`R_0 = 0`). -/
def regret {n : ℕ} (μ xstar : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, (μ ⬝ᵥ x t - μ ⬝ᵥ xstar)

/-- `Z_t = (µ̂_t - µ)ᵀ A_t (µ̂_t - µ)`. -/
noncomputable def zStat {n : ℕ} (μ : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ) (t : ℕ) : ℝ :=
  (muHat x ℓ t - μ) ⬝ᵥ (designMatrix x t *ᵥ (muHat x ℓ t - μ))

open Classical in
/-- The indicator `E_t = 𝟙{Z_τ ≤ β_τ for all 1 ≤ τ ≤ t}`. -/
noncomputable def escapeInd {n : ℕ} (δ : ℝ) (μ : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ)
    (t : ℕ) : ℝ :=
  if ∀ τ ∈ Finset.Icc 1 t, zStat μ x ℓ τ ≤ beta n δ τ then 1 else 0

/-- The martingale increment `M_t = 2 η_t E_t x_tᵀ(µ̂_t - µ) / (1 + w_t²)` with noise
`η_t = ℓ_t - µ ⬝ᵥ x_t`. -/
noncomputable def mIncrement {n : ℕ} (δ : ℝ) (μ : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ)
    (t : ℕ) : ℝ :=
  2 * (ℓ t - μ ⬝ᵥ x t) * escapeInd δ μ x ℓ t * (x t ⬝ᵥ (muHat x ℓ t - μ)) /
    (1 + width x t ^ 2)

end StochLinOpt.UpperBound


