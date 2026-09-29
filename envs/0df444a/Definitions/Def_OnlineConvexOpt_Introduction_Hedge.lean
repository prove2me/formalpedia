-- Prove2me | Definitions.Def_OnlineConvexOpt_Introduction_Hedge
-- name    : OnlineConvexOpt_Introduction_Hedge
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T05:05:37.866721+00:00
-- url     : https://prove2.me/theorems/03369332-ff65-4d90-942c-9ade073017ba
-- title:
--   One run of the Hedge algorithm and its cumulative losses
-- statement:
--   Defines `IsHedgeRun`, one run of the Hedge algorithm (Algorithm 1, Hazan p. 12) with
--   $N$ experts and learning rate $\varepsilon$, against an adversarially chosen non-negative loss
--   sequence $\ell : \mathbb N \to (\text{Fin } N \to \mathbb R)$, where $\ell_t(i)$ is
--   expert $i$'s loss at round $t$. Weights start at $W_0(i) = 1$ and update multiplicatively in
--   the loss,
--   $$
--   W_{t+1}(i) = W_t(i)\, e^{-\varepsilon\, \ell_t(i)},
--   $$
--   and Hedge's mixed strategy $x_t$ normalizes them to a probability vector,
--   $x_t(i) = W_t(i) / \sum_j W_t(j)$. Alongside the run predicate, this file defines
--   `expectedLoss x ℓ T`, Hedge's cumulative expected loss $\sum_{t=1}^T x_t^\top \ell_t$ over
--   rounds $1,\dots,T$ (Hazan's vector notation, p. 12), and `expertLoss ℓ i T`, expert $i$'s own
--   cumulative loss $\sum_{t=1}^T \ell_t(i)$.
--
--   **Formalization Note.** As with the mistake-count definitions, rounds are indexed from $0$, so
--   `expectedLoss x ℓ T` sums over the book's rounds $1,\dots,T$. `IsHedgeRun` is a `Prop`-valued
--   structure on `ℓ`, `W` and `x`; the algorithm is not required to be an executable recursive
--   definition, only to satisfy the stated initial condition and update rule.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 12, Algorithm 1

import Mathlib

namespace OnlineConvexOpt.Introduction

variable {N : ℕ}

/-- One run of the Hedge algorithm (Algorithm 1, p. 12) with `N` experts and learning rate
`ε`, against an adversarially chosen non-negative loss sequence `ℓ : ℕ → Fin N → ℝ`
(`ℓ_t(i)` is expert `i`'s loss at round `t`). `W` are the weights (`W_1(i) = 1`, updated as
`W_{t+1}(i) = W_t(i) e^{-ε ℓ_t(i)}`); `x` is Hedge's mixed strategy, the weights normalized to
a probability vector, `x_t(i) = W_t(i) / ∑_j W_t(j)`. -/
structure IsHedgeRun (ε : ℝ) (ℓ : ℕ → Fin N → ℝ) (W : ℕ → Fin N → ℝ)
    (x : ℕ → Fin N → ℝ) : Prop where
  weight_init : ∀ i, W 0 i = 1
  weight_update : ∀ t i, W (t + 1) i = W t i * Real.exp (-ε * ℓ t i)
  prob_def : ∀ t i, x t i = W t i / ∑ j, W t j

/-- Hedge's cumulative expected loss over rounds `0, …, T - 1`,
`∑_{t=1}^T x_t^\top \ell_t` in the book's vector notation, p. 12. -/
noncomputable def expectedLoss {N : ℕ} (x ℓ : ℕ → Fin N → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, ∑ i, x t i * ℓ t i

/-- Expert `i`'s cumulative loss over rounds `0, …, T - 1`, `∑_{t=1}^T \ell_t(i)`. -/
noncomputable def expertLoss {N : ℕ} (ℓ : ℕ → Fin N → ℝ) (i : Fin N) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, ℓ t i

end OnlineConvexOpt.Introduction


