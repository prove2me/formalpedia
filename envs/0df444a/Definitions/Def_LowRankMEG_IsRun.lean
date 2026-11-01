-- Prove2me | Definitions.Def_LowRankMEG_IsRun
-- name    : LowRankMEG_IsRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:51:47.931304+00:00
-- url     : https://prove2.me/theorems/f66b04d3-31d9-4fb7-bc90-55c871fe0dfe
-- title:
--   A run of Algorithm 2 with deterministic updates
-- statement:
--   Algorithm 2 takes positive step sizes $\{\eta_t\}_{t\ge1}$, approximation parameters $\{\varepsilon_t\}_{t\ge0}\subset[0,1]$, a rank parameter $r\in\{1,\dots,n-1\}$, and $X_0\in\mathcal S_n$ with $\operatorname{rank}(X_0)=r$. It sets
--   $$
--   X_1=(1-\varepsilon_0)X_0+\frac{\varepsilon_0}{n}I,
--   $$
--   and for $t\ge1$ obtains $X_{t+1}$ from $X_t$ by the low-rank update (9) with $\eta=\eta_t$, $\varepsilon=\varepsilon_t$ and $D=\nabla f(X_t)$.
--
--   **Formalization Note** The eigenvectors are chosen step by step, so a theorem about runs covers every valid choice. The stochastic branch of the algorithm is not formalized.
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, Algorithm 2, p.9

import Mathlib
import Definitions.Def_PSDPolyApprox_densityMatrices
import Definitions.Def_LowRankMEG_IsLowRankUpdate

namespace LowRankMEG

/-- **A run of Algorithm 2 with deterministic updates**: step sizes `η_t` (`t ≥ 1`), approximation
parameters `ε_t ∈ [0, 1]` (`t ≥ 0`), SVD rank parameter `r ∈ {1, …, n − 1}`, initialization
`X₀ ∈ 𝒮_n` with `rank(X₀) = r`, `X₁ = (1 − ε₀)X₀ + (ε₀/n)I`, and for `t ≥ 1` the update (9) with
`D = ∇f(X_t)`.
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, Algorithm 2, p.9.

**Formalization Note.** `X : ℕ → _` with `X 0` the input, `η 0` unused. The eigenvectors `Vʳ` are chosen
step by step (`IsLowRankUpdate`), so a theorem about runs covers every valid choice at every step. Algorithm 2
allows `ε_t = 0, 1`, which makes the next iterate singular; statements about runs add the hypothesis
that keeps every `X_t`, `t ≥ 1`, positive definite. -/
structure IsRun {n : ℕ} (grad : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ)
    (η ε : ℕ → ℝ) (r : ℕ) (X : ℕ → Matrix (Fin n) (Fin n) ℝ) : Prop where
  /-- The step sizes are positive. -/
  eta_pos : ∀ t, 1 ≤ t → 0 < η t
  /-- `ε_t ∈ [0, 1]`. -/
  eps_mem : ∀ t, ε t ∈ Set.Icc (0 : ℝ) 1
  /-- `r ∈ {1, …, n − 1}`. -/
  rank_pos : 1 ≤ r
  /-- `r ∈ {1, …, n − 1}`. -/
  rank_lt : r < n
  /-- `X₀ ∈ 𝒮_n`. -/
  init_mem : X 0 ∈ PSDPolyApprox.densityMatrices n
  /-- `rank(X₀) = r`. -/
  init_rank : (X 0).rank = r
  /-- `X₁ = (1 − ε₀)X₀ + (ε₀/n)I`. -/
  first : X 1 = (1 - ε 0) • X 0 + (ε 0 / (n : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ)
  /-- `X_{t+1}` is the low-rank update of `X_t`, for `t ≥ 1`. -/
  step : ∀ t, 1 ≤ t → IsLowRankUpdate (X t) (grad (X t)) (η t) (ε t) r (X (t + 1))

end LowRankMEG


