-- Prove2me | Definitions.Def_PoSShares_Stability_VarianceSeq
-- name    : PoSShares_Stability_VarianceSeq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:36.548228+00:00
-- url     : https://prove2.me/theorems/aff649c6-f2f4-4bc4-90f9-fcd43b2f0dcb
-- title:
--   (A12), (A16) — the variance recursions $a_t$ and $\alpha_n$
-- statement:
--   Two deterministic sequences from the appendix of Roşu and Saleh.
--
--   For $\nu \in \mathbb{R}$ and $\theta_1, \theta_2, \ldots \in \mathbb{R}$, the sequence of (A16) is
--   $$\alpha_0 = 0, \qquad \alpha_{n+1} = \alpha_n + \Big(\frac{\theta_{n+1}}{\nu + \sum_{k=1}^{n+1}\theta_k}\Big)^2 (1 - \alpha_n),$$
--   so that $\alpha_1 = \big(\theta_1/(\nu + \theta_1)\big)^2$ as printed.
--
--   For an initial supply $N_0$ and rewards $R_1, R_2, \ldots$, the **variance sequence** of (A12) is the same recursion with $\nu = N_0$ and $\theta = R$:
--   $$a_0 = 0, \qquad a_{t+1} = a_t + \Big(\frac{R_{t+1}}{N_{t+1}}\Big)^2 (1 - a_t), \qquad N_t = N_0 + \sum_{n=1}^t R_n,$$
--   so that $a_1 = (R_1/N_1)^2$. By Lemma 2, $a_t$ is the variance of the investor's share at $t$ divided by $\pi_0(1-\pi_0)$.
--
--   **Formalization Note.** The start $a_0 = 0$ is the paper's own extension (proof of Lemma 4, p. 21). The file also records the recursion (A12) for $a_t$ and $a_0 = 0$ as definitional lemmas.
-- source:
--   Roşu, Saleh, Evolution of Shares in a Proof-of-Stake Cryptocurrency, author's manuscript of July 30, 2020 (sha256 90d9c06b…2b35eb), p. 20, Lemma 2 (A12); pp. 20–21, Lemma 3 (A16); p. 21, proof of Lemma 4 (a_0 = 0)

import Mathlib
import Definitions.Def_PoSShares_Stability_Model

namespace PoSShares.Stability

/-! # The variance recursions (A12) and (A16)

Roşu, Saleh, *Evolution of Shares in a Proof-of-Stake Cryptocurrency*, author's manuscript of
July 30, 2020 (sha256 90d9c06b…2b35eb), p. 20 (Lemma 2, (A12)), pp. 20–21 (Lemma 3, (A16)),
p. 21 (proof of Lemma 4: "We extend the sequence a_t at t = 0 by a_0 = 0").

**Formalization Note.** Both sequences start at index `0` with value `0` (the paper's own extension
`a_0 = 0`, proof of Lemma 4, p. 21). The recursion then reproduces the printed first terms
`α_1 = (θ_1/(ν + θ_1))^2` and `a_1 = (R_1/N_1)^2`. `θ 0` and `R 0` are never used.
-/

/-- The sequence of (A16) (Lemma 3, pp. 20–21), extended by `α_0 = 0`:
`α_{n+1} = α_n + (θ_{n+1} / (ν + Σ_{k=1}^{n+1} θ_k))^2 (1 − α_n)`. -/
noncomputable def alphaSeq (ν : ℝ) (θ : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => alphaSeq ν θ n
      + (θ (n + 1) / (ν + ∑ k ∈ Finset.Icc 1 (n + 1), θ k)) ^ 2 * (1 - alphaSeq ν θ n)

/-- The variance sequence `a_t` of (A12) (Lemma 2, p. 20), extended by `a_0 = 0`:
`a_{t+1} = a_t + (R_{t+1}/N_{t+1})^2 (1 − a_t)` with `N_t = N_0 + Σ_{n=1}^t R_n`.
It is the sequence (A16) with `ν = N_0` and `θ = R`. -/
noncomputable def aSeq (N₀ : ℝ) (R : ℕ → ℝ) : ℕ → ℝ :=
  alphaSeq N₀ R

/-- The recursion (A12) in the paper's notation: `a_{t+1} = a_t + (R_{t+1}/N_{t+1})^2 (1 − a_t)`. -/
theorem aSeq_succ (N₀ : ℝ) (R : ℕ → ℝ) (t : ℕ) :
    aSeq N₀ R (t + 1) =
      aSeq N₀ R t + (R (t + 1) / coinSupply N₀ R (t + 1)) ^ 2 * (1 - aSeq N₀ R t) := rfl

theorem aSeq_zero (N₀ : ℝ) (R : ℕ → ℝ) : aSeq N₀ R 0 = 0 := rfl

end PoSShares.Stability


