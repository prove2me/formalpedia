-- Prove2me | Definitions.Def_WFMFG_Conv_Multinomial
-- name    : WFMFG_Conv_Multinomial
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:00.894293+00:00
-- url     : https://prove2.me/theorems/acc5fbfe-b808-427d-b18a-95da200c3011
-- title:
--   Notation, p. 5 — the multinomial law $\mathcal M_{N,\mu}$ and the expectation $\mathbf E[F(S_{N,\mu})]$
-- statement:
--   Let $d \ge 1$, $N \ge 0$ and $\mu = (\mu[1], \dots, \mu[d]) \in \mathbb R^d$. For a multi-index $k \in \mathbb N^d$ with $k_1 + \dots + k_d = N$, the **multinomial weight** is
--   $$
--   \mathcal M_{N,\mu}(k) = \frac{N!}{k_1! \cdots k_d!} \prod_{i=1}^d \mu[i]^{k_i}.
--   $$
--   For a real function $F$ of multi-indices, the **multinomial expectation** is the finite sum
--   $$
--   \mathbf E\big[F(S_{N,\mu})\big] = \sum_{k \in \mathbb N^d,\ k_1 + \dots + k_d = N} \mathcal M_{N,\mu}(k)\, F(k).
--   $$
--   When $\mu$ is a probability vector this is the expectation of $F(S_{N,\mu})$ for a random variable $S_{N,\mu}$ with the multinomial distribution of parameters $N$ and $(\mu[1], \dots, \mu[d])$.
--
--   The common noise of the $N$-player game redistributes weights according to this law, so every common-noise term of the Nash system (3.2) and the moment bounds of Lemma 4.5 are written with it.
--
--   **Formalization Note.** The convention $0^0 = 1$ makes a coordinate with $\mu[i] = 0$ contribute only multi-indices with $k_i = 0$, as for the multinomial distribution.
-- source:
--   Bayraktar, Cecchin, Cohen & Delarue, Finite State Mean Field Games with Wright–Fisher Common Noise as Limits of N-Player Weighted Games, arXiv:2012.04845v2, p. 5, Notation (multinomial distribution M_{N,μ})

import Mathlib

open Finset

namespace WFMFG.Conv

/-- The multinomial weight `𝓜_{N,μ}(k) = N!/(k_1! ⋯ k_d!) ∏_i μ[i]^{k_i}` (p. 5), for a
multi-index `k` with `k_1 + ⋯ + k_d = N`. -/
noncomputable def multW {d : ℕ} (p : Fin d → ℝ) (k : Fin d → ℕ) : ℝ :=
  (Nat.multinomial Finset.univ k : ℝ) * ∏ i, p i ^ k i

/-- `E[F(S_{N,μ})]` for `S_{N,μ}` multinomial with parameters `N, (μ[1], …, μ[d])`: the finite
sum of `𝓜_{N,μ}(k) F(k)` over the multi-indices `k ∈ ℕ^d` with `∑ k = N`. -/
noncomputable def multE {d : ℕ} (N : ℕ) (p : Fin d → ℝ) (F : (Fin d → ℕ) → ℝ) : ℝ :=
  ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW p k * F k

end WFMFG.Conv


