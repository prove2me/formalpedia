-- Prove2me | Definitions.Def_ScalableMARL_StepSizes
-- name    : ScalableMARL_StepSizes
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:46:35.229713+00:00
-- url     : https://prove2.me/theorems/fc18a19e-a8b3-4497-bfda-df8458958a68
-- title:
--   Step-size products $\beta_{k,t}$, $\tilde\beta_{k,t}$ and $b_{k,t}$
-- statement:
--   With the critic step size $\alpha_\ell=h/(\ell+t_0)$, the proof of Theorem 5 uses the products (pp. 17–18)
--   $$\beta_{k,t}=\alpha_k\prod_{\ell=k+1}^{t-1}(1-\alpha_\ell\sigma),\qquad\tilde\beta_{k,t}=\prod_{\ell=k+1}^{t-1}(1-\alpha_\ell\sigma),\qquad b_{k,t}=\alpha_k\bar d_k\prod_{\ell=k+1}^{t-1}(1-\alpha_\ell\bar d_\ell),$$
--   where in $b_{k,t}$ the sequence $\bar d_k$ is, on the page, the marginal probability of a fixed local pair $z_{N_i^\kappa}$ at step $k$. Empty products equal $1$.
--
--   These enter Lemma 9 and Lemma 12, which bound the transient of the critic recursion.
--
--   **Formalization Note** $\bar d$ is an arbitrary real sequence here; Lemma 12 assumes $\sigma\le\bar d_k\le1$.
-- source:
--   Qu, Wierman & Li, Scalable Reinforcement Learning for Multi-Agent Networked Systems, arXiv:1912.02906v3, p. 17 (β, β̃), p. 18 (Lemma 7, b_{k,t}), p. 19 (Lemma 12)

import Mathlib

namespace ScalableMARL

/-- `β_{k,t} = α_k ∏_{ℓ=k+1}^{t−1} (1 − α_ℓ σ)` with `α_ℓ = h/(ℓ + t₀)` (p. 17). The product is
empty (equal to 1) when `t ≤ k + 1`. -/
noncomputable def betaKT (h t₀ σ : ℝ) (k t : ℕ) : ℝ :=
  h / (k + t₀) * ∏ ℓ ∈ Finset.Ico (k + 1) t, (1 - h / (ℓ + t₀) * σ)

/-- `β̃_{k,t} = ∏_{ℓ=k+1}^{t−1} (1 − α_ℓ σ)` with `α_ℓ = h/(ℓ + t₀)` (p. 17). -/
noncomputable def betaTildeKT (h t₀ σ : ℝ) (k t : ℕ) : ℝ :=
  ∏ ℓ ∈ Finset.Ico (k + 1) t, (1 - h / (ℓ + t₀) * σ)

/-- `b_{k,t} = α_k d̄_k ∏_{ℓ=k+1}^{t−1} (1 − α_ℓ d̄_ℓ)` with `α_ℓ = h/(ℓ + t₀)` (Lemma 7, p. 18, and
Lemma 12, p. 19), for a sequence `d̄` (there, the marginal probabilities of a fixed local pair). -/
noncomputable def bKT (h t₀ : ℝ) (dbar : ℕ → ℝ) (k t : ℕ) : ℝ :=
  h / (k + t₀) * dbar k * ∏ ℓ ∈ Finset.Ico (k + 1) t, (1 - h / (ℓ + t₀) * dbar ℓ)

end ScalableMARL


