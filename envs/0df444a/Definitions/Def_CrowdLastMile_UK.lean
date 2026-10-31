-- Prove2me | Definitions.Def_CrowdLastMile_UK
-- name    : CrowdLastMile_UK
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:22:01.62737+00:00
-- url     : https://prove2.me/theorems/946f56a7-121e-409f-9525-12138b32f08e
-- title:
--   Uncertainty set $U_K$ of opportunity costs (6)
-- statement:
--   For means $\mu_1,\dots,\mu_{\mathbb N}$, standard deviations $\sigma_1,\dots,\sigma_{\mathbb N}$ and a conservatism level $\gamma$, the uncertainty set of the crowd's opportunity costs is
--
--   $$
--   U_K=\left\{(K_1,\dots,K_{\mathbb N})\ge 0:\ \left|\frac{\sum_{i\in I}(K_i-\mu_i)}{\sqrt{\sum_{i\in I}\sigma_i^2}}\right|\le\gamma\quad\forall I\subseteq\{1,\dots,\mathbb N\}\right\}.
--   $$
--
--   The module also defines, for $S\subseteq\{1,\dots,\mathbb N\}$, the set of values of $(\sum_{i\in S}K_i)/N$ as $K$ ranges over $U_K$; Lemma 1 computes its maximum.
--
--   This is the CLT-motivated set over which the worst case of the drivers' opportunity costs is taken.
--
--   **Formalization Note** The ground set is `Fin pop`. The condition is required for non-empty $I$, because at $I=\emptyset$ the printed quotient is $0/0$.
-- source:
--   Fatehi–Wagner, Crowdsourcing Last-Mile Deliveries, SSRN 3434625, eq. (6), p.11; Lemma 1, p.12

import Mathlib

namespace CrowdLastMile

/-- The CLT-motivated uncertainty set `U_K` of the crowd's opportunity costs, eq. (6):
the nonnegative vectors `(K_1, …, K_ℕ)` with
`|∑_{i∈I} (K_i - μ_i)| / √(∑_{i∈I} σ_i²) ≤ γ` for every `I ⊆ {1, …, ℕ}`.
Fatehi–Wagner, Crowdsourcing Last-Mile Deliveries, SSRN 3434625, eq. (6), p.11.

**Formalization Note.** The ground set `{1, …, ℕ}` is `Fin pop`. The condition is required for
non-empty `I`: at `I = ∅` the printed quotient is `0/0`, which is undefined. -/
def UK {pop : ℕ} (μ σ : Fin pop → ℝ) (γ : ℝ) : Set (Fin pop → ℝ) :=
  {K | (∀ i, 0 ≤ K i) ∧
    ∀ I : Finset (Fin pop), I.Nonempty →
      |∑ i ∈ I, (K i - μ i)| / Real.sqrt (∑ i ∈ I, (σ i) ^ 2) ≤ γ}

/-- The values of the objective `(∑_{i∈S} K_i)/N` of Lemma 1 as `K` ranges over `U_K`.
Fatehi–Wagner, Crowdsourcing Last-Mile Deliveries, SSRN 3434625, Lemma 1, p.12. -/
def subsetAverages {pop : ℕ} (μ σ : Fin pop → ℝ) (γ : ℝ) (N : ℕ) (S : Finset (Fin pop)) : Set ℝ :=
  (fun K : Fin pop → ℝ => (∑ i ∈ S, K i) / (N : ℝ)) '' UK μ σ γ

end CrowdLastMile


