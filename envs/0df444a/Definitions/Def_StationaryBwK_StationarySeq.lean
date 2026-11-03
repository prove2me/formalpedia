-- Prove2me | Definitions.Def_StationaryBwK_StationarySeq
-- name    : StationaryBwK_StationarySeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:50:30.616475+00:00
-- url     : https://prove2.me/theorems/45e4c84a-b58e-40b2-97f0-7a7be6da59cc
-- title:
--   $\sigma$-stationary sequence on $[T]$ (Definition 3.1)
-- statement:
--   A real sequence $f$ is **$\sigma$-stationary on the rounds $[T]=\{1,\dots,T\}$** if
--   $$\min_{t\in[T]}f(t)\ \ge\ \sigma\max_{t\in[T]}f(t),$$
--   equivalently $\sigma f(s)\le f(t)$ for all $s,t\in[T]$.
--
--   This is the per-action condition of Definition 3.1: an adversary is $(\sigma_r,\sigma_c)$-stationary when every action's conditional expected reward is $\sigma_r$-stationary and every action's conditional expected consumption of every resource is $\sigma_c$-stationary. Lemmas A.1 and A.2 use it directly.
--
--   **Formalization Note** The pairwise form is used because it needs no $\min$/$\max$ over a finite set.
-- source:
--   G. Fikioris and É. Tardos, Approximately Stationary Bandits with Knapsacks, arXiv:2302.14686v2 [cs.LG] (preprint, 8 Jul 2023), https://arxiv.org/abs/2302.14686v2, §3, Definition 3.1, p.6

import Mathlib

namespace StationaryBwK

/-- A sequence `f` is `σ`-stationary on the rounds `[T] = {1, …, T}` if
`min_{t∈[T]} f(t) ≥ σ · max_{t∈[T]} f(t)` (Fikioris & Tardos, arXiv:2302.14686v2,
Definition 3.1, p.6).

**Formalization Note.** For a finite nonempty index set, `min_t f(t) ≥ σ max_t f(t)` is the same
as `σ f(s) ≤ f(t)` for all `s, t ∈ [T]`, which is the form used here. -/
def IsStationarySeq (σ : ℝ) (T : ℕ) (f : ℕ → ℝ) : Prop :=
  ∀ s ∈ Finset.Icc 1 T, ∀ t ∈ Finset.Icc 1 T, σ * f s ≤ f t

end StationaryBwK


