-- Prove2me | Definitions.Def_NonstatRL_PerStep_EVIOutput
-- name    : NonstatRL_PerStep_EVIOutput
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T06:17:37.769382+00:00
-- url     : https://prove2.me/theorems/6c840f87-d8ea-41b6-b0da-ae5b4afcff02
-- title:
--   Extended value-iteration output contract
-- statement:
--   An extended value-iteration output consists of an allowed deterministic policy $\tilde\pi$, selected reward and transition arrays $(\tilde r,\tilde p)$ in the episode-start confidence sets, a gain $\tilde\rho$, and a nonnegative bias $\tilde\gamma$ with at least one zero entry. Its optimistic inequality dominates the reward and bias-weighted transition value of every point in those sets. Its near-optimality inequality has error $1/\sqrt{\tau(m)}$ on the action selected by the policy.
--
--   $$
--   \tilde\rho+\tilde\gamma(s)\ge r'(s,a)+\sum_{s'}p'(s'\mid s,a)\tilde\gamma(s'),\qquad
--   \tilde r(s,\tilde\pi(s))\ge\tilde\rho+\tilde\gamma(s)-\sum_{s'}\tilde p(s'\mid s,\tilde\pi(s))\tilde\gamma(s')-\frac1{\sqrt{\tau(m)}}.
--   $$
--
--   This contract exposes exactly the output properties used by the paper's per-step analysis. **Formalization Note** The EVI algorithm is abstracted by these stated properties. The first inequality is the standard joint-distribution form implied by the stronger coordinatewise-maxima expression printed as Property 1. The one-based episode start $\tau(m)$ is represented by zero-based index $\tau_m$ and error $1/\sqrt{\tau_m+1}$.
-- source:
--   Cheung, Simchi-Levi & Zhu, Non-Stationary Reinforcement Learning: The Blessing of (More) Optimism, arXiv:1906.02922v4, p. 13, EVI output; pp. 35–36, Algorithm 3 and Properties 1–2

import Mathlib
import Definitions.Def_NonstatRL_PerStep_Window

open BanditAlgorithm

namespace NonstatRL.PerStep

structure IsEVIOutput {S A : ℕ} (As : Fin S → Finset (Fin A))
    (T : ℕ) (δ η : ℝ) (W τm : ℕ)
    (st : ℕ → Fin S) (ac : ℕ → Fin A) (R : ℕ → ℝ)
    (πt : Fin S → Fin A) (rt : Fin S → Fin A → ℝ)
    (pt : Fin S → Fin A → Fin S → ℝ)
    (ρt : ℝ) (γt : Fin S → ℝ) : Prop where
  allowed : ∀ s, πt s ∈ As s
  reward_mem : ∀ s a, a ∈ As s →
    rt s a ∈ Hr As T δ st ac R (τm - W) τm s a
  transition_mem : ∀ s a, a ∈ As s →
    (pt s a) ∈ Hp As T δ st ac (τm - W) τm η s a
  bias_nonneg : ∀ s, 0 ≤ γt s
  bias_zero : ∃ s, γt s = 0
  optimistic : ∀ s a, a ∈ As s →
    ∀ v ∈ Hr As T δ st ac R (τm - W) τm s a,
    ∀ p ∈ Hp As T δ st ac (τm - W) τm η s a,
      v + (∑ s' : Fin S, γt s' * p s') ≤ ρt + γt s
  near_optimal : ∀ s,
    ρt + γt s - (∑ s' : Fin S, pt s (πt s) s' * γt s') -
      1 / Real.sqrt (τm + 1) ≤ rt s (πt s)

end NonstatRL.PerStep


