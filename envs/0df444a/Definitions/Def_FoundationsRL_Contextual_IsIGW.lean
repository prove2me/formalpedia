-- Prove2me | Definitions.Def_FoundationsRL_Contextual_IsIGW
-- name    : FoundationsRL_Contextual_IsIGW
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T04:58:37.478715+00:00
-- url     : https://prove2.me/theorems/fbd95cd8-35e8-47de-a9af-bd99c5dd3076
-- title:
--   Definition 4 — Inverse Gap Weighting distribution
-- statement:
--   This definition formalizes the **Inverse Gap Weighting** (IGW) distribution (Definition 4,
--   Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
--   p. 50), a sampling rule over a finite decision set $\Pi = \{1,\dots,A\}$ built from a vector
--   of estimated values.
--
--   Given a vector $\hat f = (\hat f(1),\dots,\hat f(A)) \in \mathbb{R}^A$ and an exploration
--   parameter $\gamma \ge 0$, let $\bar\pi = \arg\max_\pi \hat f(\pi)$ be the greedy action. The
--   IGW distribution $p = \mathrm{IGW}_\gamma(\hat f)$ is
--
--   $$
--   p(\pi) = \frac{1}{\lambda + 2\gamma\bigl(\hat f(\bar\pi) - \hat f(\pi)\bigr)},
--   $$
--
--   where $\lambda \in [1, A]$ is the unique normalizing constant making $p$ sum to one; the
--   source establishes its existence via a continuity/intermediate-value argument rather than an
--   explicit formula. The predicate `IsIGW A fhat γ bstar p` packages exactly this: `bstar` is a
--   maximizer of `fhat`, some `lam ∈ [1, A]` realizes the displayed formula for every action, and
--   `p` is a genuine probability vector (nonnegative, summing to one).
--
--   Small $\gamma$ gives a near-uniform distribution (more exploration); large $\gamma$
--   concentrates mass on the greedy action. Proposition 9 shows this specific family of
--   distributions gives an optimal trade-off between the resulting instantaneous regret and the
--   estimation error of $\hat f$, for any $\hat f$ and any ground-truth vector — the key primitive
--   behind the SquareCB algorithm.
--
--   **Formalization Note** The source defines $\lambda$ implicitly, as the unique point in
--   $[1, A]$ at which $\sum_\pi p(\pi) = 1$; rather than constructing $\lambda$ via Mathlib's
--   intermediate value theorem, this definition states its defining property (existence of such a
--   $\lambda$, together with $p$ summing to one and being nonnegative) directly, following the
--   convention recommended for this mission.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 50, Definition 4

import Mathlib

namespace FoundationsRL.Contextual

/-- The Inverse Gap Weighting distribution property (Foster & Rakhlin, *Foundations of
Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, Definition 4,
p. 50). Given estimated values `fhat : Fin A → ℝ`, an exploration parameter `γ`, and a
greedy action `bstar`, `IsIGW A fhat γ bstar p` asserts that `p` is the distribution
`p(π) = 1 / (λ + 2γ(fhat(bstar) - fhat(π)))` for some normalizing constant `λ ∈ [1, A]`
(guaranteed to exist by the book via a continuity/intermediate-value argument, p. 50) that
makes `p` sum to one, and that `bstar` is indeed a maximizer of `fhat`. -/
structure IsIGW (A : ℕ) (fhat : Fin A → ℝ) (γ : ℝ) (bstar : Fin A) (p : Fin A → ℝ) : Prop where
  greedy : ∀ π, fhat π ≤ fhat bstar
  lam_spec : ∃ lam ∈ Set.Icc (1 : ℝ) (A : ℝ), ∀ π, p π = 1 / (lam + 2 * γ * (fhat bstar - fhat π))
  nonneg : ∀ π, 0 ≤ p π
  sum_one : ∑ π, p π = 1

end FoundationsRL.Contextual


