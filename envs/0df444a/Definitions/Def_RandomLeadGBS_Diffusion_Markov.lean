-- Prove2me | Definitions.Def_RandomLeadGBS_Diffusion_Markov
-- name    : RandomLeadGBS_Diffusion_Markov
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:54.646992+00:00
-- url     : https://prove2.me/theorems/cd5ec887-2dda-48f3-9f6f-b9bf019be384
-- title:
--   Stationary distributions of countable continuous-time and discrete-time Markov chains (global balance with finite mean exit rate)
-- statement:
--   Let $S$ be a countable state space.
--
--   1. **Continuous time.** A continuous-time Markov chain on $S$ is described by its transition rates $q(s,s') \ge 0$ (the rate of a jump from $s$ to $s'$) and its exit rates $q(s)$ (the total rate of leaving $s$). A function $p : S \to \mathbb R$ is a *stationary distribution* of the chain if $p \ge 0$, $\sum_s p(s) = 1$ (the series converging), the mean exit rate $\sum_s p(s)\,q(s)$ is finite, and global balance holds at every state:
--   $$
--   \sum_{s\in S} p(s)\,q(s,s') = p(s')\,q(s') \qquad \text{for all } s'\in S .
--   $$
--   2. **Discrete time.** For one-step transition probabilities $K(s,s')$, a function $p$ is a *stationary distribution* if $p\ge 0$, $\sum_s p(s)=1$ and $\sum_s p(s)K(s,s') = p(s')$ for every $s'$.
--
--   These are the notions of "stationary regime" used throughout Stolyar and Wang's analysis of the generalized base-stock policy, for the two-dimensional inventory chain, the one-dimensional artificial chain and the reflected random walk $Q_n$.
--
--   **Formalization Note** The finiteness of the mean exit rate is a convention made explicit: on an unbounded state space a probability solution of global balance with finite mean exit rate is exactly an invariant law of the non-explosive jump dynamics. Sums are Lean `tsum`s; summability of $p$ and of $p\cdot q$ is required explicitly.
-- source:
--   Stolyar and Wang, Exploiting random lead times for significant inventory cost savings, arXiv:1801.02646v6, pp. 4, 13, 16–17 (the stationary regime X(∞), p. 4; steady state of the GBS process, p. 13; the embedded chain Q_n, p. 16)

import Mathlib

namespace RandomLeadGBS.Diffusion

/-- A stationary distribution of a continuous-time Markov chain on a countable state type `S`,
given by its transition rates `q s s'` (rate of a jump from `s` to `s'`) and its exit rates
`qx s` (total rate of leaving `s`). The law `p` is a probability mass function, the mean exit
rate `∑ p s * qx s` is finite, and global balance holds at every state: the probability flux
into `s'` equals the flux out of `s'`. -/
def IsCTMCStationary {S : Type*} (q : S → S → ℝ) (qx : S → ℝ) (p : S → ℝ) : Prop :=
  (∀ s, 0 ≤ p s) ∧ Summable p ∧ ∑' s, p s = 1 ∧
  Summable (fun s => p s * qx s) ∧
  ∀ s', ∑' s, p s * q s s' = p s' * qx s'

/-- A stationary distribution of a discrete-time Markov chain on a countable state type `S`
with one-step transition probabilities `K s s'`: a probability mass function `p` with
`∑ s, p s * K s s' = p s'` for every `s'`. -/
def IsDTMCStationary {S : Type*} (K : S → S → ℝ) (p : S → ℝ) : Prop :=
  (∀ s, 0 ≤ p s) ∧ Summable p ∧ ∑' s, p s = 1 ∧
  ∀ s', ∑' s, p s * K s s' = p s'

end RandomLeadGBS.Diffusion


