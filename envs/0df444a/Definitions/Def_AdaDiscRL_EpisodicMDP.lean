-- Prove2me | Definitions.Def_AdaDiscRL_EpisodicMDP
-- name    : AdaDiscRL_EpisodicMDP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:25:56.317071+00:00
-- url     : https://prove2.me/theorems/42af52b5-76b5-45f3-842f-53961894d4fd
-- title:
--   Episodic Markov decision process $(\mathcal S,\mathcal A,H,T,R)$ with reward kernels
-- statement:
--   An **episodic Markov decision process** consists of a state space $\mathcal S$, an action space $\mathcal A$ (both measurable spaces), a horizon $H$, and for every step $h\in[H]$:
--
--   1. a transition kernel $T_h(\cdot\mid x,a)\in\Delta(\mathcal S)$, the law of the next state when action $a$ is taken in state $x$;
--   2. a reward distribution $R_h(x,a)\in\Delta([0,1])$.
--
--   The **mean reward** is $r_h(x,a)=\mathbb E_{r\sim R_h(x,a)}[r]$.
--
--   This is the general object on which the adaptive-discretization algorithms AdaMB and AdaQL act; the value functions, the gap, and the regret are all built from it.
--
--   **Formalization Note** Steps are indexed by `Fin H`, so the Lean step $h$ is the paper's step $h+1$. Both families are Markov kernels (measurable in $(x,a)$); the reward law is a probability measure on $\mathbb R$ that gives full mass to $[0,1]$.
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, Definition 2.1, p.8

import Mathlib

open MeasureTheory ProbabilityTheory

namespace AdaDiscRL

/-- **Episodic Markov decision process** (Sinclair, Banerjee & Yu, *Adaptive Discretization in
Online Reinforcement Learning*, arXiv:2110.15843v3, Definition 2.1, p.8).

An episodic MDP `(S, A, H, T, R)` has horizon `H`, transition kernels `T h : S × A → Δ(S)` and
reward kernels `R h : S × A → Δ([0,1])`, one of each per step.

**Formalization Note.** Steps are `h : Fin H`, where `h` is the paper's step `h + 1`. The reward
law `R h (x, a)` is a probability measure on `ℝ` giving full mass to `[0, 1]`. Both families are
Markov kernels, hence measurable in `(x, a)`. -/
structure EpisodicMDP (S A : Type*) [MeasurableSpace S] [MeasurableSpace A] (H : ℕ) where
  /-- transition kernel `T_h(· | x, a)` -/
  T : Fin H → Kernel (S × A) S
  /-- reward distribution `R_h(x, a)` -/
  R : Fin H → Kernel (S × A) ℝ
  isMarkov_T : ∀ h, IsMarkovKernel (T h)
  isMarkov_R : ∀ h, IsMarkovKernel (R h)
  R_mem_unit : ∀ h p, R h p (Set.Icc (0 : ℝ) 1)ᶜ = 0

/-- The mean reward `r_h(x, a) = 𝔼_{r ∼ R_h(x,a)}[r]` (Definition 2.1, p.8). -/
noncomputable def EpisodicMDP.meanReward {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    {H : ℕ} (M : EpisodicMDP S A H) (h : Fin H) (p : S × A) : ℝ :=
  ∫ r, r ∂(M.R h p)

end AdaDiscRL


