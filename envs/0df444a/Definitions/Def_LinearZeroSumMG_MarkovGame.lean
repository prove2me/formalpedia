-- Prove2me | Definitions.Def_LinearZeroSumMG_MarkovGame
-- name    : LinearZeroSumMG_MarkovGame
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:00.740982+00:00
-- url     : https://prove2.me/theorems/8c186849-5c08-41a0-9f2e-fbbcd8e4ae24
-- title:
--   Two-player zero-sum simultaneous-move episodic Markov game $(\mathcal S,\mathcal A,\mathcal A,r,\mathbb P,H)$
-- statement:
--   A **two-player zero-sum simultaneous-move episodic Markov game** consists of
--   1. a measurable state space $\mathcal S$;
--   2. a finite action set $\mathcal A$, the same for both players;
--   3. a horizon $H\in\mathbb N$;
--   4. for each step $h\in[H]$, a deterministic reward $r_h:\mathcal S\times\mathcal A\times\mathcal A\to[-1,1]$, jointly measurable;
--   5. for each step $h\in[H]$, a transition kernel $\mathbb P_h(\cdot\mid x,a,b)$, a probability measure on $\mathcal S$ depending measurably on $(x,a,b)$.
--
--   At step $h$, in state $x$, player P1 plays $a$ and player P2 plays $b$ simultaneously; both observe the reward $r_h(x,a,b)$, which P1 maximizes and P2 minimizes, and the next state is drawn from $\mathbb P_h(\cdot\mid x,a,b)$.
--
--   This is the general object the rest of the mission is built on: the linear structure of Assumption 1, the values, the algorithm and its run all refer to a game of this form.
--
--   **Formalization Note** Steps are 1-based. The reward and kernel are indexed by all $h\in\mathbb N$; only $h\in[1,H]$ is ever used. The bound $|r_h|\le1$ is the paper's standing assumption (p.6).
-- source:
--   Xie, Chen, Wang & Yang, Learning Zero-Sum Simultaneous-Move Markov Games Using Function Approximation and Correlated Equilibrium, arXiv:2002.07066v3, §2.2, pp.5–6

import Mathlib

namespace LinearZeroSumMG

open MeasureTheory ProbabilityTheory

/-- **Two-player zero-sum simultaneous-move episodic Markov game `(𝒮, 𝒜, 𝒜, r, ℙ, H)`.**
Xie, Chen, Wang & Yang, *Learning Zero-Sum Simultaneous-Move Markov Games Using Function
Approximation and Correlated Equilibrium*, arXiv:2002.07066v3, §2.2, pp.5–6: "A two-player,
zero-sum, simultaneous-moves, episodic Markov game is defined by the tuple `(𝒮, 𝒜₁, 𝒜₂, r, ℙ, H)`,
where `𝒮` is the state space, `𝒜ᵢ` is a finite set of actions that player `i ∈ {1, 2}` can take, `r` is
reward function, `ℙ` is transition kernel and `H` is the number of steps in each episode. At each
step `h ∈ [H]`, upon observing the state `x ∈ 𝒮`, P1 and P2 take actions `a ∈ 𝒜₁` and `b ∈ 𝒜₂`,
respectively, and then both receive the reward `r_h(x, a, b)`. The system then transitions to a new
state `x' ∼ ℙ_h(·|x, a, b)` according to the transition kernel. Throughout this paper, we assume for
simplicity that `𝒜₁ = 𝒜₂ = 𝒜` and that the rewards `r_h(x, a, b)` are deterministic functions of the
tuple `(x, a, b)` taking value in `[−1, 1]`."

P1 maximizes the cumulative reward and P2 minimizes it.

**Formalization Note**
1. The state space `S` is a measurable space; the common finite action set `A` (a type with
   `Fintype`, given its discrete σ-algebra by the theorems of this mission) is a type parameter.
2. Steps are 1-based, `h ∈ {1, …, H}`, as in the paper. `r` and `P` are indexed by all `h : ℕ`;
   their values outside `[1, H]` are never used.
3. `P h` is a Markov kernel from `S × A × A` to `S`; the reward is jointly measurable and takes
   values in `[−1, 1]` at every step (the standing assumption of p.6). -/
structure MarkovGame (S A : Type*) [MeasurableSpace S] [MeasurableSpace A] where
  /-- The horizon `H` (number of steps per episode). -/
  H : ℕ
  /-- The reward `r_h(x, a, b)` received when P1 plays `a` and P2 plays `b` in state `x` at step
  `h`. -/
  r : ℕ → S → A → A → ℝ
  /-- The transition kernel `ℙ_h(· | x, a, b)`. -/
  P : ℕ → Kernel (S × A × A) S
  P_markov : ∀ h, IsMarkovKernel (P h)
  r_measurable : ∀ h, Measurable (fun z : S × A × A => r h z.1 z.2.1 z.2.2)
  r_bound : ∀ h x a b, |r h x a b| ≤ 1

end LinearZeroSumMG


