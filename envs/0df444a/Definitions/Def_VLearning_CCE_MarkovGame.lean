-- Prove2me | Definitions.Def_VLearning_CCE_MarkovGame
-- name    : VLearning_CCE_MarkovGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:13.21991+00:00
-- url     : https://prove2.me/theorems/9ffc4d9a-bbed-4dca-9fbe-537ee7b37869
-- title:
--   §2, p. 4 — tabular episodic m-player general-sum Markov game MG(H, S, {A_i}, ℙ, {r_i}) and its standing assumptions
-- statement:
--   A **tabular episodic Markov game** with $m$ players is a tuple $\mathrm{MG}(H,\mathcal S,\{\mathcal A_i\}_{i=1}^m,\mathbb P,\{r_i\}_{i=1}^m)$:
--
--   1. a finite state space $\mathcal S$ with $|\mathcal S| = S$, and an episode length $H$;
--   2. for each player $i$ a finite action set $\mathcal A_i$ with $|\mathcal A_i| = A_i$; a joint action is $\boldsymbol a = (a_1,\dots,a_m) \in \mathcal A = \mathcal A_1\times\cdots\times\mathcal A_m$;
--   3. transition kernels $\mathbb P_h(\cdot\mid s,\boldsymbol a)$, the law of the next state when the joint action $\boldsymbol a$ is taken at state $s$ at step $h$;
--   4. deterministic rewards $r_{i,h}(s,\boldsymbol a)$ of player $i$;
--   5. a fixed initial state $s_1$.
--
--   The **standing assumptions** of the paper are bundled in the predicate `Standing`: there is at least one player, one state, one step and one action per player; every $\mathbb P_h(\cdot\mid s,\boldsymbol a)$ is a probability vector on $\mathcal S$; and every reward lies in $[0,1]$. The maximal action count $A = \max_{j\in[m]} A_j$ is also defined here.
--
--   This is the game model on which V-learning and its coarse-correlated-equilibrium guarantee are stated.
--
--   **Formalization Note** States are `Fin S`, players `Fin m`, player $j$'s actions `Fin (A j)`, and steps `Fin H` are 0-based: the paper's step $h\in[H]$ is `h.val + 1`.
-- source:
--   Jin, Liu, Wang & Yu, V-Learning—A Simple, Efficient, Decentralized Algorithm for Multiagent RL, arXiv:2110.14555v1, p. 4, §2 (model); p. 10 (A = max_j A_j)

import Mathlib

namespace VLearning.CCE

/-- A tabular episodic `m`-player Markov game `MG(H, 𝒮, {𝒜_i}, ℙ, {r_i})` (Jin–Liu–Wang–Yu, §2, p. 4).

* States are `Fin S`, players `Fin m`, player `j`'s actions `Fin (A j)`, and a joint action is
  an element of `(j : Fin m) → Fin (A j)`.
* Steps are `Fin H`, **0-based**: the paper's step `h ∈ [H]` is `h.val + 1`.
* `P h s a s'` is the probability `ℙ_h(s' | s, a)` of moving to `s'` after joint action `a`
  is taken at state `s` at step `h`.
* `r j h s a` is the deterministic reward `r_{j,h}(s, a)` of player `j`.
* `s1` is the fixed initial state. -/
structure Game where
  /-- number of players -/
  m : ℕ
  /-- number of states -/
  S : ℕ
  /-- episode length -/
  H : ℕ
  /-- number of actions of each player -/
  A : Fin m → ℕ
  /-- transition probabilities `ℙ_h(s' | s, a)` -/
  P : Fin H → Fin S → ((j : Fin m) → Fin (A j)) → Fin S → ℝ
  /-- rewards `r_{j,h}(s, a)` -/
  r : Fin m → Fin H → Fin S → ((j : Fin m) → Fin (A j)) → ℝ
  /-- fixed initial state `s_1` -/
  s1 : Fin S

namespace Game

/-- Joint actions `𝒜 = 𝒜_1 × ⋯ × 𝒜_m`. -/
abbrev JointAct (G : Game) : Type := (j : Fin G.m) → Fin (G.A j)

/-- `A = max_{j ∈ [m]} A_j` (p. 10). -/
def Amax (G : Game) : ℕ := Finset.univ.sup G.A

/-- The standing assumptions of §2 (p. 4): at least one player, state, step and action per
player; every `ℙ_h(· | s, a)` is a probability vector on the states; every reward lies in
`[0, 1]`. -/
structure Standing (G : Game) : Prop where
  m_pos : 0 < G.m
  S_pos : 0 < G.S
  H_pos : 0 < G.H
  A_pos : ∀ j, 0 < G.A j
  P_nonneg : ∀ h s a s', 0 ≤ G.P h s a s'
  P_sum : ∀ h s a, ∑ s', G.P h s a s' = 1
  r_mem : ∀ j h s a, G.r j h s a ∈ Set.Icc (0 : ℝ) 1

end Game

end VLearning.CCE


