-- Prove2me | Definitions.Def_KallenbergLP_Positive_Value
-- name    : KallenbergLP_Positive_Value
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T10:48:42.962977+00:00
-- url     : https://prove2.me/theorems/91fbb638-f270-4ebc-81df-9d801cb42e6d
-- title:
--   Sections 2.2 and 3.3 — total reward, TMD value and real superharmonic vectors
-- statement:
--   The expected reward at time $n+1$, starting from state $i$ under policy $R$, is
--   $$
--   v_i^{n+1}(R)=\sum_{j\in E}\sum_{a\in A(j)}\Pr_R(X_{n+1}=j,Y_{n+1}=a\mid X_1=i)\,r_{ja}.
--   $$
--   The **total reward** $v_i(R)$ is the supremum of finite cumulative rewards, and the **TMD value** is $v_i=\sup_{R\in C}v_i(R)$. With nonnegative rewards, finite cumulative rewards increase, so their supremum is precisely the book's limit and may be $+\infty$. The supremum over $C$ includes every history dependent randomized policy.
--
--   A real vector $w\in\mathbb R^E$ is **TMD superharmonic** when
--   $$
--   w_i\ge r_{ia}+\sum_{j\in E}p_{iaj}w_j\qquad(i\in E,\ a\in A(i)).
--   $$
--   This is the original real-valued definition in Definition 3.3.1. The value itself is represented in extended real numbers because Section 3.5 allows an infinite optimal reward.
--
--   **Formalization Note** `EReal` is used for total reward and value. The supremum definition of total reward is used by the positive reward theorems; for signed rewards the book instead assumes that the finite cumulative rewards have a limit.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, pp. 21–22 (PDF pp. 29–30), Section 2.2; p. 52 (PDF p. 60), Definition 3.3.1

import Definitions.Def_KallenbergLP_Positive_Policy

namespace KallenbergLP.Positive

variable {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]

/-- Expected reward at time `n + 1`, conditional on the initial state. -/
def stageReward (M : MDP N α) (R : Policy M) (i : Fin N) (n : ℕ) : ℝ :=
  ∑ j : Fin N, ∑ a ∈ M.actions j, occupancy M R i j a n * M.reward j a

/-- Total expected reward, defined as the supremum of finite partial sums.
Under nonnegative rewards this is exactly the limit in §2.2, including `+∞`. -/
noncomputable def totalReward (M : MDP N α) (R : Policy M) (i : Fin N) : EReal :=
  ⨆ n : ℕ, (↑(∑ t ∈ Finset.range n, stageReward M R i t) : EReal)

/-- Componentwise TMD value over all admissible history-dependent policies. -/
noncomputable def value (M : MDP N α) (i : Fin N) : EReal :=
  ⨆ R : Policy M, totalReward M R i

/-- Definition 3.3.1, with its original real-valued domain. -/
def IsSuperharmonic (M : MDP N α) (w : Fin N → ℝ) : Prop :=
  ∀ i (a : α), a ∈ M.actions i →
    M.reward i a + ∑ j : Fin N, M.transition i a j * w j ≤ w i

end KallenbergLP.Positive


