-- Prove2me | Definitions.Def_AccelVI_LowerBound_Setting
-- name    : AccelVI_LowerBound_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:21.676128+00:00
-- url     : https://prove2.me/theorems/d47f40c5-c7c6-496f-bc36-eb439d6bf931
-- title:
--   §2, (2.1), §6.2, Figure 1 — finite MDP, Bellman operator T, the n-state chain MDP, first-order iterates
-- statement:
--   This file fixes the objects of the lower bound of Goyal and Grand-Clément.
--
--   1. **MDP.** A finite Markov decision process with state set $S$ ($|S| = n$), action set $A$, transition kernel $P$ with entries $P_{iaj}$ (the probability of moving from state $i$ to state $j$ under action $a$), rewards $r_{ia}$ and discount factor $\lambda$. The initial distribution $p_0$ of the paper is omitted, since no result here uses it. The MDP is **valid** when each $P_{ia}$ is a probability vector and $0 < \lambda < 1$.
--
--   2. **Bellman operator** (2.1): for $v \in \mathbb{R}^n$,
--   $$
--   T(v)_i = \max_{a \in A} \Big\{ r_{ia} + \lambda \sum_{j} P_{iaj} v_j \Big\}, \qquad i \in S.
--   $$
--
--   3. **The chain of Figure 1.** For $n \ge 1$ and $\lambda$, the MDP with $n$ states and one action in which state 1 is absorbing with reward $r_1 = 1$, and every state $i \ge 2$ moves deterministically to $i - 1$ with reward $0$.
--
--   4. **First-order iterates** (p. 12): a sequence $(v_s)_{s \ge 0}$ in $\mathbb{R}^n$ is first-order for an operator $T$ when
--   $$
--   v_0 = 0, \qquad v_{s+1} \in \operatorname{span}\{v_0, \dots, v_s, T(v_0), \dots, T(v_s)\}, \quad s \ge 0 .
--   $$
--
--   These are the objects in terms of which Theorem 6.3 states that no first-order method can approach the fixed point of $T$ faster than $\lambda^s$ on the chain.
--
--   **Formalization Note.** The data $(P, r, \lambda)$ is a plain structure; validity is the separate predicate `MDP.Valid`, whose kernel condition is the published `IsTransitionKernel`, and $T$ is the published `BellmanOperator` (a `Finset.sup'` over the nonempty finite action set) applied to $(P, r, \lambda)$. The chain uses 0-based states `Fin n`: the paper's state $i$ is `⟨i − 1, _⟩`, so state 0 is the absorbing one and state $k \ge 1$ moves to $k - 1$. The action set is `Unit`. "span" is the real linear span `Submodule.span ℝ` (the page does not say affine or convex); both lists run up to index $s$ inclusive.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, pp. 3, 12, §2 (2.1), §6.2 first-order iterates, Theorem 6.3 proof and Figure 1

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_BellmanOperator

namespace AccelVI.LowerBound

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

/-- §2, p. 3: the data (P, r, λ) of an MDP (S, A, P, r, p₀, λ); p₀ is omitted (no planned result uses it). -/
structure MDP (S A : Type*) where
  P : S → A → S → ℝ
  r : S → A → ℝ
  lam : ℝ

/-- §2: P_ia is a probability distribution over next states (the published
`FoundationsML.ReinforcementLearning.IsTransitionKernel`), and λ ∈ (0, 1). -/
def MDP.Valid (M : MDP S A) : Prop :=
  FoundationsML.ReinforcementLearning.IsTransitionKernel M.P ∧ 0 < M.lam ∧ M.lam < 1

/-- (2.1): T(v)_i = max_{a ∈ A} {r_ia + λ P_iaᵀ v}, the published
`FoundationsML.ReinforcementLearning.BellmanOperator` (a `Finset.sup'` over the nonempty action set). -/
noncomputable def bellman [Nonempty A] (M : MDP S A) (v : S → ℝ) : S → ℝ :=
  FoundationsML.ReinforcementLearning.BellmanOperator Finset.univ_nonempty M.P M.r M.lam v

/-- Figure 1, p. 12, with 0-based states: the paper's state i ∈ {1, …, n} is `⟨i − 1, _⟩ : Fin n`.
One action; state 0 (the paper's state 1) is absorbing with reward 1; every other state k moves
deterministically to k − 1 with reward 0. -/
def chainMDP (n : ℕ) (lam : ℝ) : MDP (Fin n) Unit where
  P i _ j := if (i : ℕ) = 0 then (if (j : ℕ) = 0 then 1 else 0) else (if (j : ℕ) + 1 = (i : ℕ) then 1 else 0)
  r i _ := if (i : ℕ) = 0 then 1 else 0
  lam := lam

/-- §6.2, p. 12: a first-order sequence of iterates for an operator T:
v₀ = 0 and v_{s+1} ∈ span_ℝ {v₀, …, v_s, T(v₀), …, T(v_s)} for all s ≥ 0. -/
def IsFirstOrder {n : ℕ} (T : (Fin n → ℝ) → (Fin n → ℝ)) (v : ℕ → Fin n → ℝ) : Prop :=
  v 0 = 0 ∧ ∀ s, v (s + 1) ∈ Submodule.span ℝ
    (Set.range (fun t : Fin (s + 1) => v t) ∪ Set.range (fun t : Fin (s + 1) => T (v t)))

end AccelVI.LowerBound


