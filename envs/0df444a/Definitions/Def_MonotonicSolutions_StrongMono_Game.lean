-- Prove2me | Definitions.Def_MonotonicSolutions_StrongMono_Game
-- name    : MonotonicSolutions_StrongMono_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:02:27.993607+00:00
-- url     : https://prove2.me/theorems/0a8bfd3a-6c26-42bb-b0cf-e91954024b3a
-- title:
--   Cooperative game with $v(\emptyset)=0$, allocation procedure, and marginal contribution $v^i(S)$, Eq. (3)
-- statement:
--   Fix a number of players $n$ and the player set $N = \{1, 2, \dots, n\}$.
--
--   A **cooperative game** on $N$ is a real-valued function $v$ defined on all coalitions $S \subseteq N$ such that
--   $$v(\emptyset) = 0.$$
--   No further condition is imposed; in particular the game need not be superadditive.
--
--   An **allocation procedure** is a map $\varphi$ that assigns to every cooperative game $v$ on $N$ an allocation $\varphi(v) = (\varphi_1(v), \dots, \varphi_n(v)) \in \mathbb{R}^N$ which is *efficient*:
--   $$\sum_{i \in N} \varphi_i(v) = v(N).$$
--
--   The **marginal contribution** of player $i$ to the coalition $S$ (the *derivative* of $v$ with respect to $i$) is
--   $$v^i(S) = \begin{cases} v(S) - v(S \setminus \{i\}) & \text{if } i \in S,\\ v(S \cup \{i\}) - v(S) & \text{if } i \notin S. \end{cases}$$
--   It is defined for every coalition $S$, whether or not it contains $i$.
--
--   These are the basic objects of Young's axiomatization of the Shapley value: strong monotonicity, marginality and the dummy axiom are all conditions on how $\varphi_i$ responds to the marginal contributions $v^i$.
--
--   **Formalization Note** Players are `Fin n`, so the paper's player $k$ is the Lean index $k-1$. A game is the subtype `Game n := {v : Finset (Fin n) → ℝ // v ∅ = 0}`; the normalisation $v(\emptyset) = 0$ is part of the type. `IsAllocationProcedure φ` is the efficiency condition on a map `φ : Game n → Fin n → ℝ`. `marginal v i S` takes a bare set function, so it can also be applied to auxiliary sums of primitive games. The same `Game` and `IsAllocationProcedure` are defined in the sister mission on Theorem 1 (namespace `MonotonicSolutions.CoreRules`).
-- source:
--   Young, Monotonic Solutions of Cooperative Games, Int. J. Game Theory 14 (1985), p. 65 (cooperative game), p. 66 (allocation procedure, efficiency), p. 67, Eq. (3) (marginal contribution)

import Mathlib

namespace MonotonicSolutions.StrongMono

/-- A cooperative game on the player set `N = Fin n` (Young 1985, p. 65): a real-valued
function on coalitions `S ⊆ N` with `v ∅ = 0`. Superadditivity is not required.
The paper's player `k ∈ {1, …, n}` is the Lean index one below `k`. -/
def Game (n : ℕ) : Type := {v : Finset (Fin n) → ℝ // v ∅ = 0}

/-- An allocation procedure (Young 1985, p. 66): a map `φ` assigning to every game `v` on `N`
an allocation `φ v : Fin n → ℝ` that is efficient, `∑_{i ∈ N} (φ v) i = v N`. -/
def IsAllocationProcedure {n : ℕ} (φ : Game n → Fin n → ℝ) : Prop :=
  ∀ v : Game n, ∑ i, φ v i = v.1 Finset.univ

/-- The marginal contribution `v^i(S)` of player `i` to the coalition `S`, Eq. (3) of
Young (1985, p. 67): `v S - v (S - i)` if `i ∈ S`, and `v (S + i) - v S` if `i ∉ S`.
It is defined for every coalition `S`. -/
def marginal {n : ℕ} (v : Finset (Fin n) → ℝ) (i : Fin n) (S : Finset (Fin n)) : ℝ :=
  if i ∈ S then v S - v (S.erase i) else v (insert i S) - v S

end MonotonicSolutions.StrongMono


