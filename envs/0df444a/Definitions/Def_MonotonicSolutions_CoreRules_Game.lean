-- Prove2me | Definitions.Def_MonotonicSolutions_CoreRules_Game
-- name    : MonotonicSolutions_CoreRules_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:56:05.508268+00:00
-- url     : https://prove2.me/theorems/8b358255-d52e-4aba-8766-cd60d8ff3ded
-- title:
--   Cooperative game on $N=\{1,\dots,n\}$ with $v(\emptyset)=0$; efficient allocation procedure
-- statement:
--   Fix a number of players $n$ and the player set $N = \{1, 2, \dots, n\}$.
--
--   A **cooperative game** on $N$ is a real-valued function $v$ defined on all coalitions $S \subseteq N$ such that
--   $$v(\emptyset) = 0.$$
--   The number $v(S)$ is the *value* of the coalition $S$. No further condition is imposed; in particular the game need not be superadditive.
--
--   An **allocation procedure** is a map $\varphi$ that assigns to every cooperative game $v$ on $N$ an allocation $\varphi(v) = (\varphi_1(v), \dots, \varphi_n(v)) \in \mathbb{R}^N$ which is *efficient*:
--   $$\sum_{i \in N} \varphi_i(v) = v(N).$$
--
--   These are the basic objects of Young's study of monotonic solutions: every monotonicity axiom and every solution concept in the mission is a property of such maps $\varphi$.
--
--   **Formalization Note** Players are `Fin n`, so the paper's player $k$ is the Lean index $k-1$. A game is the subtype `Game n := {v : Finset (Fin n) → ℝ // v ∅ = 0}`; the normalisation $v(\emptyset)=0$ is part of the type, so any axiom quantifying over games ranges only over normalised games. `IsAllocationProcedure φ` is the efficiency condition; a procedure is any function `Game n → Fin n → ℝ` satisfying it.
-- source:
--   Young, Monotonic Solutions of Cooperative Games, Int. J. Game Theory 14 (1985), p. 65 (cooperative game), p. 66 (allocation procedure, efficiency)

import Mathlib

namespace MonotonicSolutions.CoreRules

/-- A cooperative game on the player set `N = Fin n` (Young 1985, p. 65): a real-valued
function on coalitions `S ⊆ N` with `v ∅ = 0`. Superadditivity is not required.
The paper's player `k ∈ {1, …, n}` is the Lean index one below `k`. -/
def Game (n : ℕ) : Type := {v : Finset (Fin n) → ℝ // v ∅ = 0}

/-- An allocation procedure (Young 1985, p. 66): a map `φ` assigning to every game `v` on `N`
an allocation `φ v : Fin n → ℝ` that is efficient, `∑_{i ∈ N} (φ v) i = v N`. -/
def IsAllocationProcedure {n : ℕ} (φ : Game n → Fin n → ℝ) : Prop :=
  ∀ v : Game n, ∑ i, φ v i = v.1 Finset.univ

end MonotonicSolutions.CoreRules


