-- Prove2me | Definitions.Def_MonotonicSolutions_CoreRules_IsCoalitionallyMonotonic
-- name    : MonotonicSolutions_CoreRules_IsCoalitionallyMonotonic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:57:15.896682+00:00
-- url     : https://prove2.me/theorems/4ab63fd2-5b4f-4ea8-a986-25a7eb02cbc0
-- title:
--   Coalitional monotonicity, Eq. (4)
-- statement:
--   Let $\varphi$ assign to each cooperative game $v$ on $N = \{1, \dots, n\}$ an allocation $\varphi(v) \in \mathbb{R}^N$. The map $\varphi$ is **coalitionally monotonic** if an increase in the value of one coalition, all other values being unchanged, never decreases the allocation of any member of that coalition: for all games $v, w$ and every coalition $T \subseteq N$,
--   $$v(T) \ge w(T) \ \text{ and } \ v(S) = w(S) \text{ for all } S \ne T \quad \Longrightarrow \quad \varphi_i(v) \ge \varphi_i(w) \text{ for all } i \in T.$$
--
--   The coalition $T$ ranges over all coalitions, including the grand coalition $N$ itself.
--
--   **Formalization Note** The games $v, w$ range over `Game n`, i.e. functions with $v(\emptyset) = 0$. The definition applies to any map `Game n → Fin n → ℝ`; efficiency is a separate condition.
-- source:
--   Young, Monotonic Solutions of Cooperative Games, Int. J. Game Theory 14 (1985), p. 68, Eq. (4)

import Mathlib
import Definitions.Def_MonotonicSolutions_CoreRules_Game

namespace MonotonicSolutions.CoreRules

/-- Coalitional monotonicity, Young 1985, p. 68, Eq. (4): if `v T ≥ w T` for some coalition `T`
(any `T ⊆ N`, including `N` itself) and `v S = w S` for every `S ≠ T`, then
`φ v i ≥ φ w i` for every `i ∈ T`. -/
def IsCoalitionallyMonotonic {n : ℕ} (φ : Game n → Fin n → ℝ) : Prop :=
  ∀ (v w : Game n) (T : Finset (Fin n)), w.1 T ≤ v.1 T → (∀ S, S ≠ T → v.1 S = w.1 S) →
    ∀ i ∈ T, φ w i ≤ φ v i

end MonotonicSolutions.CoreRules


