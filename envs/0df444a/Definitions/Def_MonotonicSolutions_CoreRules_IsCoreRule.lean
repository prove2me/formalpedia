-- Prove2me | Definitions.Def_MonotonicSolutions_CoreRules_IsCoreRule
-- name    : MonotonicSolutions_CoreRules_IsCoreRule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:56:43.477397+00:00
-- url     : https://prove2.me/theorems/f32cad33-b73f-4fe9-b467-db6b5bdc7463
-- title:
--   Core allocation rule: $\varphi(v)$ lies in the core whenever the core is nonempty
-- statement:
--   Let $v$ be a cooperative game on $N = \{1, \dots, n\}$ (with $v(\emptyset) = 0$). Its **core** is the set of allocations
--   $$C(v) = \Big\{x \in \mathbb{R}^N : \sum_{i \in S} x_i \ge v(S) \text{ for all } S \subseteq N,\ \sum_{i \in N} x_i = v(N)\Big\}.$$
--
--   A map $\varphi$ from games to allocations is a **core allocation rule** (a *core solution concept*) if
--   $$\varphi(v) \in C(v) \quad \text{whenever } C(v) \neq \emptyset .$$
--   Games with an empty core impose no constraint on $\varphi(v)$.
--
--   The nucleolus is the standard example of a core allocation rule. Theorem 1 of the paper shows that, for five or more players, no such rule is coalitionally monotonic.
--
--   **Formalization Note** The core is the published definition `Supermodularity.Cooperative.Core Finset.univ v.1`, whose defining conditions are exactly those above with $U = N$. The nonemptiness guard is essential: since some games have an empty core, the unconditional requirement $\varphi(v) \in C(v)$ for all $v$ could not be met by any map.
-- source:
--   Young, Monotonic Solutions of Cooperative Games, Int. J. Game Theory 14 (1985), p. 68 (core solution concept, Gillies [1959]); p. 69, Theorem 1 ("core allocation rule")

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_MonotonicSolutions_CoreRules_Game

namespace MonotonicSolutions.CoreRules

/-- A core allocation rule (Young 1985, p. 68): whenever the core
`{x | ∑_{i ∈ N} x i = v N ∧ ∀ S, v S ≤ ∑_{i ∈ S} x i}` of the game `v` is nonempty,
`φ v` lies in it. Games with an empty core are unconstrained. -/
def IsCoreRule {n : ℕ} (φ : Game n → Fin n → ℝ) : Prop :=
  ∀ v : Game n, (Supermodularity.Cooperative.Core Finset.univ v.1).Nonempty →
    φ v ∈ Supermodularity.Cooperative.Core Finset.univ v.1

end MonotonicSolutions.CoreRules


