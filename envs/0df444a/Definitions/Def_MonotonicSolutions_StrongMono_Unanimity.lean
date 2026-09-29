-- Prove2me | Definitions.Def_MonotonicSolutions_StrongMono_Unanimity
-- name    : MonotonicSolutions_StrongMono_Unanimity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:03:22.337097+00:00
-- url     : https://prove2.me/theorems/9f018480-bbed-4f21-b69a-37d3601075ef
-- title:
--   Primitive (unanimity) game $v_R$, Eq. (9)
-- statement:
--   Let $N = \{1, \dots, n\}$ and let $R \subseteq N$ be a coalition. The **primitive game** (unanimity game) $v_R$ is
--   $$v_R(S) = \begin{cases} 1 & \text{if } R \subseteq S,\\ 0 & \text{if } R \not\subseteq S. \end{cases}$$
--   For a real $c_R$, the game $c_R v_R$ gives the value $c_R$ to every coalition containing $R$ and $0$ to every other coalition.
--
--   Primitive games with $R \neq \emptyset$ form a basis of the space of games (Shapley), and Young's proof of Theorem 2 proceeds by induction on the number of primitive games needed to write a game.
--
--   **Formalization Note** `unanimity R S` is the bare function $v_R(S)$; it is defined for every $R$, but the paper (and every statement of the mission) uses it only for nonempty $R$, for which $v_R(\emptyset) = 0$.
-- source:
--   Young, Monotonic Solutions of Cooperative Games, Int. J. Game Theory 14 (1985), p. 70, Eq. (9)

import Mathlib

namespace MonotonicSolutions.StrongMono

/-- The primitive (unanimity) game `v_R` of Young (1985, p. 70, Eq. (9)): `v_R(S) = 1` if
`R ⊆ S` and `0` otherwise. In Eq. (9) it is used only for nonempty `R`. -/
def unanimity {n : ℕ} (R S : Finset (Fin n)) : ℝ := if R ⊆ S then 1 else 0

end MonotonicSolutions.StrongMono


