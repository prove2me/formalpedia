-- Prove2me | Definitions.Def_WhitneyMatroid_Components_IsComponent
-- name    : WhitneyMatroid_Components_IsComponent
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T04:28:47.711623+00:00
-- url     : https://prove2.me/theorems/e8f785c5-044f-450f-9db9-6b8a2bef100c
-- title:
--   Components of a matroid (§10)
-- statement:
--   Let $M$ be a matroid on a ground set $E$ with rank function $r$. A **component** of $M$ is a maximal non-separable part of $M$: a nonempty set $K\subseteq E$ which is non-separable (in the sense of §10, (10.1)) and such that no non-separable set $L\subseteq E$ strictly contains $K$:
--
--   $$
--   K\neq\emptyset,\qquad K \text{ non-separable},\qquad \bigl(L \text{ non-separable},\ K\subseteq L\bigr)\ \Longrightarrow\ L=K .
--   $$
--
--   Components are the pieces into which a matroid decomposes (Theorem 15); in the matroid of a graph they correspond to the blocks (2-connected pieces) of the graph, and Whitney's Theorem 19 characterizes them through circuits.
--
--   **Formalization Note** Components are defined through the rank condition, not through circuits. The set $K$ is required to be nonempty: the empty set is vacuously non-separable, and on a matroid with no elements it would otherwise be a (maximal) non-separable part; Whitney's components are always nonempty.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 518, §10

import Mathlib
import Definitions.Def_WhitneyMatroid_Components_IsSeparable

namespace WhitneyMatroid.Components

/-- Whitney §10: a *component* of `M` is a maximal non-separable part of `M`: a nonempty
non-separable subset `K ⊆ M.E` such that no strictly larger subset of `M.E` is non-separable. -/
def IsComponent {α : Type*} (M : Matroid α) (K : Set α) : Prop :=
  K.Nonempty ∧ IsNonSeparable M K ∧ ∀ L : Set α, IsNonSeparable M L → K ⊆ L → L = K

end WhitneyMatroid.Components


