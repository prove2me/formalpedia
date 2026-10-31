-- Prove2me | Definitions.Def_ContPatrol_MetricGraph_AlphaLeGenGirth
-- name    : ContPatrol_MetricGraph_AlphaLeGenGirth
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:12:47.316009+00:00
-- url     : https://prove2.me/theorems/3f136804-bc07-449f-bd01-880bc2ef63b6
-- title:
--   Definition 6: the condition $\alpha\le g^*$ on the generalized girth
-- statement:
--   The **generalized girth** $g^*$ of a network treats a leaf arc of length $L$ as a circuit of length $2L$:
--   $$g^*=\min\Big(g,\;2\min_{\text{leaf arcs }a}\lambda(a)\Big).$$
--
--   The condition $\alpha\le g^*$ says that every circuit has length at least $\alpha$ and every leaf arc has length at least $\alpha/2$.
--
--   It is the hypothesis under which the paper solves the game on every network (Theorem 6).
--
--   **Formalization Note** A minimum over an empty family is $\infty$; the corresponding half of the condition is then vacuous.
-- source:
--   Alpern, Bui, Lidbetter, Papadaki, Continuous Patrolling Games, arXiv:2008.07369v2, Definition 6, p.15

import Mathlib
import Definitions.Def_ContPatrol_MetricGraph_AlphaLeGirth
import Definitions.Def_ContPatrol_MetricGraph_leafArcLength

namespace ContPatrol

namespace MetricGraph

variable {V E : Type}

/-- **α ≤ g\*, the generalized girth (Definition 6).**
Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, Definition 6,
p.15: "We define the generalized girth g∗ of a network Q by considering a leaf arc of length L to
be a circuit of length 2L. So g∗ is the smaller between (1) the shortest circuit length of Q and
(2) twice the length of the shortest leaf arc."

`G.AlphaLeGenGirth α` says `α ≤ g*`: every circuit has length at least `α`, and every leaf arc
has length at least `α/2`.

**Formalization Note.** `α ≤ min(g, 2·min_leaf λ(leaf arc))` is the conjunction of the two
conditions; a minimum over an empty family (no circuit, or no leaf) is `∞`, and the corresponding
conjunct is then vacuous, as it should be. -/
def AlphaLeGenGirth [Fintype E] [DecidableEq V] (G : MetricGraph V E) (α : ℝ) : Prop :=
  G.AlphaLeGirth α ∧ ∀ v, G.deg v = 1 → α ≤ 2 * G.leafArcLength v

end MetricGraph

end ContPatrol


