-- Prove2me | Definitions.Def_CombOpt_ShortestPath_Digraph_IsIncorrect
-- name    : CombOpt_ShortestPath_Digraph_IsIncorrect
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:54.814122+00:00
-- url     : https://prove2.me/theorems/51ee20cc-8dfc-418d-bffb-d08ffcee858f
-- title:
--   Incorrect arc
-- statement:
--   With labels $y_v\in\mathbb R\cup\{\infty\}$, an arc $vw$ is **incorrect** if it violates (2.12), that is,
--   $$y_v+c_{vw}<y_w.$$
--   By the rules $a+\infty=\infty$ and $a<\infty$, an arc whose tail has label $\infty$ is never incorrect, and an arc from a node with finite label to a node with label $\infty$ always is.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.2, p. 22 (PDF p. 31), incorrect arcs

import Mathlib
import Definitions.Def_CombOpt_ShortestPath_Digraph

namespace CombOpt.ShortestPath

/-- **An incorrect arc.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.2, p. 22 (PDF p. 31): "Let us call an arc vw violating (2.12) *incorrect*", where (2.12)
is y_v + c_vw ≥ y_w and the labels may be ∞ (p. 21: "a + ∞ = ∞ and a < ∞ for all real numbers a").

`G.IsIncorrect c y e` says `y (tail e) + c e < y (head e)` in `WithTop ℝ`.

**Formalization Note.** With `⊤ = ∞`, an arc whose tail has label `∞` is never incorrect
(`⊤ + a = ⊤` is not `< ` anything), and an arc from a finite label to an `∞` label always
is. -/
def Digraph.IsIncorrect {V E : Type*} (G : Digraph V E) (c : E → ℝ) (y : V → WithTop ℝ)
    (e : E) : Prop :=
  y (G.tail e) + ((c e : ℝ) : WithTop ℝ) < y (G.head e)

end CombOpt.ShortestPath


