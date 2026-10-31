-- Prove2me | Definitions.Def_CombOpt_ShortestPath_FordState
-- name    : CombOpt_ShortestPath_FordState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:08.55873+00:00
-- url     : https://prove2.me/theorems/2b61623c-5068-4776-a8ca-4be39be777f3
-- title:
--   State $(y,p)$ of Ford's Algorithm
-- statement:
--   A **state** of Ford's Algorithm is a pair $(y,p)$: labels $y_v\in\mathbb R\cup\{\infty\}$ and predecessors $p(v)$ for $v\in V$. Here $y_v=\infty$ means that no dipath to $v$ is known yet, with the conventions $a+\infty=\infty$ and $a<\infty$ for every real $a$.
--
--   **Formalization Note** The labels take values in `WithTop ℝ`, whose top element is the book's $\infty$ and which satisfies exactly these two rules.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.2, pp. 21–22 (PDF pp. 30–31), Ford's Algorithm

import Mathlib
import Definitions.Def_CombOpt_ShortestPath_FordPred

namespace CombOpt.ShortestPath

/-- **A state of Ford's Algorithm.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.2, pp. 21–22 (PDF pp. 30–31): the algorithm maintains labels y_v ∈ ℝ ∪ {∞} ("y_v = ∞
simply means that we do not yet know a dipath to v, and ∞ satisfies a + ∞ = ∞ and a < ∞ for all
real numbers a") and predecessors p(v).

**Formalization Note.** `y v : WithTop ℝ`, with `⊤` the book's `∞`; in `WithTop ℝ`,
`a + ⊤ = ⊤` and `a < ⊤` for real `a`, exactly the book's rules. `p v : FordPred E`. -/
structure FordState (V E : Type*) where
  /-- The labels `y_v`. -/
  y : V → WithTop ℝ
  /-- The predecessors `p(v)`. -/
  p : V → FordPred E

end CombOpt.ShortestPath


