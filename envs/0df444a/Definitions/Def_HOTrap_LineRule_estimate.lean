-- Prove2me | Definitions.Def_HOTrap_LineRule_estimate
-- name    : HOTrap_LineRule_estimate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:46:57.731195+00:00
-- url     : https://prove2.me/theorems/ef6c1137-16c5-49d6-814c-b542a98680cb
-- title:
--   Estimate of a line rule
-- statement:
--   The estimate returned by a line rule with gradient oracle $g$: the rule's estimate on the answers $g(\text{node}_i)$ at its nodes.
--
--   **Formalization Note** Positions of the answer sequence past the query count hold $0$, so the objective enters only through the queried gradients.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Lemma 4.2, pp.22–23

import Mathlib
import Definitions.Def_HOTrap_LineRule

namespace HOTrap

/-- **The estimate returned by a line rule** when the gradient oracle is `g`: the rule's answers are `g`
at its `count` nodes, and `0` afterwards. Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Lemma 4.2, pp.22–23. -/
noncomputable def LineRule.estimate {d : ℕ} {Θ : Type} (R : LineRule d Θ) (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (u v : EuclideanSpace ℝ (Fin d)) (θ : Θ) : ℝ :=
  R.est u v θ (fun i => if i < R.count u v θ then g (R.node u v θ i) else 0)

end HOTrap


