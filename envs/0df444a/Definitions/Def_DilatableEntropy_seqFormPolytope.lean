-- Prove2me | Definitions.Def_DilatableEntropy_seqFormPolytope
-- name    : DilatableEntropy_seqFormPolytope
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:59.62979+00:00
-- url     : https://prove2.me/theorems/4a195007-0ece-49d7-8a4c-8e1f56aac919
-- title:
--   Sequence-form polytope $Q$
-- statement:
--   The **sequence-form polytope** of a sequential decision problem is
--   $$
--   Q:=\Big\{x\in\mathbb R^{\Sigma}_{\ge 0} :\ x_\varnothing=1,\ \ \sum_{a\in A_j}x_{ja}=x_{p_j}\ \ \forall j\in J\Big\}.
--   $$
--   A point of $Q$ is a strategy in sequence form: $x_{ja}$ is the product of the probabilities of all actions on the path from the root to action $a$ at $j$, included.
--
--   It is the decision space of each player in the bilinear saddle-point formulation of a two-player zero-sum extensive-form game.
-- source:
--   Farina, Kroer, Sandholm, Better Regularization for Sequential Decision Spaces, arXiv:2105.12954v2, §4, eq. (4), pp.7–8

import Mathlib
import Definitions.Def_DilatableEntropy_SeqDecisionProblem

namespace DilatableEntropy

/-- The **sequence-form polytope** `Q` of a sequential decision problem (Farina, Kroer, Sandholm, *Better Regularization for Sequential Decision Spaces*, arXiv:2105.12954v2, §4, eq. (4),
pp.7–8): the set of vectors `x ∈ ℝ^{|Σ|}_{≥0}` with
`x_∅ = 1` and `∑_{a ∈ A_j} x_{ja} = x_{p_j}` for every `j ∈ J`. -/
def seqFormPolytope (P : SeqDecisionProblem) : Set (Seq P → ℝ) :=
  {x | (∀ σ, 0 ≤ x σ) ∧ x none = 1 ∧ ∀ j : P.J, ∑ a : P.A j, x (some ⟨j, a⟩) = x (P.parent j)}

end DilatableEntropy


