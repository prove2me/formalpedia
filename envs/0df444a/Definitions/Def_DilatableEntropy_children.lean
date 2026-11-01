-- Prove2me | Definitions.Def_DilatableEntropy_children
-- name    : DilatableEntropy_children
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:48.579006+00:00
-- url     : https://prove2.me/theorems/5acdd7e6-3a4a-41eb-a987-34ed763f6970
-- title:
--   Decision points following a sequence, $\mathcal C_\sigma$
-- statement:
--   For a sequence $\sigma\in\Sigma$, the set of decision points that immediately follow it is
--   $$
--   \mathcal C_\sigma:=\{\,j\in J : p_j=\sigma\,\}.
--   $$
--   For $\sigma=ja$ this is the set $\mathcal C_{ja}$ of next decision points the player may face after taking action $a$ at $j$; $\mathcal C_\varnothing$ is the set of root decision points.
--
--   The weights of the dilatable global entropy are defined by recursion over these sets.
-- source:
--   Farina, Kroer, Sandholm, Better Regularization for Sequential Decision Spaces, arXiv:2105.12954v2, §4, p.7 (C_ja), pp.9–10 (C_∅)

import Mathlib
import Definitions.Def_DilatableEntropy_SeqDecisionProblem

namespace DilatableEntropy

/-- The decision points that follow a sequence `σ` (Farina, Kroer, Sandholm, *Better Regularization for Sequential Decision Spaces*, arXiv:2105.12954v2, §4, p.7):
`C_σ := {j ∈ J : p_j = σ}`. For `σ = ja` this is the paper's `C_{ja}`, the set of next
decision points the player may face after taking action `a` at `j`; `C_∅` is the set of root
decision points (pp.9–10). -/
def children (P : SeqDecisionProblem) (σ : Seq P) : Finset P.J :=
  Finset.univ.filter (fun j => P.parent j = σ)

end DilatableEntropy


