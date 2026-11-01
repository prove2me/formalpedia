-- Prove2me | Definitions.Def_DilatableEntropy_gammaRoot
-- name    : DilatableEntropy_gammaRoot
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:51:39.869289+00:00
-- url     : https://prove2.me/theorems/5b382ba7-25c0-4f7b-ada8-58eb2e766844
-- title:
--   Root weight $\gamma_\varnothing$, (8)
-- statement:
--   The weight of the empty sequence is
--   $$
--   \gamma_\varnothing:=1+\sum_{j\in\mathcal C_\varnothing}\gamma_j ,
--   $$
--   where $\mathcal C_\varnothing$ is the set of root decision points and $\gamma_j$ are the weights of (8).
--
--   It is the coefficient of $x_\varnothing\log x_\varnothing$ in the dilated entropy $\varphi$.
-- source:
--   Farina, Kroer, Sandholm, Better Regularization for Sequential Decision Spaces, arXiv:2105.12954v2, Definition 4, eq. (8), p.10

import Mathlib
import Definitions.Def_DilatableEntropy_gamma

namespace DilatableEntropy

/-- The root weight `γ_∅ := 1 + ∑_{j ∈ C_∅} γ_j` (Farina, Kroer, Sandholm, *Better Regularization for Sequential Decision Spaces*, arXiv:2105.12954v2, Definition 4, eq. (8), p.10), where
`C_∅` is the set of root decision points. -/
noncomputable def gammaRoot (P : SeqDecisionProblem) : ℝ :=
  1 + ∑ j ∈ children P none, gamma P j

end DilatableEntropy


