-- Prove2me | Definitions.Def_DilatableEntropy_weight
-- name    : DilatableEntropy_weight
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:52:43.90685+00:00
-- url     : https://prove2.me/theorems/d8201409-19d5-4e5c-870c-f20705320a84
-- title:
--   Weights $w_\sigma$ of the dilatable global entropy
-- statement:
--   The weights $w_\sigma$ ($\sigma\in\Sigma$) are
--   $$
--   w_\varnothing:=\gamma_\varnothing-\sum_{j\in\mathcal C_\varnothing}\gamma_j,\qquad
--   w_{ja}:=\gamma_j-\sum_{j'\in\mathcal C_{ja}}\gamma_{j'}\quad(ja\in\Sigma).
--   $$
--   So $w_\varnothing=1$ and $w_{ja}=1+\max_{a'\in A_j}\sum_{j'\in\mathcal C_{ja'}}\gamma_{j'}-\sum_{j'\in\mathcal C_{ja}}\gamma_{j'}$.
--
--   They are the coefficients of the entropy terms $x_\sigma\log x_\sigma$ in the dilatable global entropy.
-- source:
--   Farina, Kroer, Sandholm, Better Regularization for Sequential Decision Spaces, arXiv:2105.12954v2, Definition 4, p.10

import Mathlib
import Definitions.Def_DilatableEntropy_gammaRoot

namespace DilatableEntropy

/-- The weights `w_σ` (`σ ∈ Σ`) of the dilatable global entropy (Farina, Kroer, Sandholm, *Better Regularization for Sequential Decision Spaces*, arXiv:2105.12954v2, Definition 4, p.10):
`w_∅ := γ_∅ − ∑_{j ∈ C_∅} γ_j` and `w_{ja} := γ_j − ∑_{j' ∈ C_{ja}} γ_{j'}`. -/
noncomputable def weight (P : SeqDecisionProblem) (σ : Seq P) : ℝ :=
  (match σ with
    | none => gammaRoot P
    | some ⟨j, _⟩ => gamma P j) - ∑ j' ∈ children P σ, gamma P j'

end DilatableEntropy


