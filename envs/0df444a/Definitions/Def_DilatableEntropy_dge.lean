-- Prove2me | Definitions.Def_DilatableEntropy_dge
-- name    : DilatableEntropy_dge
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:53:47.686993+00:00
-- url     : https://prove2.me/theorems/5aacaeed-4da6-4804-9433-28b7a00827a7
-- title:
--   Dilatable global entropy $\tilde\varphi$ (Definition 4)
-- statement:
--   The **dilatable global entropy** is
--   $$
--   \tilde\varphi(x)=w_\varnothing x_\varnothing\log x_\varnothing+\sum_{j\in J}\sum_{a\in A_j}w_{ja}\,x_{ja}\log x_{ja}+\sum_{j\in J}\gamma_j\,x_{p_j}\log|A_j| ,
--   $$
--   with the convention $0\log 0=0$, where $\gamma_j$ and $w_\sigma$ are the weights of Definition 4.
--
--   It is a weighted negative entropy of the whole sequence-form vector, and the regularizer the mission studies.
--
--   **Formalization Note** The paper defines $\tilde\varphi$ on $Q$ and differentiates the same formula (closed-form gradient on p.11). Here the formula is a function on all of $\mathbb R^\Sigma$ using Mathlib's `Real.log` (so $0\cdot\log 0=0$); only its values on $Q$ and its derivative on the relative interior of $Q$ are used.
-- source:
--   Farina, Kroer, Sandholm, Better Regularization for Sequential Decision Spaces, arXiv:2105.12954v2, Definition 4, p.10

import Mathlib
import Definitions.Def_DilatableEntropy_weight

namespace DilatableEntropy

/-- The **dilatable global entropy** `φ̃` (Farina, Kroer, Sandholm, *Better Regularization for Sequential Decision Spaces*, arXiv:2105.12954v2, Definition 4, p.10):
`φ̃(x) = w_∅ x_∅ log x_∅ + ∑_{j ∈ J} ∑_{a ∈ A_j} w_{ja} x_{ja} log x_{ja}
  + ∑_{j ∈ J} γ_j x_{p_j} log |A_j|`.

**Formalization Note** The paper defines `φ̃` on the sequence-form polytope `Q` and
differentiates the same formula (its gradient `(1 + log x_σ) w_σ + ∑_{j ∈ C_σ} γ_j log |A_j|`,
p.11). Here the formula is defined on all of `ℝ^Σ` with Mathlib's `Real.log`, so
`0 · log 0 = 0` (the paper's convention, footnote 2, p.9); only its values on `Q` and its
derivative on the relative interior of `Q` are used. `|A_j|` is `Fintype.card (P.A j)`. -/
noncomputable def dge (P : SeqDecisionProblem) (x : Seq P → ℝ) : ℝ :=
  weight P none * x none * Real.log (x none)
    + ∑ j : P.J, ∑ a : P.A j,
        weight P (some ⟨j, a⟩) * x (some ⟨j, a⟩) * Real.log (x (some ⟨j, a⟩))
    + ∑ j : P.J, gamma P j * x (P.parent j) * Real.log (Fintype.card (P.A j))

end DilatableEntropy


