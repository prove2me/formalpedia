-- Prove2me | Definitions.Def_KingDiagonal_weightMatrix
-- name    : KingDiagonal_weightMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:15:21.548984+00:00
-- url     : https://prove2.me/theorems/4d8b9019-a250-4062-a4f9-4d96988e83ac
-- title:
--   The weight matrix $A_{ij} = (\alpha_i\alpha_j)^{1/2}$
-- statement:
--   Let $\rho$ be a matrix on $\mathbb C^n\otimes\mathbb C^k$ with block traces $\alpha_i = \operatorname{Tr}(\rho)_{ii}$. Define the $n\times n$ matrix $A$ by
--
--   $$
--   A_{ij} = (\alpha_i\alpha_j)^{1/2}.
--   $$
--
--   For a state, $A = \sqrt{\alpha}\sqrt{\alpha}^{\mathsf T}$ is a rank-one positive semidefinite matrix with trace $\sum_i\alpha_i = 1$, i.e. a state on $\mathbb C^n$; the diagonal map $\Phi$ acts on $\rho$ only through $\Phi(A)$.
--
--   **Formalization Note** The square root is `Real.sqrt`; it is applied to $\alpha_i\alpha_j \ge 0$ for states.
-- source:
--   King, An application of a matrix inequality in quantum information theory, arXiv:quant-ph/0412046v1, p.4, sentence after eq. (11)

import Mathlib
import Definitions.Def_KingDiagonal_alpha

namespace KingDiagonal

/-- King, arXiv:quant-ph/0412046v1, p.4 (after (11)): the `n × n` matrix `A` with entries
`A_{ij} = (α_i α_j)^{1/2}`, where `α_i = Tr (ρ)_{ii}` is (10).

**Formalization Note.** `Real.sqrt` is used for the power `1/2`; for a state all `α_i ≥ 0`, so
this is the page's value. -/
noncomputable def weightMatrix {n k : Type*} [Fintype k] (ρ : Matrix (n × k) (n × k) ℂ) :
    Matrix n n ℂ :=
  Matrix.of fun i j => ((Real.sqrt (alpha ρ i * alpha ρ j) : ℝ) : ℂ)

end KingDiagonal


