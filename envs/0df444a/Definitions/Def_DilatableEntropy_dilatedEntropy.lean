-- Prove2me | Definitions.Def_DilatableEntropy_dilatedEntropy
-- name    : DilatableEntropy_dilatedEntropy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:52:49.686023+00:00
-- url     : https://prove2.me/theorems/7cdd9434-7473-4f0e-8d4e-779b2f63752b
-- title:
--   Dilated entropy $\varphi$ with weights $\gamma$
-- statement:
--   The **dilated entropy** with weights $\gamma$ is
--   $$
--   \varphi(x)=\gamma_\varnothing x_\varnothing\log x_\varnothing+\sum_{j\in J}\gamma_j\Big(x_{p_j}\log|A_j|+\sum_{a\in A_j}x_{ja}\log\frac{x_{ja}}{x_{p_j}}\Big),
--   $$
--   with the convention $0\log 0=0\log(0/0)=0$.
--
--   It is an instance of the dilated distance-generating functions of Hoda et al., whose smoothed support function is computable in linear time; Theorem 3 says it coincides with $\tilde\varphi$ on $Q$.
--
--   **Formalization Note** The convention is what `Real.log` and $x/0=0$ give. On $Q$, $x_{p_j}=0$ forces $x_{ja}=0$, so no other boundary case occurs there.
-- source:
--   Farina, Kroer, Sandholm, Better Regularization for Sequential Decision Spaces, arXiv:2105.12954v2, §5 (Dilatability), p.11

import Mathlib
import Definitions.Def_DilatableEntropy_gammaRoot

namespace DilatableEntropy

/-- The **dilated entropy** `φ` with the weights `γ` (Farina, Kroer, Sandholm, *Better Regularization for Sequential Decision Spaces*, arXiv:2105.12954v2, §5 "Dilatability", p.11):
`φ(x) = γ_∅ x_∅ log x_∅ + ∑_{j ∈ J} γ_j (x_{p_j} log |A_j| + ∑_{a ∈ A_j} x_{ja} log(x_{ja} / x_{p_j}))`.

**Formalization Note** The paper's convention `0 log 0 = 0 log(0/0) = 0` (footnote 2, p.9) is
what Mathlib's `Real.log` and `x / 0 = 0` give. On `Q`, `x_{p_j} = 0` forces `x_{ja} = 0`, so
no other boundary case arises there. -/
noncomputable def dilatedEntropy (P : SeqDecisionProblem) (x : Seq P → ℝ) : ℝ :=
  gammaRoot P * x none * Real.log (x none)
    + ∑ j : P.J, gamma P j * (x (P.parent j) * Real.log (Fintype.card (P.A j))
        + ∑ a : P.A j, x (some ⟨j, a⟩) * Real.log (x (some ⟨j, a⟩) / x (P.parent j)))

end DilatableEntropy


