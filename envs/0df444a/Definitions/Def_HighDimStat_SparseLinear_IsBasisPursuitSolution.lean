-- Prove2me | Definitions.Def_HighDimStat_SparseLinear_IsBasisPursuitSolution
-- name    : HighDimStat_SparseLinear_IsBasisPursuitSolution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:07:59.125709+00:00
-- url     : https://prove2.me/theorems/9b199658-aeee-408a-bd40-d25f143f8557
-- title:
--   theta-hat solves the basis pursuit linear program (7.9)
-- statement:
--   This predicate says $\hat\theta$ is an optimal solution of the **basis pursuit linear
--   program** (7.9): among all vectors consistent with the noiseless observations $y = X\theta$,
--   $\hat\theta$ has the smallest $\ell^1$-norm.
--
--   For $X \in \mathbb R^{n\times d}$, $y \in \mathbb R^n$, and $\hat\theta \in \mathbb R^d$,
--
--   $$
--   \hat\theta \text{ solves (7.9) for } (X,y) \;:\Longleftrightarrow\; X\hat\theta = y
--   \ \wedge\ \forall \beta \in \mathbb R^d,\ X\beta = y \Rightarrow \|\hat\theta\|_1 \le
--   \|\beta\|_1.
--   $$
--
--   Theorem 7.8 characterizes exactly when this optimal $\hat\theta$ is unique and equal to a
--   sparse $\theta^*$ generating $y$.
--
--   **Formalization Note** This states optimality, not by itself uniqueness; Theorem 7.8's own
--   statement layers "for every optimal $\hat\theta$, $\hat\theta = \theta^*$" on top of this
--   predicate to express "the unique solution is $\theta^*$," exactly mirroring how the book's
--   Theorem 7.8(a) phrases it.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 200 (PDF p. 220), Eq. (7.9)

import Mathlib
import Definitions.Def_HighDimStat_SparseLinear_L1Norm

namespace HighDimStat.SparseLinear

/-- `θhat` is an optimal solution of the basis pursuit linear program (7.9),
`min_θ ‖θ‖₁` s.t. `Xθ = y`, of Wainwright, *High-Dimensional Statistics* (2019), p. 200:
`θhat` is feasible and minimizes the `ℓ¹`-norm among all feasible vectors. -/
def IsBasisPursuitSolution {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ)
    (θhat : Fin d → ℝ) : Prop :=
  X.mulVec θhat = y ∧ ∀ β : Fin d → ℝ, X.mulVec β = y → l1Norm θhat ≤ l1Norm β

end HighDimStat.SparseLinear


