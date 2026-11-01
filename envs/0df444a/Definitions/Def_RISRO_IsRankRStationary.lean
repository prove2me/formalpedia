-- Prove2me | Definitions.Def_RISRO_IsRankRStationary
-- name    : RISRO_IsRankRStationary
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:31:58.564227+00:00
-- url     : https://prove2.me/theorems/43bd80a3-919d-4a6b-ba9c-baab53fa74aa
-- title:
--   Rank-$r$ stationary point of problem (1)
-- statement:
--   A matrix $X$ is a **rank $r$ stationary point** of problem (1) when $\operatorname{rank}X=r$ and
--
--   $$
--   \nabla f(X)^\top\bar U=0,\qquad \nabla f(X)\bar V=0,
--   $$
--
--   where $\bar U,\bar V$ are the left and right singular vectors of $X$.
--
--   **Formalization Note.** The condition is stated in the basis-free form $X^\top\nabla f(X)=0$, $\nabla f(X)X^\top=0$, which is equivalent when $\operatorname{rank}X=r$: with $X=\bar U\bar\Sigma\bar V^\top$ and $\bar\Sigma$ invertible, $X^\top\nabla f=\bar V\bar\Sigma\bar U^\top\nabla f$ vanishes exactly when $\bar U^\top\nabla f$ does, and $\nabla f\,X^\top=\nabla f\,\bar V\bar\Sigma\bar U^\top$ vanishes exactly when $\nabla f\,\bar V$ does.
-- source:
--   Luo, Huang, Li & Zhang, Recursive Importance Sketching for Rank Constrained Least Squares, arXiv:2011.08360v4, p.11

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic
import Definitions.Def_RISRO_gradF

open HighDimStat.MatrixRank Matrix

namespace RISRO

/-- `X` is a stationary point of problem (1): `rank X = r`, and `∇f(X)ᵀ Ū = 0`, `∇f(X) V̄ = 0`
for the left and right singular vectors `Ū`, `V̄` of `X`.

Luo, Huang, Li & Zhang, arXiv:2011.08360v4, p.11.

Formalization Note: basis-free form `Xᵀ ∇f(X) = 0`, `∇f(X) Xᵀ = 0`. It is equivalent to the
page's condition when `rank X = r`: writing `X = Ū Σ̄ V̄ᵀ` with `Σ̄` invertible, `Xᵀ ∇f = V̄ Σ̄ Ūᵀ ∇f`
vanishes iff `Ūᵀ ∇f` does, and `∇f Xᵀ = ∇f V̄ Σ̄ Ūᵀ` vanishes iff `∇f V̄` does. -/
def IsRankRStationary {p₁ p₂ n : ℕ} (A : Fin n → Matrix (Fin p₁) (Fin p₂) ℝ) (y : Fin n → ℝ)
    (r : ℕ) (X : Matrix (Fin p₁) (Fin p₂) ℝ) : Prop :=
  X.rank = r ∧ Xᵀ * gradF A y X = 0 ∧ gradF A y X * Xᵀ = 0

end RISRO


