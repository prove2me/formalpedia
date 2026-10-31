-- Prove2me | Definitions.Def_DissolveCDF_IsStationaryOCP
-- name    : DissolveCDF_IsStationaryOCP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:30:53.005143+00:00
-- url     : https://prove2.me/theorems/85277c5c-1837-4c55-a243-66e62e71fc5d
-- title:
--   Definition 2.1 — first-order stationary point of OCP
-- statement:
--   A point $x\in\mathbb R^n$ is a **first-order stationary point of OCP** if there is $\tilde\lambda\in\mathbb R^p$ with
--
--   $$
--   \nabla f(x)-\sum_{i=1}^p\tilde\lambda_i\nabla c_i(x)=0,\qquad c(x)=0. \tag{2.1}
--   $$
--
--   **Formalization Note** $\sum_i\tilde\lambda_i\nabla c_i(x)=J_c(x)\tilde\lambda$, since the columns of $J_c(x)$ are the gradients $\nabla c_i(x)$.
-- source:
--   Xiao, Liu & Toh, Dissolving Constraints for Riemannian Optimization, arXiv:2203.10319v3, Definition 2.1, (2.1), p.5

import Mathlib
import Definitions.Def_DissolveCDF_transJac

namespace DissolveCDF

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, Definition 2.1 (p.5): `x ∈ ℝⁿ` is a **first-order stationary point of OCP** if
there is `λ̃ ∈ ℝᵖ` with `∇f(x) − Σᵢ λ̃ᵢ ∇cᵢ(x) = 0` and `c(x) = 0`.

**Formalization Note** `Σᵢ λ̃ᵢ ∇cᵢ(x) = J_c(x) λ̃`, since the columns of `J_c(x)` are the
gradients `∇cᵢ(x)`. -/
def IsStationaryOCP {n p : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p)) (x : EuclideanSpace ℝ (Fin n)) :
    Prop :=
  ∃ lam : EuclideanSpace ℝ (Fin p), gradient f x - transJac c x lam = 0 ∧ c x = 0

end DissolveCDF


