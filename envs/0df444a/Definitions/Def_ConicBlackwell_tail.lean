-- Prove2me | Definitions.Def_ConicBlackwell_tail
-- name    : ConicBlackwell_tail
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:42:26.340788+00:00
-- url     : https://prove2.me/theorems/ffe683f7-4212-4f4b-ae06-3fd32b72b6bf
-- title:
--   The $\mathbb R^n$ part $\hat u$ of $u=(\tilde u,\hat u)\in\mathbb R\times\mathbb R^n$
-- statement:
--   An aggregate payoff vector is written $u=(\tilde u,\hat u)\in\mathbb R\times\mathbb R^n$, with a scalar part $\tilde u$ and a vector part $\hat u$. This definition is the map $u\mapsto\hat u$.
--
--   **Formalization Note** $\mathbb R\times\mathbb R^n$ is the Euclidean space $\mathbb R^{n+1}$ with the scalar in coordinate $0$ (as in the published `ApproachRegret.ToOLO.lift`), so $\tilde u$ is `u 0` and $\hat u$ = `tail u` collects coordinates $1,\dots,n$; in particular `tail (lift a x) = x`.
-- source:
--   Grand-Clément & Kroer, Solving Optimization Problems with Blackwell Approachability, arXiv:2202.12277v1 (https://arxiv.org/abs/2202.12277v1), §3.1, p.5 ("Given an aggregate payoff vector u = (ũ, û) ∈ ℝ × ℝⁿ")

import Mathlib
import Definitions.Def_ApproachRegret_ToOLO_Cones
open scoped RealInnerProductSpace
open ApproachRegret.ToOLO

namespace ConicBlackwell

/-- **The `ℝⁿ` part `û` of a vector `u = (ũ, û) ∈ ℝ × ℝⁿ`.**
Grand-Clément & Kroer, *Solving Optimization Problems with Blackwell Approachability*, arXiv:2202.12277v1, §3.1, p.5 ("Given an aggregate payoff vector u = (ũ, û) ∈ ℝ × ℝⁿ").

Formalization Note: `ℝ × ℝⁿ` is `E (n + 1)` with the scalar `ũ = u 0` in coordinate `0`, as in
`ApproachRegret.ToOLO.lift`; `tail u` is the vector of coordinates `1, …, n`, so that
`tail (lift a x) = x`. -/
noncomputable def tail {n : ℕ} (u : E (n + 1)) : E n :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (fun j => u j.succ)

end ConicBlackwell


