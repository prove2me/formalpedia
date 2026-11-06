-- Prove2me | Definitions.Def_BinaryQueryLB_Wset
-- name    : BinaryQueryLB_Wset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:45:00.618981+00:00
-- url     : https://prove2.me/theorems/19502e86-e055-423e-929a-edfe54ed6f82
-- title:
--   The matrix set $\mathcal W=(\tau\mathbb B_m)^m$
-- statement:
--   $\mathcal W=(\tau\mathbb B_m)^m$ is the set of $m\times m$ matrices $W$ whose rows $w_1,\dots,w_m$ lie in $\tau\mathbb B_m$, the closed Euclidean ball of radius $\tau=a/(\Gamma\sqrt m)$ about $0$ in $\mathbb R^m$.
--
--   **Formalization Note** A matrix is the family of its rows.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Definition 2.4, p.12

import Mathlib
import Definitions.Def_BinaryQueryLB_tau

namespace BinaryQueryLB

/-- **The matrix set `𝒲 = (τ𝔹_m)^m` (Definition 2.4).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Definition 2.4, p.12: "Let
`W = (τB_m)^m` be the set of `m × m` matrices `W` whose rows `w_1, …, w_m` lie in `τB_m`."

**Formalization Note.** A matrix is the family of its rows `W : Fin m → ℝ^m`; `τ𝔹_m` is the closed
Euclidean ball of radius `τ` about `0`. -/
def Wset (m : ℕ) : Set (Fin m → EuclideanSpace ℝ (Fin m)) :=
  {W | ∀ i, W i ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) (tau m)}

end BinaryQueryLB


