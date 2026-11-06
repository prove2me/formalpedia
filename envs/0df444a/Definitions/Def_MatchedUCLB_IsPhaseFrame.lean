-- Prove2me | Definitions.Def_MatchedUCLB_IsPhaseFrame
-- name    : MatchedUCLB_IsPhaseFrame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:31:07.863759+00:00
-- url     : https://prove2.me/theorems/4959ba9e-319c-4c4f-be62-0a8461b26452
-- title:
--   An orthonormal phase frame
-- statement:
--   Directions $v_j,u_{j,1},\dots,u_{j,m}$ ($0\le j<L$) form a **phase frame** if all $L(m+1)$ of them are orthonormal. Equivalently, the blocks $E_j=\operatorname{span}\{v_j,u_{j,1},\dots,u_{j,m}\}$ are mutually orthogonal and each has the displayed orthonormal basis. A phase frame exists exactly when $d\ge L(m+1)$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Step 2.1, p.7; Definition E.1, p.83

import Mathlib
import Definitions.Def_MatchedUCLB_frameVec

namespace MatchedUCLB

/-- **An orthonormal phase frame.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Step 2.1, p.7, and Definition E.1, p.83: the blocks
`E_0, …, E_{L−1}` are mutually orthogonal and `v_j, u_{j,1}, …, u_{j,m}` is an orthonormal basis of
`E_j`. Equivalently, the family of all `v_j, u_{j,i}` (`j < L`, `1 ≤ i ≤ m`) is orthonormal. -/
def IsPhaseFrame {d m : ℕ} (L : ℕ) (v : ℕ → EuclideanSpace ℝ (Fin d)) (u : ℕ → Fin m → EuclideanSpace ℝ (Fin d)) : Prop :=
  Orthonormal ℝ (frameVec L v u)

end MatchedUCLB


