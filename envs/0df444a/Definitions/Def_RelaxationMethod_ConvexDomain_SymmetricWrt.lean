-- Prove2me | Definitions.Def_RelaxationMethod_ConvexDomain_SymmetricWrt
-- name    : RelaxationMethod_ConvexDomain_SymmetricWrt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:46:40.112452+00:00
-- url     : https://prove2.me/theorems/d195126d-b95f-4f73-aa9c-68ab5a57fc9e
-- title:
--   Two points symmetric with respect to a flat
-- statement:
--   Let $L$ be a flat (affine subspace) of $E_n$ with direction space $\vec L$. Two points $u, v \in E_n$ are **symmetric with respect to $L$** if
--   $$\tfrac12 (u + v) \in L \qquad\text{and}\qquad \langle u - v, w\rangle = 0 \ \text{ for all } w \in \vec L.$$
--   Equivalently, $v = 2\,\pi_L(u) - u$, where $\pi_L$ is the orthogonal projection on $L$: $v$ is the point reflection of $u$ through the foot of the perpendicular from $u$ to $L$.
--
--   This is the notion of symmetry in Case 2 of Theorem 3.
--
--   **Formalization Note** For $\dim L < n-1$ this is not a reflection in a hyperplane: the mirror is the point $\pi_L(u)$ inside the $(r+1)$-flat spanned by $L$ and $u$.
-- source:
--   Motzkin and Schoenberg, The relaxation method for linear inequalities, Canad. J. Math. 6 (1954), p. 402, Theorem 3, Case 2

import Mathlib

namespace RelaxationMethod.ConvexDomain

/-- Theorem 3, p. 402: the points `u` and `v` are symmetric with respect to the flat `L`:
their midpoint lies in `L` and `u - v` is orthogonal to the direction of `L`
(equivalently, `v` is the point reflection of `u` through its orthogonal projection on `L`). -/
def IsSymmetricWrt {n : ℕ} (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)))
    (u v : EuclideanSpace ℝ (Fin n)) : Prop :=
  midpoint ℝ u v ∈ L ∧ ∀ w ∈ L.direction, inner ℝ (u - v) w = 0

end RelaxationMethod.ConvexDomain


