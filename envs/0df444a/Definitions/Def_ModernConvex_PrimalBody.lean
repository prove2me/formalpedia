-- Prove2me | Definitions.Def_ModernConvex_PrimalBody
-- name    : ModernConvex_PrimalBody
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:56:30.029559+00:00
-- url     : https://prove2.me/theorems/ea75239b-4f9f-45de-972f-3710c9c491e9
-- title:
--   The primal MAXCUT SDP body in ellipsoid coordinates
-- statement:
--   **The primal body of the Max-Cut semidefinite relaxation, in ellipsoid coordinates.**
--
--   For a weighted graph on $n$ vertices, the feasible set of the relaxation $\max\{\tfrac14\sum_{i,j}a_{ij}(1-X_{ij}) : X\succeq0,\ X_{ii}=1\}$ is a set of $n\times n$ matrices. Enumerating each matrix column by column turns it into a point of $\mathbb R^{n^2}$, and `primalBodyVec n` is the resulting set:
--   $$x\in\texttt{primalBodyVec}\ n \iff \texttt{finToMat}\ x\succeq0\ \text{and}\ (\texttt{finToMat}\ x)_{ii}=1\ \text{for all } i .$$
--   This is the set on which the ellipsoid method is run: it is compact and convex (closed, bounded by $|X_{ij}|\le1$, and convex as the intersection of the semidefinite cone with affine constraints), with the identity matrix in its interior.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, (4.3.15), p. 170; body coordinates chosen for Bubeck arXiv:1405.4980v2, Thm 2.4.

import Mathlib
import Definitions.Def_ModernConvex_MatrixVec

/-!
# The primal body of the Max-Cut SDP in ellipsoid coordinates

The feasible set of the Max-Cut semidefinite relaxation, reindexed as a subset of
`Fin (n * n) → ℝ` so that the ellipsoid method of `ConvexOptAlg.Ellipsoid.theorem_2_4` applies:
`x ∈ primalBodyVec n` iff the matrix it enumerates is positive semidefinite with unit diagonal.
-/

open Matrix
open scoped BigOperators MatrixOrder

namespace ModernConvex.Relaxations

/-- The primal body of the Max-Cut SDP, in the ellipsoid coordinates of `ℝ^{n·n}`. -/
def primalBodyVec (n : ℕ) : Set (Fin (n * n) → ℝ) :=
  {x | (finToMat x).PosSemidef ∧ ∀ i, (finToMat x) i i = 1}

end ModernConvex.Relaxations


