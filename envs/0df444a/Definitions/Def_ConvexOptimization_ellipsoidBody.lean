-- Prove2me | Definitions.Def_ConvexOptimization_ellipsoidBody
-- name    : ConvexOptimization_ellipsoidBody
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-13T04:08:26.196602+00:00
-- url     : https://prove2.me/theorems/6ef5fae6-de88-43f6-b6a2-0fdf30b80efb
-- title:
--   Ellipsoid in quadratic-form guise
-- statement:
--   An ellipsoid of $\mathbb{R}^n$ written in *quadratic-form* (preimage) guise, the parametrization Boyd & Vandenberghe use for the minimum-volume covering ellipsoid problem.
--
--   Fix a dimension $n$, a matrix $A \in \mathbb{R}^{n \times n}$ and a vector $b \in \mathbb{R}^n$, and write $u \cdot w = \sum_{k=1}^{n} u_k w_k$ for the standard inner product on $\mathbb{R}^n$. The set defined here is
--
--   $$\mathcal{E}(A,b) \;=\; \{\, v \in \mathbb{R}^n \;:\; (Av + b)\cdot(Av + b) \le 1 \,\} \;=\; \{\, v \in \mathbb{R}^n \;:\; \lVert Av + b \rVert_2 \le 1 \,\},$$
--
--   the preimage of the closed Euclidean unit ball under the affine map $v \mapsto Av + b$.
--
--   When $A$ is symmetric positive definite this is a bounded, full-dimensional ellipsoid: its centre is $-A^{-1}b$, its semi-axis lengths are the reciprocals of the eigenvalues of $A$, and its volume is $\beta_n / \det A$ where $\beta_n$ is the volume of the unit ball. Minimizing volume over a family of covering ellipsoids is therefore exactly maximizing $\det A$, which is what makes this parametrization convenient — the covering constraints $\lVert Ax_i + b\rVert_2 \le 1$ are convex in $(A,b)$ and $\log \det A^{-1}$ is a convex objective.
--
--   No hypothesis on $A$ is built into the definition. For singular $A$ the set is an unbounded slab or cylinder, and for $A = 0$ it is all of $\mathbb{R}^n$ when $b \cdot b \le 1$ and empty otherwise; symmetry and positive definiteness are imposed by the statements that use it.
--
--   **Formalization Note** The ambient space is the plain function type `Fin n → ℝ` rather than `EuclideanSpace`, and the inner product is Mathlib's dot product `⬝ᵥ`; the squared inequality $(Av+b)\cdot(Av+b) \le 1$ is used in place of a norm because the pi type carries the sup norm, not the Euclidean one. The dimension is called `nn` in the Lean source.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 410, §8.4.1 eq. (8.9) (ellipsoid described as the preimage of the unit ball, E = {v | ||Av + b||_2 <= 1})

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

namespace ConvexOptimization

/-- The ellipsoid `{v | ‖Av + b‖₂ ≤ 1}` in quadratic-form guise (B&V (8.10)). -/
def ellipsoidBody {nn : ℕ} (A : Matrix (Fin nn) (Fin nn) ℝ) (b : Fin nn → ℝ) :
    Set (Fin nn → ℝ) :=
  {v | (A.mulVec v + b) ⬝ᵥ (A.mulVec v + b) ≤ 1}

end ConvexOptimization


