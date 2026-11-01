-- Prove2me | Definitions.Def_PSDPolyApprox_pairSlackMatrix
-- name    : PSDPolyApprox_pairSlackMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:54.643222+00:00
-- url     : https://prove2.me/theorems/fc953e9f-116f-41b5-bf94-84272e6a349d
-- title:
--   Slack matrix $S_{K,L}(x,y)=1-\langle x,y\rangle$ of a pair
-- statement:
--   For convex bodies $K\subseteq L\subseteq\mathbb R^d$, the (potentially infinite) **slack matrix of the pair** $(K,L)$ is
--   $$
--   S_{K,L}(x,y)=1-\langle x,y\rangle,
--   $$
--   with rows indexed by the extreme points $x$ of $K$ and columns indexed by the extreme points $y$ of the polar $L^\circ$. When $K\subseteq L$ all entries are nonnegative.
--
--   **Formalization Note** The row and column index sets are the sets of extreme points themselves, which may be infinite; nonnegative factorizations of such matrices still have finitely many rank-one terms.
-- source:
--   Fawzi, On polyhedral approximations of the positive semidefinite cone, arXiv:1811.09649v1, §2.2, p.4, equation (2)

import Mathlib
import Definitions.Def_PSDPolyApprox_polar

namespace PSDPolyApprox

open Matrix

/-- **Slack matrix of a pair `(K, L)`.**
Fawzi, arXiv:1811.09649v1, §2.2, p.4, equation (2): "Deﬁne the (potentially inﬁnite) slack
matrix of the pair (K, L) as the matrix SK,L(x, y) ↦ 1 − ⟨x, y⟩ where rows are indexed by extreme
points x of K, and columns are indexed by extreme points y of L◦."

`pairSlackMatrix K L x y = 1 − x ⬝ᵥ y` for `x ∈ ext K` and `y ∈ ext L°`.

**Formalization Note.** Rows and columns are the subtypes `Set.extremePoints ℝ K` and
`Set.extremePoints ℝ (polar L)`, which may be infinite. -/
def pairSlackMatrix {ι : Type*} [Fintype ι] (K L : Set (ι → ℝ)) :
    Matrix (Set.extremePoints ℝ K) (Set.extremePoints ℝ (polar L)) ℝ :=
  fun x y => 1 - (x : ι → ℝ) ⬝ᵥ (y : ι → ℝ)

end PSDPolyApprox


