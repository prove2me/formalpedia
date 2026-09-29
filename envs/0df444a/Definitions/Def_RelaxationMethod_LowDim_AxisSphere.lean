-- Prove2me | Definitions.Def_RelaxationMethod_LowDim_AxisSphere
-- name    : RelaxationMethod_LowDim_AxisSphere
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:28:42.59027+00:00
-- url     : https://prove2.me/theorems/0e0b48f5-389e-4180-837c-9efcae0d279c
-- title:
--   The locus (1.10): points equidistant with $c$ from every point of a flat $L$
-- statement:
--   Let $L$ be an affine subspace (a flat) of $E_n$ and $c \in E_n$. The locus
--   $$X(L, c) = \{x \in E_n : |x - a| = |c - a| \text{ for every } a \in L\}$$
--   is the set (1.10) of the paper. When $c \notin L$ and $L$ has dimension $r$, it is the $(n-r-1)$-dimensional sphere $S_{n-r-1}$ through $c$ that the paper calls a **spherical surface having $L$ as its axis**. When $c \in L$ the locus is the single point $\{c\}$.
--
--   This is the set on which, by Theorem 2, an infinite reflexion sequence eventually lies when the solution polytope is not full-dimensional.
--
--   **Formalization Note** The definition does not require $c \notin L$; every statement that uses $X(L, c)$ as a sphere assumes $c \notin L$ explicitly, which excludes the degenerate one-point locus.
-- source:
--   Motzkin and Schoenberg, The relaxation method for linear inequalities, Canad. J. Math. 6 (1954), DOI 10.4153/CJM-1954-038-x, p. 395, §2, (1.10)

import Mathlib

namespace RelaxationMethod.LowDim

/-- The locus (1.10) of points `x` with `|x - a| = |c - a|` for every point `a` of the flat `L`.
For `c ∉ L` this is the spherical surface `S_{n-r-1}` through `c` having `L` as its axis (§2,
p. 395); every statement using it assumes `c ∉ L` (for `c ∈ L` the locus is `{c}`). -/
def axisSphere {n : ℕ} (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)))
    (c : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ a ∈ L, dist x a = dist c a}

end RelaxationMethod.LowDim


