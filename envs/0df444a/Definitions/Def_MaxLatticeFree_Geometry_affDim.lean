-- Prove2me | Definitions.Def_MaxLatticeFree_Geometry_affDim
-- name    : MaxLatticeFree_Geometry_affDim
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T18:12:20.382541+00:00
-- url     : https://prove2.me/theorems/bcd58be2-114d-4b73-af77-9625bc022ae6
-- title:
--   Dimension $\dim(S)$ of a set, with $\dim(\emptyset)=-1$
-- statement:
--   The **dimension** of a set $S\subseteq\mathbb R^n$ is the dimension of its affine hull, with the standard convention for the empty set:
--
--   $$
--   \dim(S)=\begin{cases}\dim\operatorname{aff}(S) & S\neq\emptyset,\\ -1 & S=\emptyset.\end{cases}
--   $$
--
--   It is an integer, so that statements such as $\dim(F)=\dim(S)-1$ for a facet are ordinary integer equations.
--
--   **Formalization Note** `affDim S : ℤ` is the `finrank` of the direction of `affineSpan ℝ S` when `S` is nonempty and `-1` otherwise. Using a natural-number dimension would give $\dim(\emptyset)=0$ and truncated subtraction, which would make a point a facet of itself.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, pp. 8–15 (dim(S) used throughout; standard convention)

import Mathlib

namespace MaxLatticeFree.Geometry

open Classical in
/-- Dimension `dim(S)` of a set `S ⊆ ℝⁿ`: the dimension of its affine hull, with the standard
convention `dim(∅) = -1`. Integer valued so that `dim(F) = dim(S) - 1` is never a truncated
natural-number subtraction. -/
noncomputable def affDim {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) : ℤ :=
  if S.Nonempty then (Module.finrank ℝ (affineSpan ℝ S).direction : ℤ) else -1

end MaxLatticeFree.Geometry


