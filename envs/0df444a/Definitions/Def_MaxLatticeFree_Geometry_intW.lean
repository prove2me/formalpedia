-- Prove2me | Definitions.Def_MaxLatticeFree_Geometry_intW
-- name    : MaxLatticeFree_Geometry_intW
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T18:11:14.465798+00:00
-- url     : https://prove2.me/theorems/61bb8e94-bf07-4f1c-9b1f-177789f345fe
-- title:
--   Interior relative to a subspace, $\mathbf{int}_W(S)$, and relative interior
-- statement:
--   For $x\in\mathbb R^n$ and $\varepsilon>0$ let $B_\varepsilon(x)$ be the open Euclidean ball of radius $\varepsilon$ centred at $x$. For sets $W,S\subseteq\mathbb R^n$ the **interior of $S$ relative to $W$** is
--
--   $$
--   \mathbf{int}_W(S)=\{x\in S \mid B_\varepsilon(x)\cap W\subseteq S \text{ for some } \varepsilon>0\}.
--   $$
--
--   When $W$ is an affine space containing $S$, this is the interior of $S$ in the topology that $W$ inherits from $\mathbb R^n$. The **relative interior** of $S$ is its interior relative to its own affine hull,
--
--   $$
--   \mathbf{relint}(S)=\mathbf{int}_{\operatorname{aff}(S)}(S).
--   $$
--
--   Every notion of "interior" in the mission is one of these two: lattice-freeness is measured by $\mathbf{int}_W$, and lattice points on facets by $\mathbf{relint}$. With the ambient interior instead, every subset of a proper subspace would be trivially lattice-free.
--
--   **Formalization Note** `intW W S` is defined for arbitrary sets `W S`, literally as on p. 8; `relint S` is `intW (affineSpan ℝ S) S`. It coincides with Mathlib's `intrinsicInterior ℝ S`, but that equivalence is not used or asserted here.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 8, notation before Definition 8

import Mathlib

namespace MaxLatticeFree.Geometry

/-- Interior relative to `W` (arXiv:1701.06543v1, p. 8): `int_W(S)` is the set of points `x ∈ S`
such that `B_ε(x) ∩ W ⊆ S` for some `ε > 0`, where `B_ε(x)` is the open Euclidean ball.
This is the interior of `S` in the topology induced on `W` by `ℝⁿ` (for `S ⊆ W`). -/
def intW {n : ℕ} (W S : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | x ∈ S ∧ ∃ ε : ℝ, 0 < ε ∧ Metric.ball x ε ∩ W ⊆ S}

/-- Relative interior (arXiv:1701.06543v1, p. 8): `relint(S) = int_{aff(S)}(S)`, the interior of
`S` relative to its affine hull. -/
def relint {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  intW (affineSpan ℝ S : Set (EuclideanSpace ℝ (Fin n))) S

end MaxLatticeFree.Geometry


