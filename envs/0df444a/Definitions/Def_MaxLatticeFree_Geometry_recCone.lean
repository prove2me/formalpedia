-- Prove2me | Definitions.Def_MaxLatticeFree_Geometry_recCone
-- name    : MaxLatticeFree_Geometry_recCone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T18:11:59.353253+00:00
-- url     : https://prove2.me/theorems/3a082bc4-7eb0-4bf1-a168-c11b602915aa
-- title:
--   Recession cone $\operatorname{rec}(S)$ and lineality space
-- statement:
--   For $S\subseteq\mathbb R^n$ the **recession cone** of $S$ is the set of directions along which one can move indefinitely from every point of $S$ without leaving $S$:
--
--   $$
--   \operatorname{rec}(S)=\{r\in\mathbb R^n \mid x+tr\in S \text{ for all } x\in S,\ t\ge 0\}.
--   $$
--
--   The **lineality space** of $S$ is the set of directions $r$ with both $r$ and $-r$ in the recession cone,
--
--   $$
--   \operatorname{lin}(S)=\operatorname{rec}(S)\cap\bigl(-\operatorname{rec}(S)\bigr).
--   $$
--
--   For a nonempty convex set, $\operatorname{rec}(S)$ is a convex cone and $\operatorname{lin}(S)$ a linear subspace. They enter through Lemma 16 and the two claims in the proof of Theorem 10, where an unbounded maximal lattice-free set is shown to be a cylinder over its lineality space.
--
--   **Formalization Note** The paper takes both notions from convex analysis without a definition; the form above is the one its proof of Lemma 16 uses. No closedness of $S$ is assumed. For $S=\emptyset$ every direction belongs to $\operatorname{rec}(S)$.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 12 (Lemma 16) and p. 14 (proof of Theorem 10); notions from convex analysis, ref. [21]

import Mathlib

namespace MaxLatticeFree.Geometry

/-- Recession cone `rec(S)` of a set `S ⊆ ℝⁿ` (used in Lemma 16 and the proof of Theorem 10 of
arXiv:1701.06543v1, pp. 12–14; the paper takes it from convex analysis): the directions `r` with
`x + t r ∈ S` for every `x ∈ S` and every `t ≥ 0`. No closedness is assumed; for `S = ∅` every
direction qualifies. -/
def recCone {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  {r | ∀ x ∈ S, ∀ t : ℝ, 0 ≤ t → x + t • r ∈ S}

/-- Lineality space of `S` (proof of Theorem 10, arXiv:1701.06543v1, p. 14): the directions `r`
with both `r` and `-r` in the recession cone, i.e. `rec(S) ∩ -rec(S)`. -/
def linSpace {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  {r | r ∈ recCone S ∧ -r ∈ recCone S}

end MaxLatticeFree.Geometry


