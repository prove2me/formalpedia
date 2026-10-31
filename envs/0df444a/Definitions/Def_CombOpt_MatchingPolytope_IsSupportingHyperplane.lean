-- Prove2me | Definitions.Def_CombOpt_MatchingPolytope_IsSupportingHyperplane
-- name    : CombOpt_MatchingPolytope_IsSupportingHyperplane
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:05:08.207116+00:00
-- url     : https://prove2.me/theorems/a818aa5a-d2e8-4373-8b58-a68bf3ab89df
-- title:
--   A supporting hyperplane of a set
-- statement:
--   The solution set of an equation $w^\top x=t$ is a **hyperplane** if $w\ne0$. With respect to a polyhedron $P$, it is a **supporting hyperplane** if $w^\top x\le t$ is valid for $P$ and $P\cap\{x:\ w^\top x=t\}\ne\emptyset$.
--
--   Faces of polyhedra are their intersections with supporting hyperplanes.
--
--   **Formalization Note** The space $\mathbb R^n$ is the coordinate space $\mathbb R^\iota$ of functions $\iota\to\mathbb R$ on a finite index type $\iota$ (take $\iota=\{1,\dots,n\}$ for $\mathbb R^n$, or $\iota=E$ for $\mathbb R^E$), and $w^\top x$ is the dot product.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.2, p. 204 (PDF p. 212)

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_IsValid

namespace CombOpt.MatchingPolytope

/-- **A supporting hyperplane.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.2, p. 204 (PDF p. 212): "we call the solution set of an equation w^T x = t a hyperplane
if w ≠ 0. With respect to a polyhedron P, it is called a supporting hyperplane if w^T x ≤ t is
valid for P and P ∩ {x : w^T x = t} ≠ ∅."

`IsSupportingHyperplane P w t` says that `{x | w ⬝ᵥ x = t}` is a supporting hyperplane of `P`.

**Formalization Note.** `ℝ^n` is the coordinate space `ι → ℝ` over a finite index type `ι`
(`Fin n` for the book's `ℝ^n`, `E` for `ℝ^E`); `w ⬝ᵥ x` is `w^T x`. -/
def IsSupportingHyperplane {ι : Type*} [Fintype ι] (P : Set (ι → ℝ)) (w : ι → ℝ) (t : ℝ) :
    Prop :=
  w ≠ 0 ∧ IsValid P w t ∧ (P ∩ {x | w ⬝ᵥ x = t}).Nonempty

end CombOpt.MatchingPolytope


