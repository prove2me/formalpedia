-- Prove2me | Definitions.Def_CombOpt_TotalUnimodularity_IsFace
-- name    : CombOpt_TotalUnimodularity_IsFace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:04:16.664141+00:00
-- url     : https://prove2.me/theorems/530941f8-2cee-4b0b-a557-0d0a5162f223
-- title:
--   Face of a polyhedron
-- statement:
--   Let $P\subseteq\mathbb R^n$ be a polyhedron. An inequality $w^\top x\le t$ (with $w\in\mathbb R^n$, $t\in\mathbb R$) is **valid** for $P$ if $P\subseteq\{x : w^\top x\le t\}$. If moreover $w\neq 0$ and $P\cap\{x : w^\top x=t\}\neq\emptyset$, the hyperplane $\{x : w^\top x = t\}$ is a **supporting hyperplane** of $P$.
--
--   A **face** of $P$ is a set of the form
--   $$F = P\cap\{x : w^\top x=t\}$$
--   for a supporting hyperplane $\{x: w^\top x=t\}$ of $P$; by convention the empty set and $P$ itself are also faces.
--
--   Faces are the basic objects of polyhedral combinatorics: integrality of a polyhedron, vertices and minimal faces are all defined through them.
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ` and $w^\top x$ is the dot product. The predicate is defined for any set $P$; in this mission it is applied only to polyhedra given by linear inequalities, equations and sign constraints.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.2, p. 204 (PDF p. 212)

import Mathlib

namespace CombOpt.TotalUnimodularity

open Matrix

/-- **Face of a polyhedron.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.2,
p. 204 (PDF p. 212): "An inequality wᵀx ≤ t is *valid* for a polyhedron P if
P ⊆ {x : wᵀx ≤ t}. As usual, we call the solution set of an equation wᵀx = t a *hyperplane* if
w ≠ 0. With respect to a polyhedron P, it is called a *supporting hyperplane* if wᵀx ≤ t is
valid for P and P ∩ {x : wᵀx = t} ≠ ∅. … In general, we call the intersection a *face* of the
polyhedron. By convention, we also call the null set and the polyhedron itself faces".

`IsFace P F` holds when `F = ∅`, or `F = P`, or `F = P ∩ {x : w ⬝ᵥ x = t}` for some `w ≠ 0`
and `t` with `w ⬝ᵥ x ≤ t` valid for `P` and `P ∩ {x : w ⬝ᵥ x = t}` nonempty.

**Formalization Note.** Vectors of `ℝⁿ` are `Fin n → ℝ` and `wᵀx` is `w ⬝ᵥ x`. The predicate is
stated for any set `P`; in this mission it is applied only to polyhedra `{x : Ax ≤ b}`
(possibly with extra equations or sign constraints), as in the book. -/
def IsFace {n : ℕ} (P F : Set (Fin n → ℝ)) : Prop :=
  F = ∅ ∨ F = P ∨
    ∃ (w : Fin n → ℝ) (t : ℝ), w ≠ 0 ∧ (∀ x ∈ P, w ⬝ᵥ x ≤ t) ∧
      (P ∩ {x | w ⬝ᵥ x = t}).Nonempty ∧ F = P ∩ {x | w ⬝ᵥ x = t}

end CombOpt.TotalUnimodularity


