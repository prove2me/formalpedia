-- Prove2me | Definitions.Def_AnchoredEP_IsSolution
-- name    : AnchoredEP_IsSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:34:57.321202+00:00
-- url     : https://prove2.me/theorems/e442519c-5f1d-47e6-bb66-bea218124f59
-- title:
--   Solution of the monotone inclusion $0\in F(z)+H(z)$
-- statement:
--   Let $F:\mathbb R^d\to\mathbb R^d$ and let $H:\mathbb R^d\rightrightarrows\mathbb R^d$ be a set-valued operator. A point $z^\ast\in\mathbb R^d$ is a **solution** of the monotone inclusion problem
--   $$
--   \text{find } z\in\mathbb R^d \text{ such that } 0\in F(z)+H(z)
--   $$
--   if there is a vector $v^\ast\in H(z^\ast)$ with $F(z^\ast)+v^\ast=0$.
--
--   The paper assumes throughout that a solution exists and measures all bounds by the distance $\|z_0-z^\ast\|$ from the initial point to an arbitrary solution.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` and a set-valued operator is a map into `Set`.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Section 1, Problem (1), p.1

import Mathlib

namespace AnchoredEP

/-- **A solution of the monotone inclusion (1).** Jiang–Yoon, *Anchored Extra-Proximal Methods:
Optimal Higher-Order Methods for Monotone Inclusion Problems*, arXiv:2609.30212, Section 1,
Problem (1), p.1: "find `z ∈ ℝ^d` such that `0 ∈ F(z) + H(z)`".

`IsSolution F H zstar` says that some `v ∈ H(zstar)` satisfies `F(zstar) + v = 0`, i.e.
`0 ∈ F(zstar) + H(zstar)`.

**Formalization Note.** `ℝ^d` is `EuclideanSpace ℝ (Fin d)`; the set-valued operator
`H : ℝ^d ⇒ ℝ^d` is a map `E → Set E`. -/
def IsSolution {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (H : EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin d)))
    (zstar : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∃ v ∈ H zstar, F zstar + v = 0

end AnchoredEP


