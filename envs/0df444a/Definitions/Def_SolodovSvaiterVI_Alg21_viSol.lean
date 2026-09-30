-- Prove2me | Definitions.Def_SolodovSvaiterVI_Alg21_viSol
-- name    : SolodovSvaiterVI_Alg21_viSol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T09:49:15.604167+00:00
-- url     : https://prove2.me/theorems/b49f394c-a837-44db-90b8-57551150046c
-- title:
--   Solution set $S$ of the variational inequality $\mathrm{VI}(F, C)$
-- statement:
--   Let $C \subseteq \mathbb{R}^n$ and $F : \mathbb{R}^n \to \mathbb{R}^n$. The **variational inequality problem** $\mathrm{VI}(F, C)$ asks for a point $x^*$ such that
--
--   $$x^* \in C, \qquad \langle F(x^*), x - x^* \rangle \ge 0 \quad \text{for all } x \in C. \tag{1.1}$$
--
--   The set $S$ of all such points is the **solution set** of $\mathrm{VI}(F, C)$. Variational inequalities include systems of nonlinear equations ($C = \mathbb{R}^n$), complementarity problems ($C$ the nonnegative orthant) and first-order optimality conditions of constrained optimization ($F = \nabla f$).
--
--   **Formalization Note** $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)` with its standard inner product. No hypotheses on $F$ or $C$ are built into the definition; the theorems add them (closed convex $C$, continuous $F$).
-- source:
--   Solodov & Svaiter, A New Projection Method for Variational Inequality Problems, SIAM J. Control Optim. 37 (1999), p. 765, Section 1, Eq. (1.1)

import Mathlib

open scoped InnerProductSpace

namespace SolodovSvaiterVI.Alg21

/-- The solution set `S` of the variational inequality `VI(F, C)` (Solodov–Svaiter, p. 765,
(1.1)): the points `x* ∈ C` with `⟨F(x*), x − x*⟩ ≥ 0` for all `x ∈ C`. -/
def viSol {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (C : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | x ∈ C ∧ ∀ y ∈ C, 0 ≤ ⟪F x, y - x⟫_ℝ}

end SolodovSvaiterVI.Alg21


