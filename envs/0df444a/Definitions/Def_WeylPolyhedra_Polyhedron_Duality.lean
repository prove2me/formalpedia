-- Prove2me | Definitions.Def_WeylPolyhedra_Polyhedron_Duality
-- name    : WeylPolyhedra_Polyhedron_Duality
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T22:02:15.417117+00:00
-- url     : https://prove2.me/theorems/c6febc13-b50c-405a-8458-3e0354350089
-- title:
--   Homogeneous inequality systems: the region $(S)$, extreme solutions, and the dual region $(\Sigma)$ (§3)
-- statement:
--   Let $S \subseteq \mathbb{R}^n$ be a finite point system, now read as the system of homogeneous linear inequalities
--   $$(a\xi) = a_1\xi_1 + \dots + a_n\xi_n \ge 0 \qquad (a \in S).$$
--
--   1. The **region** $(S) = \{\xi \in \mathbb{R}^n : (a\xi) \ge 0 \text{ for all } a \in S\}$ is the set of solutions of the system.
--   2. A vector $\xi$ is an **extreme solution** of $S$ when $\xi \in (S)$, $\xi \neq 0$, and equality $(a\xi) = 0$ holds in $n-1$ linearly independent inequalities $a \in S$.
--   3. The **dual system** $\Sigma$ consists of the inequalities $(\alpha x) \ge 0$, one for each extreme solution $\alpha$ of $S$, and its region is
--   $$(\Sigma) = \{x \in \mathbb{R}^n : (\alpha x) \ge 0 \text{ for every extreme solution } \alpha \text{ of } S\}.$$
--
--   Weyl uses these objects to set up the duality between a finite point system and the finite system of its extreme supports (Satz 3 to Satz 11).
--
--   **Formalization Note** Weyl's Satz 4 defines an extreme solution only by the $n-1$ independent equalities; the requirements $\xi \in (S)$ and $\xi \neq 0$ are added explicitly, following the word "Lösung" and Weyl's identification of solutions on the same ray (they are rays, and $0$ is not one). Since positive multiples of an extreme solution give the same inequality, $(\Sigma)$ quantifies over all extreme solutions rather than choosing representatives.
-- source:
--   Weyl, Elementare Theorie der konvexen Polyeder, Comment. Math. Helv. (1935), p. 296, §3 (9) and Satz 4; p. 297, (10)

import Mathlib

namespace WeylPolyhedra.Polyhedron

/-- Weyl (1935), §3, p. 296, (9): the finite point system `S ⊆ ℝⁿ` read as the system of
homogeneous linear inequalities `a ⬝ᵥ ξ ≥ 0` (`a ∈ S`); `(S)` is the region of the dual space
cut out by them. -/
def solutionRegion {n : ℕ} (S : Finset (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {ξ | ∀ a ∈ S, 0 ≤ a ⬝ᵥ ξ}

/-- Weyl (1935), §3, p. 296, Satz 4: `ξ` is an *extreme Lösung* (extreme solution) of the
inequality system `S` when equality `a ⬝ᵥ ξ = 0` holds in `n - 1` linearly independent
inequalities `a` of `S`. Added, as implicit in the word "Lösung" and in the identification of
solutions on a ray (p. 290, p. 297): `ξ` solves the system (`ξ ∈ (S)`) and `ξ ≠ 0`. -/
def IsExtremeSolution {n : ℕ} (S : Finset (Fin n → ℝ)) (ξ : Fin n → ℝ) : Prop :=
  ξ ∈ solutionRegion S ∧ ξ ≠ 0 ∧
    ∃ T : Finset (Fin n → ℝ), T ⊆ S ∧ T.card = n - 1 ∧
      LinearIndependent ℝ (fun t : T => (t : Fin n → ℝ)) ∧ ∀ a ∈ T, a ⬝ᵥ ξ = 0

/-- Weyl (1935), §3, p. 297, (10): the region `(Σ)` of the dual system `Σ`, whose inequalities
are `α ⬝ᵥ x ≥ 0` for **all** extreme solutions `α` of `S` (positive multiples of an extreme
solution give the same inequality, so no representatives are chosen). -/
def dualRegion {n : ℕ} (S : Finset (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x | ∀ α : Fin n → ℝ, IsExtremeSolution S α → 0 ≤ α ⬝ᵥ x}

end WeylPolyhedra.Polyhedron


