-- Prove2me | Definitions.Def_WeylPolyhedra_Polyhedron_Supplement_DualSystems
-- name    : WeylPolyhedra_Polyhedron_Supplement_DualSystems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T06:33:00.336498+00:00
-- url     : https://prove2.me/theorems/db3fecbc-7950-4c16-8297-82eedc6c6314
-- title:
--   Inequality systems given by infinite sets: their region and extreme solutions; the systems $\Sigma$ and $S'$ (§3, Satz 4 and IV)
-- statement:
--   Let $S \subseteq \mathbb{R}^n$ be a finite system of homogeneous inequalities $(a\xi) = a_1\xi_1 + \dots + a_n\xi_n \ge 0$, $a \in S$. Weyl's dual system $\Sigma$ and the system $S'$ have as inequalities **all** extreme solutions of a system, a set closed under positive scaling and so infinite. This definition extends the region and the extreme solutions from finite systems to arbitrary sets of inequalities.
--
--   1. For a set $A \subseteq \mathbb{R}^n$, its **region** is $\{\xi \in \mathbb{R}^n : (a\xi) \ge 0 \text{ for all } a \in A\}$.
--   2. A vector $\xi$ is an **extreme solution** of $A$ when $\xi$ lies in the region of $A$, $\xi \neq 0$, and $(a\xi) = 0$ holds for $n-1$ linearly independent vectors $a \in A$.
--   3. $\Sigma$ is the set of all extreme solutions $\alpha$ of the finite system $S$. Its region is the region $(\Sigma)$ of Weyl's dual system (10).
--   4. $S'$ is the set of all extreme solutions $a'$ of $\Sigma$. Its region is the region $(S')$ of Satz 10:
--   $$(S') = \{\xi : (a'\xi) \ge 0 \text{ for every extreme solution } a' \text{ of } \Sigma\}.$$
--
--   These objects carry Weyl's "complete dualization" of §3 IV (Satz 10–12).
--
--   **Formalization Note** For a finite $A$ the region and the extreme solutions coincide with the published `solutionRegion` and `IsExtremeSolution` (which take a `Finset`). As there, $\xi \neq 0$ and membership in the region are part of being an extreme solution. No representatives of the rays are chosen: $\Sigma$ and $S'$ contain every positive multiple.
-- source:
--   Weyl, Elementare Theorie der konvexen Polyeder, Comment. Math. Helv. (1935), p. 296, Satz 4; p. 297, (10); p. 300, §3 IV

import Mathlib
import Definitions.Def_WeylPolyhedra_Polyhedron_Duality

namespace WeylPolyhedra.Polyhedron.Supplement

/-- Weyl (1935), §3, p. 296 (Satz 4) and p. 300 (IV): the region of an arbitrary — possibly
infinite — set `A ⊆ ℝⁿ` of homogeneous inequalities `a ⬝ᵥ ξ ≥ 0` (`a ∈ A`). For a finite `S`
it is the base `solutionRegion S`; it is needed for the systems `Σ` and `S′`, whose
inequalities are all (infinitely many, positively proportional) extreme solutions. -/
def regionOf {n : ℕ} (A : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {ξ | ∀ a ∈ A, 0 ≤ a ⬝ᵥ ξ}

/-- Weyl (1935), §3, Satz 4 (p. 296), applied to an arbitrary inequality set `A`: `ξ` is an
*extreme Lösung* of `A` when `ξ` solves every inequality of `A`, `ξ ≠ 0`, and equality
`a ⬝ᵥ ξ = 0` holds in `n - 1` linearly independent inequalities `a` of `A`. This is the base
`IsExtremeSolution` with a `Set` in place of a `Finset`. -/
def IsExtremeSolutionOf {n : ℕ} (A : Set (Fin n → ℝ)) (ξ : Fin n → ℝ) : Prop :=
  ξ ∈ regionOf A ∧ ξ ≠ 0 ∧
    ∃ T : Finset (Fin n → ℝ), (↑T : Set (Fin n → ℝ)) ⊆ A ∧ T.card = n - 1 ∧
      LinearIndependent ℝ (fun t : T => (t : Fin n → ℝ)) ∧ ∀ a ∈ T, a ⬝ᵥ ξ = 0

/-- Weyl (1935), §3 I, p. 297, (10): the inequalities of the dual system `Σ` of the finite
system `S` are `α ⬝ᵥ x ≥ 0` for **all** extreme solutions `α` of `S` (no representatives are
chosen). Its region `regionOf (sigmaSet S)` is the base `dualRegion S`. -/
def sigmaSet {n : ℕ} (S : Finset (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {α | IsExtremeSolution S α}

/-- Weyl (1935), §3 IV, p. 300: `S′` is the system of the inequalities `a′ ⬝ᵥ ξ ≥ 0` for all
extreme solutions `a′` of the dual system `Σ`; its region is `(S′) = regionOf (sPrimeSet S)`. -/
def sPrimeSet {n : ℕ} (S : Finset (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {a' | IsExtremeSolutionOf (sigmaSet S) a'}

end WeylPolyhedra.Polyhedron.Supplement


