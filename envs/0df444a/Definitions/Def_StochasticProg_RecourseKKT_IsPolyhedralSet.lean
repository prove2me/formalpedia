-- Prove2me | Definitions.Def_StochasticProg_RecourseKKT_IsPolyhedralSet
-- name    : StochasticProg_RecourseKKT_IsPolyhedralSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:48:27.190383+00:00
-- url     : https://prove2.me/theorems/e418ce5a-d94a-417e-8d76-88ea5f4e24df
-- title:
--   Convex polyhedron
-- statement:
--   A subset $S$ of a real vector space $E$ is a **convex polyhedron** when it is the solution set of finitely many linear inequalities: there are linear functionals $\varphi_1, \dots, \varphi_k$ on $E$ and reals $u_1, \dots, u_k$ with
--
--   $$
--   S = \{\, x \in E \mid \varphi_i(x) \le u_i,\ i = 1, \dots, k \,\}.
--   $$
--
--   With $k = 0$ this is the whole space, and the empty set is a polyhedron ($0 \le -1$). It is the notion of Theorem 1 and of the regularity condition of the corrected Theorem 9.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, doi:10.1007/978-1-4614-0237-4, Chapter 3, Theorem 1 and its proof, printed p. 106 (PDF p. 131)

import Mathlib

namespace StochasticProg.RecourseKKT

/-- **Convex polyhedron.**
Birge & Louveaux, *Introduction to Stochastic Programming*, 2nd ed., Springer 2011,
doi:10.1007/978-1-4614-0237-4, Chapter 3, Theorem 1 and its proof, printed p. 106 (PDF p. 131): "the elementary feasibility
set K₂(ξ) is a convex polyhedron"; "The intersection of finitely many convex polyhedra is a convex
polyhedron."

A subset of a real vector space `E` is a convex polyhedron when it is the solution set of finitely
many linear inequalities `φᵢ(x) ≤ uᵢ`, `i = 1, …, k`.

**Formalization Note.** `k = 0` gives the whole space, and the empty set is `{x | 0 ≤ −1}`; both
are polyhedra, as in the book's proof of Theorem 5(b) ("the problem is infeasible and the result in
(b) is trivially satisfied"). Equalities are pairs of inequalities. `E` is generic so the same
notion applies to sets of first-stage decisions and to sets of right-hand sides `(h, T)`. -/
def IsPolyhedralSet {E : Type*} [AddCommGroup E] [Module ℝ E] (S : Set E) : Prop :=
  ∃ (k : ℕ) (φ : Fin k → E →ₗ[ℝ] ℝ) (u : Fin k → ℝ), S = {x | ∀ i, φ i x ≤ u i}

end StochasticProg.RecourseKKT


