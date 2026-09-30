-- Prove2me | Definitions.Def_CalamaiMore_ActiveSet_polyhedron
-- name    : CalamaiMore_ActiveSet_polyhedron
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:51:37.276646+00:00
-- url     : https://prove2.me/theorems/db64f83e-af57-4cd4-9c1c-7357d5a7c825
-- title:
--   Polyhedral set (4.1) and active constraints $A(x)$ (4.2)
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, let $c_1, \dots, c_m \in E$ be **constraint normals** and $\delta_1, \dots, \delta_m \in \mathbb{R}$ scalars. The **polyhedral set** they define is
--
--   $$
--   \Omega = \{x \in E : \langle c_j, x \rangle \ge \delta_j,\ j = 1, \dots, m\},
--   $$
--
--   and the **set of active constraints** at a point $x$ is
--
--   $$
--   A(x) = \{j : \langle c_j, x \rangle = \delta_j\}.
--   $$
--
--   Every polyhedral set of $\mathbb{R}^n$, including bound constraints $l \le x \le u$ and linear equality constraints (written as two inequalities), has this form. The active set records which constraints hold with equality; identifying the active set of a solution reduces the constrained problem locally to a problem on an affine subspace.
--
--   **Formalization Note** The constraints are indexed by `Fin m` (so $j = 0, \dots, m-1$), `polyhedron c δ` is $\Omega$ and `activeSet c δ x : Finset (Fin m)` is $A(x)$; $A(x)$ is defined for every $x \in E$, and $m = 0$ gives $\Omega = E$ with $A(x) = \emptyset$.
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 105, Eqs. (4.1)–(4.2)

import Mathlib

namespace CalamaiMore.ActiveSet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The polyhedral set of Calamai–Moré Eq. (4.1):
`Ω = {x : ⟨c_j, x⟩ ≥ δ_j, j = 1, …, m}`, for constraint normals `c_j` and scalars `δ_j`. -/
def polyhedron {m : ℕ} (c : Fin m → E) (δ : Fin m → ℝ) : Set E :=
  {x | ∀ j, δ j ≤ inner ℝ (c j) x}

open Classical in
/-- The set of active constraints at `x`, Calamai–Moré Eq. (4.2):
`A(x) = {j : ⟨c_j, x⟩ = δ_j}`. -/
noncomputable def activeSet {m : ℕ} (c : Fin m → E) (δ : Fin m → ℝ) (x : E) : Finset (Fin m) :=
  Finset.univ.filter (fun j => inner ℝ (c j) x = δ j)

end CalamaiMore.ActiveSet


