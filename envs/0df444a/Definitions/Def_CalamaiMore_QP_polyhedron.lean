-- Prove2me | Definitions.Def_CalamaiMore_QP_polyhedron
-- name    : CalamaiMore_QP_polyhedron
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:57:48.998288+00:00
-- url     : https://prove2.me/theorems/74142c48-a927-4c5e-a42e-7435ffc49b02
-- title:
--   Polyhedral set (4.1), active set (4.2), and the equality-constrained problem (6.2)
-- statement:
--   Let $E$ be a real inner product space, $c_1, \dots, c_m \in E$ and $\delta_1, \dots, \delta_m \in \mathbb{R}$. The **polyhedral set** is
--
--   $$
--   \Omega = \{x \in E : \langle c_j, x \rangle \ge \delta_j,\ j = 1, \dots, m\},
--   $$
--
--   and the set of **active constraints** at $x$ is $A(x) = \{j : \langle c_j, x \rangle = \delta_j\}$.
--
--   For a **working set** $W \subseteq \{1, \dots, m\}$, problem (6.2) is the equality-constrained problem
--
--   $$
--   \min\{f(y) : \langle c_j, y \rangle = \delta_j,\ j \in W\}.
--   $$
--
--   Its feasible set is the affine set $\{y : \langle c_j, y\rangle = \delta_j,\ j \in W\}$ (all of $E$ when $W = \emptyset$); it is **not** intersected with $\Omega$, so the inequality constraints outside $W$ are ignored. A point $x$ is a **global minimizer of (6.2)** if it lies in this affine set and $f(x) \le f(y)$ for every $y$ in it.
--
--   Active-set methods for quadratic programming keep a working set $W_k \subseteq A(x_k)$ and alternate between minimising over the affine set of $W_k$ and changing $W_k$.
--
--   **Formalization Note** Constraints are indexed by `Fin m`; $A(x)$ and working sets are `Finset (Fin m)`. `workingFace c δ W` is the affine set of (6.2) and `IsWorkingSetMinimizer f c δ W x` is "x is a global minimizer of (6.2)". $m = 0$ is allowed (then $\Omega = E$).
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 105, Eqs. (4.1)–(4.2); p. 110, Eq. (6.2)

import Mathlib

namespace CalamaiMore.QP

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

/-- The feasible set of the equality-constrained problem (6.2) of Calamai–Moré, p. 110, for a
working set `W`: the affine set `{y : ⟨c_j, y⟩ = δ_j, j ∈ W}`. Only equality constraints; it is
not intersected with `Ω`. -/
def workingFace {m : ℕ} (c : Fin m → E) (δ : Fin m → ℝ) (W : Finset (Fin m)) : Set E :=
  {y | ∀ j ∈ W, inner ℝ (c j) y = δ j}

/-- `x` is a global minimizer of problem (6.2), `min {f(y) : ⟨c_j, y⟩ = δ_j, j ∈ W}`
(Calamai–Moré, p. 110): `x` lies in the affine set of `W` and `f(x) ≤ f(y)` for every `y` in it. -/
def IsWorkingSetMinimizer {m : ℕ} (f : E → ℝ) (c : Fin m → E) (δ : Fin m → ℝ)
    (W : Finset (Fin m)) (x : E) : Prop :=
  x ∈ workingFace c δ W ∧ ∀ y ∈ workingFace c δ W, f x ≤ f y

end CalamaiMore.QP


