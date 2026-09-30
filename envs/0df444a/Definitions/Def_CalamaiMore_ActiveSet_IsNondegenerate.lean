-- Prove2me | Definitions.Def_CalamaiMore_ActiveSet_IsNondegenerate
-- name    : CalamaiMore_ActiveSet_IsNondegenerate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:52:13.491969+00:00
-- url     : https://prove2.me/theorems/f59edf21-0c56-4bc0-b273-b1b7ac3b5e90
-- title:
--   Kuhn–Tucker point (4.3) and nondegenerate stationary point
-- statement:
--   Let $\Omega = \{x : \langle c_j, x \rangle \ge \delta_j,\ j = 1, \dots, m\}$ be a polyhedral set in a finite-dimensional real inner product space $E$ with active sets $A(x)$, and let $f : E \to \mathbb{R}$.
--
--   1. A point $x^* \in \Omega$ is a **Kuhn–Tucker point** of $\min\{f(x) : x \in \Omega\}$ if there are multipliers $\lambda^*_j$, $j \in A(x^*)$, with
--   $$
--   \nabla f(x^*) = \sum_{j \in A(x^*)} \lambda^*_j c_j, \qquad \lambda^*_j \ge 0 .
--   $$
--   2. A point $x^* \in \Omega$ is **nondegenerate** if the active constraint normals $\{c_j : j \in A(x^*)\}$ are linearly independent and $\nabla f(x^*) = \sum_{j \in A(x^*)} \lambda^*_j c_j$ with $\lambda^*_j > 0$ for every $j \in A(x^*)$.
--
--   By linear independence the multipliers of a nondegenerate point are unique. Nondegeneracy (linear independence of the active normals together with strict complementarity) is the hypothesis under which an algorithm's active sets settle down to the active set of the limit point.
--
--   **Formalization Note** The multipliers are a function `lam : Fin m → ℝ` of which only the entries indexed by $A(x^*)$ matter. The source defines nondegeneracy for a stationary point; the Lean definition omits the separate word "stationary" because the strict Kuhn–Tucker representation already implies stationarity (Eq. (4.3)). Linear independence is `LinearIndependent ℝ (fun j : A(x*) => c j)`, i.e. of the family indexed by the active set, so two active constraints with equal normals are not linearly independent.
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 106, Eq. (4.3) and Definition (nondegenerate stationary point)

import Mathlib
import Definitions.Def_CalamaiMore_ActiveSet_polyhedron

namespace CalamaiMore.ActiveSet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A Kuhn–Tucker point of `min {f(x) : x ∈ Ω}` for the polyhedral `Ω` of (4.1),
Calamai–Moré Eq. (4.3): `x ∈ Ω` and `∇f(x) = ∑_{j ∈ A(x)} λ_j c_j` for some `λ_j ≥ 0`. -/
def IsKuhnTuckerPoint {m : ℕ} (c : Fin m → E) (δ : Fin m → ℝ) (f : E → ℝ) (x : E) : Prop :=
  x ∈ polyhedron c δ ∧
    ∃ lam : Fin m → ℝ, gradient f x = ∑ j ∈ activeSet c δ x, lam j • c j ∧
      ∀ j ∈ activeSet c δ x, 0 ≤ lam j

/-- A nondegenerate point (Calamai–Moré, Definition on p. 106): `x ∈ Ω`, the active constraint
normals `{c_j : j ∈ A(x)}` are linearly independent, and `∇f(x) = ∑_{j ∈ A(x)} λ_j c_j` with
`λ_j > 0` for every `j ∈ A(x)` (a Kuhn–Tucker point (4.3) with strictly positive multipliers). -/
def IsNondegenerate {m : ℕ} (c : Fin m → E) (δ : Fin m → ℝ) (f : E → ℝ) (x : E) : Prop :=
  x ∈ polyhedron c δ ∧
    LinearIndependent ℝ (fun j : activeSet c δ x => c j) ∧
    ∃ lam : Fin m → ℝ, gradient f x = ∑ j ∈ activeSet c δ x, lam j • c j ∧
      ∀ j ∈ activeSet c δ x, 0 < lam j

end CalamaiMore.ActiveSet


