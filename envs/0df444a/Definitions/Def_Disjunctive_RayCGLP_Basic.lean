-- Prove2me | Definitions.Def_Disjunctive_RayCGLP_Basic
-- name    : Disjunctive_RayCGLP_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T16:54:06.369336+00:00
-- url     : https://prove2.me/theorems/32c85386-7575-4efd-9d93-d86dc3c670c7
-- title:
--   (CGLP)_y under the ray normalization, and its optimality
-- statement:
--   This definition fixes `(CGLP)_y` (eq. (10.9), p. 138): the cut-generating LP
--   under the ray normalization `αy=1`, for a fixed disjunctive hull `P_D`.
--
--   `IsCGLPYFeasible PD y α β` says `αx≥β` is valid for `P_D` and `αy=1`. `CGLPYHasFiniteMin` says the
--   objective `αx̄-β` is bounded below over the feasible region. `IsCGLPYOptimal` additionally
--   requires `(α,β)` to minimize that objective.
--
--   **Formalization Note.** Feasibility is stated directly as `P_D`-validity under the normalization,
--   rather than through an explicit extreme-ray/multiplier representation of the projection cone `W`
--   — matching how Theorems 10.2/10.3 and Corollary 10.4 are themselves phrased purely in terms of
--   `(α,β)`-validity for `P_D`, never in terms of a specific multiplier vector.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 138, Section 10.6

import Mathlib

namespace Disjunctive.RayCGLP

/-- `(CGLP)_y`, eq. (10.9) (Balas §10.6, p. 138): the cut-generating LP under the ray
normalization `αy=1`, for the fixed disjunctive hull `P_D`. Feasibility of `(α,β)` is stated
directly as validity for `P_D` (rather than through an explicit multiplier representation), since
Theorem 10.2/10.3/Corollary 10.4 are stated purely in terms of `(α,β)`-validity for `P_D`, matching
the book's own framing of `(CGLP)_y`'s feasible region as (a normalization slice of) the reverse
polar of `P_D`. -/
def IsCGLPYFeasible {n : ℕ} (PD : Set (Fin n → ℝ)) (y : Fin n → ℝ) (α : Fin n → ℝ) (β : ℝ) :
    Prop :=
  (∀ x ∈ PD, β ≤ dotProduct α x) ∧ dotProduct α y = 1

/-- `(CGLP)_y` has a finite minimum of its objective `αx̄-β`: the objective is bounded below over
the feasible region (Balas §10.6, p. 138, discussed just before Theorem 10.2). -/
def CGLPYHasFiniteMin {n : ℕ} (PD : Set (Fin n → ℝ)) (y : Fin n → ℝ) (xbar : Fin n → ℝ) : Prop :=
  BddBelow ((fun p : (Fin n → ℝ) × ℝ => dotProduct p.1 xbar - p.2) ''
    {p : (Fin n → ℝ) × ℝ | IsCGLPYFeasible PD y p.1 p.2})

/-- `(α,β)` is an optimal solution to `(CGLP)_y` (Balas §10.6, p. 138, Theorem 10.3): feasible,
and minimizing the objective `αx̄-β` over the feasible region. -/
def IsCGLPYOptimal {n : ℕ} (PD : Set (Fin n → ℝ)) (y : Fin n → ℝ) (xbar : Fin n → ℝ)
    (α : Fin n → ℝ) (β : ℝ) : Prop :=
  IsCGLPYFeasible PD y α β ∧
    ∀ α' β', IsCGLPYFeasible PD y α' β' → dotProduct α xbar - β ≤ dotProduct α' xbar - β'

end Disjunctive.RayCGLP


