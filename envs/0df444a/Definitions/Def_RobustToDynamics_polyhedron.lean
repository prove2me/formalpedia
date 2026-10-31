-- Prove2me | Definitions.Def_RobustToDynamics_polyhedron
-- name    : RobustToDynamics_polyhedron
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:15.069932+00:00
-- url     : https://prove2.me/theorems/973cf0cf-15d3-4d8b-84de-df9e2ba31e2d
-- title:
--   The polyhedron $P=\{x\in\mathbb R^n : Ax\le b\}$
-- statement:
--   For $A\in\mathbb R^{m\times n}$ and $b\in\mathbb R^m$,
--   $$
--   P=\{x\in\mathbb R^n : Ax\le b\},
--   $$
--   the inequality being componentwise. This is the polyhedron in which the trajectories of an R-LD-LP must remain.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ`. The data are real; rational instances are cast from $\mathbb Q$.
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, §2, (2.1), p.5

import Mathlib

open Matrix

namespace RobustToDynamics

/-- **The polyhedron `P = {x ∈ ℝⁿ | Ax ≤ b}`.**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, §2, (2.1), p.5:
"P := {x ∈ Rn| Ax ≤ b} is a polyhedron".

**Formalization Note.** `ℝⁿ` is `Fin n → ℝ`; `Ax ≤ b` is the componentwise order on `Fin m → ℝ`.
The data `A ∈ ℝ^{m×n}`, `b ∈ ℝ^m` are real here; rational instances are cast with `Rat.cast`. -/
def polyhedron {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | A *ᵥ x ≤ b}

end RobustToDynamics


