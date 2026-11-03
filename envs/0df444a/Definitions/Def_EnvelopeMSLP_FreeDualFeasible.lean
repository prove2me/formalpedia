-- Prove2me | Definitions.Def_EnvelopeMSLP_FreeDualFeasible
-- name    : EnvelopeMSLP_FreeDualFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:48.699538+00:00
-- url     : https://prove2.me/theorems/24a7efff-6df5-414b-b66f-bae12603470a
-- title:
--   Feasible point of the dual of (6)
-- statement:
--   The LP dual of $\max\{\langle c,x\rangle: Ax\le b\}$ with $x$ free is $\min\langle b,y\rangle$ subject to
--   $$A^{\mathsf T}y=c,\qquad y\ge 0.$$
--   A vector $y\in\mathbb R^m$ is dual feasible when it satisfies these two conditions.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), display (6), p.10 (dual written by the formalization; the paper uses it through Theorem 1)

import Mathlib
open Matrix

namespace EnvelopeMSLP

/-- **Feasible point of the dual of form (6).** The LP dual of
`max ⟨c, x⟩ s.t. A x ≤ b`, `x` free, of Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), display (6), p.10, is
`min ⟨b, y⟩ s.t. Aᵀ y = c`, `y ≥ 0`. -/
def FreeDualFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (y : Fin m → ℝ) :
    Prop :=
  0 ≤ y ∧ Aᵀ *ᵥ y = c

end EnvelopeMSLP


