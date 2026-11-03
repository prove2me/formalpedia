-- Prove2me | Definitions.Def_EnvelopeMSLP_FreeFeasible
-- name    : EnvelopeMSLP_FreeFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:47.8454+00:00
-- url     : https://prove2.me/theorems/587b96ee-5330-45c3-a170-406a5ff2666c
-- title:
--   Feasible point of the LP (6)
-- statement:
--   The linear program (6) with free variables is $\max\langle c,x\rangle$ subject to $Ax\le b$. A vector $x\in\mathbb R^n$ is feasible when
--   $$Ax\le b$$
--   coordinatewise. There is no sign constraint on $x$.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), display (6), p.10

import Mathlib
open Matrix

namespace EnvelopeMSLP

/-- **Feasible point of form (6).** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), display (6), p.10: `A x ≤ b`, with `x` free. -/
def FreeFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  A *ᵥ x ≤ b

end EnvelopeMSLP


