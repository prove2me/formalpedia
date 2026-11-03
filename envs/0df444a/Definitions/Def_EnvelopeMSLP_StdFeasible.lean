-- Prove2me | Definitions.Def_EnvelopeMSLP_StdFeasible
-- name    : EnvelopeMSLP_StdFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:48.097208+00:00
-- url     : https://prove2.me/theorems/1b6773a1-9858-40b6-999a-eb3c90d7b153
-- title:
--   Feasible point of the standard-form LP (4)
-- statement:
--   The standard form (4) is $\max\langle d,y\rangle$ subject to $Dy=b$, $y\ge0$. A vector $y$ is feasible when
--   $$Dy=b,\qquad y\ge0.$$
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), display (4), p.8

import Mathlib
open Matrix

namespace EnvelopeMSLP

/-- **Feasible point of form (4).** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), display (4), p.8: `D y = b`, `y ≥ 0`. -/
def StdFeasible {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) : Prop :=
  D *ᵥ y = b ∧ 0 ≤ y

end EnvelopeMSLP


