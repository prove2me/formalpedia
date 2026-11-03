-- Prove2me | Definitions.Def_EnvelopeMSLP_FreeSolvable
-- name    : EnvelopeMSLP_FreeSolvable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:27.675444+00:00
-- url     : https://prove2.me/theorems/ca8b15d4-f333-4924-9199-af14b6c6037a
-- title:
--   The LP (6) has a solution
-- statement:
--   The linear program (6) with data $(A,b,c)$ is solvable when an optimal point exists. By LP duality this holds exactly when the primal and the dual are both feasible.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), display (6), p.10

import Mathlib
import Definitions.Def_EnvelopeMSLP_FreeOptimal
open Matrix

namespace EnvelopeMSLP

/-- **Form (6) has a solution.** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), display (6), p.10: an optimal point exists. -/
def FreeSolvable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) : Prop :=
  ∃ x, FreeOptimal A b c x

end EnvelopeMSLP


