-- Prove2me | Definitions.Def_EnvelopeMSLP_StdOptimal
-- name    : EnvelopeMSLP_StdOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:25:38.553527+00:00
-- url     : https://prove2.me/theorems/f8729293-743f-4649-87ca-fc347d730dae
-- title:
--   Optimal point of the standard-form LP (4)
-- statement:
--   A vector $y$ is optimal for (4) when it is feasible and $\langle d,y'\rangle\le\langle d,y\rangle$ for every feasible $y'$.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), display (4), p.8

import Mathlib
import Definitions.Def_EnvelopeMSLP_StdFeasible
open Matrix

namespace EnvelopeMSLP

/-- **Optimal point of form (4).** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), display (4), p.8: `y` is feasible and maximizes
`⟨d, y⟩` over the feasible points. -/
def StdOptimal {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (d : Fin n → ℝ)
    (y : Fin n → ℝ) : Prop :=
  StdFeasible D b y ∧ ∀ y', StdFeasible D b y' → d ⬝ᵥ y' ≤ d ⬝ᵥ y

end EnvelopeMSLP


