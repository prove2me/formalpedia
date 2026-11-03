-- Prove2me | Definitions.Def_EnvelopeMSLP_FreeDualOptimal
-- name    : EnvelopeMSLP_FreeDualOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:25:36.730736+00:00
-- url     : https://prove2.me/theorems/ed5f047e-e5ba-4761-9cfb-d042a2dfe919
-- title:
--   Optimal point of the dual of (6)
-- statement:
--   A vector $y$ is dual optimal when it is dual feasible and $\langle b,y\rangle\le\langle b,y'\rangle$ for every dual feasible $y'$.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), display (6), p.10

import Mathlib
import Definitions.Def_EnvelopeMSLP_FreeDualFeasible
open Matrix

namespace EnvelopeMSLP

/-- **Optimal point of the dual of form (6).** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), display (6), p.10: `y` is dual feasible and
minimizes `⟨b, y⟩` over the dual feasible points. -/
def FreeDualOptimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (y : Fin m → ℝ) : Prop :=
  FreeDualFeasible A c y ∧ ∀ y', FreeDualFeasible A c y' → b ⬝ᵥ y ≤ b ⬝ᵥ y'

end EnvelopeMSLP


