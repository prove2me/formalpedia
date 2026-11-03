-- Prove2me | Definitions.Def_EnvelopeMSLP_FreeOptimal
-- name    : EnvelopeMSLP_FreeOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:25:39.902692+00:00
-- url     : https://prove2.me/theorems/2bcda49c-a60a-4138-8098-a9426f8dca0d
-- title:
--   Optimal point of the LP (6)
-- statement:
--   A vector $x$ is optimal for (6) when it is feasible and $\langle c,x'\rangle\le\langle c,x\rangle$ for every feasible $x'$.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), display (6), p.10

import Mathlib
import Definitions.Def_EnvelopeMSLP_FreeFeasible
open Matrix

namespace EnvelopeMSLP

/-- **Optimal point of form (6).** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), display (6), p.10: `x` is feasible and maximizes
`⟨c, x⟩` over the feasible points. -/
def FreeOptimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) : Prop :=
  FreeFeasible A b x ∧ ∀ x', FreeFeasible A b x' → c ⬝ᵥ x' ≤ c ⬝ᵥ x

end EnvelopeMSLP


