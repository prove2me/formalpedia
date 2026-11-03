-- Prove2me | Definitions.Def_EnvelopeMSLP_MSLP_Solvable
-- name    : EnvelopeMSLP_MSLP_Solvable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:30:43.850279+00:00
-- url     : https://prove2.me/theorems/56379e81-5a57-449c-b790-a1be39342fc5
-- title:
--   The program (7) has a solution
-- statement:
--   The program (7) is solvable at $\theta$ when an optimal policy exists. This is the paper's phrase "the problem has a solution".
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), Theorem 3, p.13

import Mathlib
import Definitions.Def_EnvelopeMSLP_MSLP_IsOptimalPolicy

namespace EnvelopeMSLP

/-- **"The problem has a solution" at `θ`.** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), Theorem 3, p.13: an optimal policy exists. -/
def MSLP.Solvable {T : ℕ} {Ω : Type*} [Fintype Ω] (P : MSLP T Ω) (θ : ℝ) : Prop :=
  ∃ x, P.IsOptimalPolicy θ x

end EnvelopeMSLP


