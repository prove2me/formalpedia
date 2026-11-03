-- Prove2me | Definitions.Def_EnvelopeMSLP_freeValue
-- name    : EnvelopeMSLP_freeValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:25:46.714358+00:00
-- url     : https://prove2.me/theorems/41ad8866-a2a1-47ed-9664-8fffeaefe14a
-- title:
--   Extended optimal value of the LP (6)
-- statement:
--   The value of (6) is
--   $$V=\sup\{\langle c,x\rangle: Ax\le b\}$$
--   in the extended reals: $-\infty$ when (6) is infeasible and $+\infty$ when it is unbounded.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), display (6), p.10

import Mathlib
import Definitions.Def_EnvelopeMSLP_lpValue
import Definitions.Def_EnvelopeMSLP_FreeFeasible
open Matrix

namespace EnvelopeMSLP

/-- **Extended optimal value of form (6).** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), display (6), p.10: `V = sup {⟨c, x⟩ : A x ≤ b}`
in `EReal`, so `⊥` when infeasible and `⊤` when unbounded. -/
noncomputable def freeValue {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) : EReal :=
  lpValue {x | FreeFeasible A b x} c

end EnvelopeMSLP


