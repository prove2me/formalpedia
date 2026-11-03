-- Prove2me | Definitions.Def_EnvelopeMSLP_basicSolution
-- name    : EnvelopeMSLP_basicSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:25:52.232082+00:00
-- url     : https://prove2.me/theorems/fe3e8b13-cd66-4b01-88ec-77bbf343382c
-- title:
--   Basic solution of a basis
-- statement:
--   The basic solution of $\beta$ is the vector $x\in\mathbb R^n$ with
--   $$x_\beta=D_\beta^{-1}b,\qquad x_{[n]\setminus\beta}=0.$$
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), proof of Lemma 1, p.9

import Mathlib
import Definitions.Def_EnvelopeMSLP_basisMatrix
open Matrix

namespace EnvelopeMSLP

/-- **Basic solution of a basis.** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), proof of Lemma 1, p.9: `x` with `x_β = D_β⁻¹ b` and
`x_[n]∖β = 0`. -/
noncomputable def basicSolution {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (β : Fin m ↪ Fin n) : Fin n → ℝ :=
  Function.extend β ((basisMatrix D β)⁻¹ *ᵥ b) 0

end EnvelopeMSLP


