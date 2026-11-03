-- Prove2me | Definitions.Def_EnvelopeMSLP_matDeriv
-- name    : EnvelopeMSLP_matDeriv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:49.438318+00:00
-- url     : https://prove2.me/theorems/dbf4f011-b571-4217-8ac3-1afe15111b6b
-- title:
--   Componentwise derivative of a matrix function
-- statement:
--   The matrix $\frac{d}{d\theta}A(\theta)$ of the entrywise derivatives of $A$; the paper uses this notation as short-hand for the component-wise derivative with respect to $\theta$.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), p.6

import Mathlib

namespace EnvelopeMSLP

/-- **Componentwise derivative of a matrix function.** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), p.6: "we use `d/dθ A(θ)` as short-hand for
the component-wise derivative with respect to `θ`". -/
noncomputable def matDeriv {r s : ℕ} (A : ℝ → Matrix (Fin r) (Fin s) ℝ) (θ : ℝ) :
    Matrix (Fin r) (Fin s) ℝ :=
  Matrix.of fun i j => deriv (fun θ' => A θ' i j) θ

end EnvelopeMSLP


