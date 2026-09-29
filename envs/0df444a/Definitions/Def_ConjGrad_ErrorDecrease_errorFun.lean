-- Prove2me | Definitions.Def_ConjGrad_ErrorDecrease_errorFun
-- name    : ConjGrad_ErrorDecrease_errorFun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T21:53:51.153476+00:00
-- url     : https://prove2.me/theorems/d972623f-463e-4eb2-accc-99b34658f12a
-- title:
--   The error function $f(x)=(h-x,A(h-x))$, eq. (4:5)
-- statement:
--   Let $A$ be a real $n\times n$ matrix, and let $h\in\mathbb{R}^n$ be the solution of the system $Ax=k$. For an estimate $x$ of $h$, the **error function** of Hestenes and Stiefel is
--
--   $$
--   f(x) = (h-x,\,A(h-x)).
--   $$
--
--   For a symmetric positive definite $A$ it satisfies $f(x)\ge 0$, with $f(x)=0$ if and only if $x=h$, so it measures the "goodness" of $x$ as an estimate of $h$. It is the quantity that the cg-method diminishes at every step.
--
--   **Formalization Note** The definition uses the first form of (4:5), in terms of $h$; the paper's second form $(x,Ax)-2(x,k)+(h,k)$ agrees with it when $A$ is symmetric and $Ah=k$. No hypothesis on $A$ or $h$ is built into the definition; the theorems carry them.
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), p. 413, eq. (4:5)

import Mathlib

open Matrix

namespace ConjGrad.ErrorDecrease

/-- The error function (4:5) of an estimate `x` of the solution `h` of `Ax = k`:
`f(x) = (h − x, A(h − x))`. -/
def errorFun {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (h x : Fin n → ℝ) : ℝ :=
  (h - x) ⬝ᵥ (A *ᵥ (h - x))

end ConjGrad.ErrorDecrease


