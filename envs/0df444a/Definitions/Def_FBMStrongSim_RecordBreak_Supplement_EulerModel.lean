-- Prove2me | Definitions.Def_FBMStrongSim_RecordBreak_Supplement_EulerModel
-- name    : FBMStrongSim_RecordBreak_Supplement_EulerModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:28:09.920801+00:00
-- url     : https://prove2.me/theorems/d04edd0f-7ac6-47c0-8741-2122d9e2b5a0
-- title:
--   Dyadic Euler recursion and its piecewise constant extension
-- statement:
--   For the driver $x$, matrix field $f$, and initial value $y_0$, define $y_n$ on $t_k^n=k/2^n$ by
--   $$y_n(0)=y_0,\qquad y_n(t_{k+1}^n)=y_n(t_k^n)+f(y_n(t_k^n))(x(t_{k+1}^n)-x(t_k^n)).$$
--   Between grid points use the left endpoint value, and at $1$ use the final grid value. This is the piecewise constant extension (5.5); it need not be continuous despite the sentence preceding (5.5). Only grid indices $0\le k\le2^n$ enter the theorems.
--
--   Differences from the source:
--   - encoding: the recursion (5.4) and half-open-cell extension (5.5) → the actual Euler recursion and a floor/min left-value extension with the final grid value at t=1; reason: the source formula specifies the half-open cells; the endpoint convention completes the path without removing a time or a level
--   - reading: the word continuous before the piecewise constant formula (5.5) → the generally discontinuous piecewise constant path given by that formula; reason: the displayed formula determines the extension
-- source:
--   Chen, Dong & Ni, ε-Strong simulation of fractional Brownian motion and related stochastic differential equations, arXiv:1902.07824v1, pp. 30–31, (5.4)–(5.5)

import Mathlib
import Definitions.Def_FBMStrongSim_RecordBreak_Model
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_CoefficientModel

namespace FBMStrongSim.RecordBreak.Supplement

/-- (5.4), including the initial condition. Values beyond the grid are never queried. -/
noncomputable def eulerValue {d h : ℕ} (f : Field d h) (x : ℝ → Vec h) (y0 : Vec d)
    (n : ℕ) : ℕ → Vec d
  | 0 => y0
  | k + 1 => eulerValue f x y0 n k +
      f (eulerValue f x y0 n k) (x (dyadic n (k + 1)) - x (dyadic n k))

/-- The piecewise constant extension (5.5), with the final grid value at t=1. -/
noncomputable def euler {d h : ℕ} (f : Field d h) (x : ℝ → Vec h) (y0 : Vec d)
    (n : ℕ) (t : ℝ) : Vec d :=
  eulerValue f x y0 n (min ⌊(2 : ℝ) ^ n * t⌋₊ (2 ^ n))


end FBMStrongSim.RecordBreak.Supplement


