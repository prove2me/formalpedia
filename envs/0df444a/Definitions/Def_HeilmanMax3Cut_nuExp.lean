-- Prove2me | Definitions.Def_HeilmanMax3Cut_nuExp
-- name    : HeilmanMax3Cut_nuExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:27:14.95859+00:00
-- url     : https://prove2.me/theorems/20cd7a2f-718e-49f6-a7b7-18f22cf4260c
-- title:
--   The exponential law $\nu$
-- statement:
--   $\nu$ is the probability measure on $(0,\infty)$ with $d\nu(r)=e^{-r}\,dr$: the law of $|\xi|^2/2$ for a standard Gaussian vector $\xi$ in $\mathbb R^2$.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), p.21 and p.29

import Mathlib
open MeasureTheory

namespace HeilmanMax3Cut

/-- **The exponential law `ν`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), p.21 and p.29: `dν(r) = e^{−r} dr`, `r ≥ 0`, the law of
`t = |ξ|²/2` for a standard Gaussian `ξ` in `ℝ²`.

**Formalization Note.** Lebesgue measure on `(0, ∞)` with density `e^{−r}` (the endpoint `0` is
null). It is a probability measure. -/
noncomputable def nuExp : Measure ℝ :=
  (volume.restrict (Set.Ioi (0 : ℝ))).withDensity (fun r => ENNReal.ofReal (Real.exp (-r)))

end HeilmanMax3Cut


