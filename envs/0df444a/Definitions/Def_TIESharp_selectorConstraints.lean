-- Prove2me | Definitions.Def_TIESharp_selectorConstraints
-- name    : TIESharp_selectorConstraints
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:41:57.567023+00:00
-- url     : https://prove2.me/theorems/1186dcd6-e569-4e04-bbc5-3e828247bf3e
-- title:
--   Seven-machine endpoint selector constraints
-- statement:
--   For seven machines, the normalized endpoint parameters satisfy $d_i>0$, the selector probabilities satisfy $\theta_i\ge0$ and $\sum_i\theta_i=1$, and the two endpoint constraints are
--   $$\theta_0\le d_0-\tfrac13,\qquad \theta_6\le1-d_6.$$
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134, Proposition 5.5 proof, displayed assumptions near the top of p.27.

import Mathlib

set_option autoImplicit false

namespace TIESharp

/-- Normalized endpoint parameters and probability constraints used in the seven-machine
refinement (Li, *Sharp Bounds for Truthful-in-Expectation Scheduling*, arXiv:2611.05134,
Proposition 5.5, p.27). -/
def selectorConstraints (d theta : Fin 7 → ℝ) : Prop :=
  (∀ i, 0 < d i) ∧ (∀ i, 0 ≤ theta i) ∧ (∑ i, theta i) = 1 ∧
  theta 0 ≤ d 0 - 1 / 3 ∧ theta 6 ≤ 1 - d 6

end TIESharp


