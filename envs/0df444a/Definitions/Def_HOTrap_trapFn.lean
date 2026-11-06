-- Prove2me | Definitions.Def_HOTrap_trapFn
-- name    : HOTrap_trapFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:46:01.015507+00:00
-- url     : https://prove2.me/theorems/e1cb443a-6465-4cfd-ae0d-bba3449b728d
-- title:
--   Trapping function $\phi_{x,\eta}$
-- statement:
--   For $x,y\in\mathbb R^d$ and $\eta>0$,
--   $$
--   \phi_{x,\eta}(y):=f(y)-f(x)+\eta\|y-x\|_2.
--   $$
--
--   This function drives gradient-flow trapping.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Definition 3.4, Eq. (1), p.15

import Mathlib

namespace HOTrap

/-- **The trapping function** `ϕ_{x,η}(y) := f(y) − f(x) + η∥y − x∥₂`. Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Definition 3.4, Eq. (1),
p.15. -/
noncomputable def trapFn {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) (η : ℝ) (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  f y - f x + η * ‖y - x‖

end HOTrap


