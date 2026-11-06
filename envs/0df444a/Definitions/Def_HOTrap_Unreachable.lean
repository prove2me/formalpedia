-- Prove2me | Definitions.Def_HOTrap_Unreachable
-- name    : HOTrap_Unreachable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:46:55.7642+00:00
-- url     : https://prove2.me/theorems/eeda1244-6624-4842-acef-7c8fa0ff52ba
-- title:
--   $\eta$-unreachable point
-- statement:
--   A point $y$ is $\eta$-unreachable from $x$ if $\phi_{x,\eta}(y)>0$, and $\eta$-reachable otherwise.
--
--   A boundary of unreachable points certifies that a region contains an approximate stationary point.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Definition 3.4, p.15

import Mathlib
import Definitions.Def_HOTrap_trapFn

namespace HOTrap

/-- **`y` is `η`-unreachable from `x`**: `ϕ_{x,η}(y) > 0`. Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Definition 3.4, p.15. -/
def Unreachable {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) (η : ℝ) (y : EuclideanSpace ℝ (Fin d)) : Prop :=
  0 < trapFn f x η y

end HOTrap


