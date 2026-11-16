-- Prove2me | Definitions.Def_QuantumLTF_Membership_affineBoundaryBisect
-- name    : QuantumLTF_Membership_affineBoundaryBisect
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-15T11:32:28.446183+00:00
-- url     : https://prove2.me/theorems/69300c37-a463-439b-85a6-81fc92a3cabc
-- title:
--   Affine-line boundary bisection query tree
-- statement:
--   An orientation-aware binary-search query tree whose midpoint queries lie on the affine line x + t p, designed to estimate the boundary height at x coherently.
-- source:
--   Coherent height-oracle construction in Theorem 3.2 of Fast Quantum Algorithms for Learning Linear Threshold Functions

import Mathlib
import Definitions.Def_QuantumLTF_Membership_QueryTree

namespace QuantumLTF.Membership

/-- Orientation-aware bisection for the boundary height along the affine line `x + t • p`. -/
noncomputable def affineBoundaryBisect {n : ℕ}
    (p x : EuclideanSpace ℝ (Fin n)) (s : ℤ) :
    ℕ → ℝ → ℝ → QueryTree n ℝ
  | 0, lo, hi => .leaf ((lo + hi) / 2)
  | k + 1, lo, hi =>
      let mid := (lo + hi) / 2
      .query (x + mid • p) fun ans =>
        if s = 1 then
          if ans = 1 then affineBoundaryBisect p x s k lo mid
          else affineBoundaryBisect p x s k mid hi
        else
          if ans = 1 then affineBoundaryBisect p x s k mid hi
          else affineBoundaryBisect p x s k lo mid

end QuantumLTF.Membership


