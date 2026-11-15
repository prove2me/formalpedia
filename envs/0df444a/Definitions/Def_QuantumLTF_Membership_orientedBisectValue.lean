-- Prove2me | Definitions.Def_QuantumLTF_Membership_orientedBisectValue
-- name    : QuantumLTF_Membership_orientedBisectValue
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-15T03:03:06.904202+00:00
-- url     : https://prove2.me/theorems/c39f7c31-cd3a-43d2-a634-d8c41b6664b2
-- title:
--   Scalar semantics of oriented boundary bisection
-- statement:
--   The scalar recursion corresponding to the orientation-aware query tree. At each step it queries the midpoint relative to the true boundary, retains the half-interval containing the boundary, and returns the final midpoint after a prescribed number of updates.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 3.1, pp. 21–22 (PDF pp. 22–23).

import Mathlib
import Definitions.Def_QuantumLTF_Membership_sgn

namespace QuantumLTF.Membership

/-- Scalar semantics of orientation-aware bisection for a boundary at `h`.
Positive orientation queries `sgn (mid-h)`; negative orientation queries `sgn (h-mid)`.
The returned value is the midpoint after `q` interval updates. -/
noncomputable def orientedBisectValue (s : ℤ) : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0, lo, hi, _ => (lo + hi) / 2
  | q + 1, lo, hi, h =>
      let mid := (lo + hi) / 2
      if s = 1 then
        if sgn (mid - h) = 1 then orientedBisectValue s q lo mid h
        else orientedBisectValue s q mid hi h
      else
        if sgn (h - mid) = 1 then orientedBisectValue s q mid hi h
        else orientedBisectValue s q lo mid h

end QuantumLTF.Membership


