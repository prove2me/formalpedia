-- Prove2me | Definitions.Def_PiIrrationality_UpperBound
-- name    : PiIrrationality_UpperBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-01T05:22:24.314989+00:00
-- url     : https://prove2.me/theorems/47a8e938-d9f9-4663-8a39-bfe20bb0c189
-- title:
--   Upper bounds for the irrationality measure of π
-- statement:
--   For a real number $B$, PiIrrationality.UpperBound $B$ expresses $\mu(\pi)\le B$: for every real $\varepsilon>0$ there is a natural number $Q$ such that every integer $p$ and positive natural denominator $q\ge Q$ satisfy $1/q^{B+\varepsilon}<|\pi-p/q|$. The threshold is uniform over $p$ and $q$.
-- source:
--   The epsilon characterization of C_7a in https://teorth.github.io/optimizationproblems/constants/7a.html . Related fixed-exponent Lean predicate: https://github.com/AxiomMath/gdm-formal-conjectures/blob/main/BorweinSineSeries/problem.lean . This definition uses the epsilon characterization, which gives the standard upper-bound meaning at the endpoint.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace PiIrrationality

/-- The epsilon formulation of an upper bound on the irrationality measure of pi.
The threshold may depend on the positive epsilon, but is uniform in p and q. -/
def UpperBound (B : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ Q : ℕ,
      ∀ (p : ℤ) (q : ℕ), 0 < q → Q ≤ q →
        1 / (q : ℝ) ^ (B + ε) <
          |Real.pi - (p : ℝ) / (q : ℝ)|

end PiIrrationality


